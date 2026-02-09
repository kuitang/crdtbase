import { existsSync } from 'node:fs';
import { spawn } from 'node:child_process';
import { createInterface } from 'node:readline';

type Pending = {
  resolve: (line: string) => void;
  reject: (error: Error) => void;
};

export class LeanDrtClient {
  private pending: Pending[] = [];
  private proc: ReturnType<typeof spawn>;

  constructor(private readonly binPath: string) {
    this.proc = spawn(this.binPath, [], { stdio: ['pipe', 'pipe', 'inherit'] });
    const rl = createInterface({ input: this.proc.stdout });
    rl.on('line', (line) => {
      const next = this.pending.shift();
      if (next) {
        next.resolve(line);
      }
    });
    this.proc.on('error', (error) => {
      const err = error instanceof Error ? error : new Error(String(error));
      this.flushError(err);
    });
    this.proc.on('exit', (code) => {
      if (code !== 0) {
        this.flushError(new Error(`Lean DRT exited with code ${code}`));
      }
    });
  }

  static findBinary(): string | null {
    const explicit = process.env.LEAN_DRT_BIN;
    if (explicit && existsSync(explicit)) {
      return explicit;
    }
    const fallback = 'lean/.lake/build/bin/CrdtBaseDRT';
    return existsSync(fallback) ? fallback : null;
  }

  async send<T>(payload: unknown): Promise<T> {
    return new Promise((resolve, reject) => {
      this.pending.push({
        resolve: (line) => {
          try {
            const parsed = JSON.parse(line) as T & { error?: string };
            if (typeof parsed.error === 'string') {
              reject(new Error(parsed.error));
              return;
            }
            resolve(parsed);
          } catch (error) {
            reject(error instanceof Error ? error : new Error(String(error)));
          }
        },
        reject,
      });
      this.proc.stdin.write(`${JSON.stringify(payload)}\n`);
    });
  }

  async lwwMerge<T>(a: unknown, b: unknown): Promise<T> {
    return this.send<T>({
      type: 'lww_merge',
      a,
      b,
    });
  }

  async sqlGenerateOps<T>(statement: unknown, context: unknown): Promise<T> {
    return this.send<T>({
      type: 'sql_generate_ops',
      statement,
      context,
    });
  }

  async sqlBuildSelectPlan<T>(statement: unknown, schema: unknown): Promise<T> {
    return this.send<T>({
      type: 'sql_build_select_plan',
      statement,
      schema,
    });
  }

  async sqlEval<T>(statement: unknown, context: unknown, state: unknown): Promise<T> {
    return this.send<T>({
      type: 'sql_eval',
      statement,
      context,
      state,
    });
  }

  close(): void {
    this.proc.kill();
  }

  private flushError(error: Error): void {
    while (this.pending.length > 0) {
      const next = this.pending.shift();
      if (next) {
        next.reject(error);
      }
    }
  }
}

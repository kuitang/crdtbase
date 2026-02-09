import { EncodedCrdtOp } from './sql';

export type LogPosition = number;

export type LogEntry = {
  siteId: string;
  hlc: string;
  seq: LogPosition;
  ops: EncodedCrdtOp[];
};

export type AppendLogEntry = Omit<LogEntry, 'seq'>;

export interface ReplicatedLog {
  append(entry: AppendLogEntry): Promise<LogPosition>;
  readSince(siteId: string, since: LogPosition): Promise<LogEntry[]>;
  listSites(): Promise<string[]>;
  getHead(siteId: string): Promise<LogPosition>;
}

/**
 * Returns the maximal contiguous prefix of entries after `since`:
 * `since+1, since+2, ...`.
 *
 * Any gap stops advancement to prevent cursor skips under eventually-consistent
 * listings where higher seq objects may appear before lower seq objects.
 */
export function takeContiguousEntriesSince(
  entries: readonly LogEntry[],
  since: LogPosition,
): LogEntry[] {
  const ordered = [...entries].sort((left, right) => left.seq - right.seq);
  const contiguous: LogEntry[] = [];
  let expected = since + 1;
  for (const entry of ordered) {
    if (entry.seq < expected) {
      continue;
    }
    if (entry.seq !== expected) {
      break;
    }
    contiguous.push(entry);
    expected += 1;
  }
  return contiguous;
}

import { expect } from 'vitest';
import { parseE2eSeeds, type NormalizedTaskRow } from './orchestrator';

export type ChaosEnvConfig = {
  seeds: number[];
  steps: number;
  maxDelayMs: number;
  drainRounds: number;
  quiescenceRounds: number;
};

export function readPositiveIntEnv(name: string, fallback: number): number {
  const raw = process.env[name];
  if (!raw || raw.trim().length === 0) {
    return fallback;
  }
  const parsed = Number.parseInt(raw, 10);
  if (!Number.isFinite(parsed) || parsed <= 0) {
    throw new Error(`invalid ${name}='${raw}'`);
  }
  return parsed;
}

export function loadChaosEnv(defaultSeeds: number[] = [11, 29]): ChaosEnvConfig {
  return {
    seeds: parseE2eSeeds(process.env.E2E_CHAOS_SEEDS, defaultSeeds),
    steps: readPositiveIntEnv('E2E_CHAOS_STEPS', 140),
    maxDelayMs: readPositiveIntEnv('E2E_CHAOS_DELAY_MS', 8),
    drainRounds: readPositiveIntEnv('E2E_CHAOS_DRAIN_ROUNDS', 20),
    quiescenceRounds: readPositiveIntEnv('E2E_CHAOS_QUIESCENCE_ROUNDS', 3),
  };
}

function rowsById(rows: NormalizedTaskRow[]): Map<string, NormalizedTaskRow> {
  return new Map(rows.map((row) => [row.id, row]));
}

export function assertAckedWritesVisible(params: {
  rows: NormalizedTaskRow[];
  expectedPointsByRow: Record<string, number>;
  expectedTagsByRow: Record<string, string[]>;
}): void {
  const byId = rowsById(params.rows);
  for (const [rowId, expectedPoints] of Object.entries(params.expectedPointsByRow)) {
    const row = byId.get(rowId);
    expect(row, `missing row '${rowId}'`).toBeDefined();
    expect(row?.points).toBe(expectedPoints);
  }

  for (const [rowId, expectedTags] of Object.entries(params.expectedTagsByRow)) {
    const row = byId.get(rowId);
    expect(row, `missing row '${rowId}'`).toBeDefined();
    const actual = new Set(row?.tags ?? []);
    for (const tag of expectedTags) {
      expect(actual.has(tag), `row '${rowId}' missing expected tag '${tag}'`).toBe(true);
    }
  }
}

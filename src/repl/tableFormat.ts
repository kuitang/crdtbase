import { table } from 'table';

function stringifyValue(value: unknown): string {
  if (value === null || value === undefined) {
    return 'NULL';
  }
  if (typeof value === 'string') {
    return value;
  }
  if (typeof value === 'number' || typeof value === 'boolean' || typeof value === 'bigint') {
    return String(value);
  }
  if (Array.isArray(value)) {
    return `[${value.map((item) => stringifyValue(item)).join(', ')}]`;
  }
  try {
    return JSON.stringify(value);
  } catch {
    return String(value);
  }
}

function collectColumns(rows: Record<string, unknown>[]): string[] {
  const columns: string[] = [];
  const seen = new Set<string>();
  for (const row of rows) {
    for (const key of Object.keys(row)) {
      if (!seen.has(key)) {
        seen.add(key);
        columns.push(key);
      }
    }
  }
  return columns;
}

export function formatRowsAsTable(rows: Record<string, unknown>[]): string {
  if (rows.length === 0) {
    return '(0 rows)';
  }

  const columns = collectColumns(rows);
  if (columns.length === 0) {
    return '(0 columns)';
  }

  const matrix = rows.map((row) => columns.map((column) => stringifyValue(row[column])));
  const rendered = table([columns, ...matrix], {
    border: {
      topBody: '─',
      topJoin: '┬',
      topLeft: '┌',
      topRight: '┐',
      bottomBody: '─',
      bottomJoin: '┴',
      bottomLeft: '└',
      bottomRight: '┘',
      bodyLeft: '│',
      bodyRight: '│',
      bodyJoin: '│',
      joinBody: '─',
      joinLeft: '├',
      joinRight: '┤',
      joinJoin: '┼',
    },
    drawHorizontalLine: (lineIndex, rowCount) =>
      lineIndex === 0 || lineIndex === 1 || lineIndex === rowCount,
    singleLine: false,
  }).trimEnd();

  return `${rendered}\n(${rows.length} row${rows.length === 1 ? '' : 's'})`;
}

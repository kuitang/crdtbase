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

function pad(text: string, width: number): string {
  if (text.length >= width) {
    return text;
  }
  return text + ' '.repeat(width - text.length);
}

function border(widths: number[]): string {
  return `+${widths.map((width) => '-'.repeat(width + 2)).join('+')}+`;
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
  const widths = columns.map((column, index) => {
    let max = column.length;
    for (const line of matrix) {
      const len = line[index]!.length;
      if (len > max) {
        max = len;
      }
    }
    return max;
  });

  const lines: string[] = [];
  lines.push(border(widths));
  lines.push(
    `| ${columns.map((column, index) => pad(column, widths[index]!)).join(' | ')} |`,
  );
  lines.push(border(widths));

  for (const line of matrix) {
    lines.push(`| ${line.map((cell, index) => pad(cell, widths[index]!)).join(' | ')} |`);
  }

  lines.push(border(widths));
  lines.push(`(${rows.length} row${rows.length === 1 ? '' : 's'})`);

  return lines.join('\n');
}

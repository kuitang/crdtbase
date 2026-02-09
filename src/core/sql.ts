export type SqlScalarType = 'STRING' | 'NUMBER' | 'BOOLEAN';

export type SqlValue = string | number | boolean | null;

export type SqlComparisonOp = '=' | '!=' | '<' | '>' | '<=' | '>=';

export type SqlColumnType =
  | { kind: 'scalar'; scalar: SqlScalarType }
  | { kind: 'lww'; scalar: SqlScalarType }
  | { kind: 'counter' }
  | { kind: 'set'; scalar: SqlScalarType }
  | { kind: 'register'; scalar: SqlScalarType };

export type SqlCreateColumn = {
  name: string;
  type: SqlColumnType;
  primaryKey?: true;
};

export type SqlWhereCondition = {
  column: string;
  op: SqlComparisonOp;
  value: SqlValue;
};

export type CreateTableStatement = {
  kind: 'create_table';
  table: string;
  columns: SqlCreateColumn[];
  partitionBy?: string;
};

export type DropTableStatement = {
  kind: 'drop_table';
  table: string;
};

export type InsertStatement = {
  kind: 'insert';
  table: string;
  columns: string[];
  values: SqlValue[];
};

export type SqlAssignment = {
  column: string;
  value: SqlValue;
};

export type UpdateStatement = {
  kind: 'update';
  table: string;
  assignments: SqlAssignment[];
  where: SqlWhereCondition[];
};

export type SelectStatement = {
  kind: 'select';
  table: string;
  columns: '*' | string[];
  where?: SqlWhereCondition[];
};

export type DeleteStatement = {
  kind: 'delete';
  table: string;
  where: SqlWhereCondition[];
};

type CounterStatementBase = {
  table: string;
  column: string;
  amount: number;
  where: SqlWhereCondition[];
};

export type IncStatement = CounterStatementBase & {
  kind: 'inc';
};

export type DecStatement = CounterStatementBase & {
  kind: 'dec';
};

type SetStatementBase = {
  table: string;
  column: string;
  value: SqlValue;
  where: SqlWhereCondition[];
};

export type AddStatement = SetStatementBase & {
  kind: 'add';
};

export type RemoveStatement = SetStatementBase & {
  kind: 'remove';
};

export type SqlStatement =
  | CreateTableStatement
  | DropTableStatement
  | InsertStatement
  | UpdateStatement
  | SelectStatement
  | DeleteStatement
  | IncStatement
  | DecStatement
  | AddStatement
  | RemoveStatement;

export type SelectQuerySpec = {
  table: string;
  columns: SelectStatement['columns'];
  where?: SqlWhereCondition[];
};

export type SelectPlannerSchema = {
  partitionBy?: string | null;
};

export type SelectQueryRoute =
  | { kind: 'single_partition'; partition: string }
  | { kind: 'all_partitions' };

export type SelectQueryPlan = {
  table: string;
  columns: SelectStatement['columns'];
  partitionBy: string | null;
  route: SelectQueryRoute;
  filters: SqlWhereCondition[];
};

export type SqlPrimaryKey = string | number;

export type SetRemoveTag = {
  hlc: string;
  site: string;
};

type BaseCrdtOp = {
  tbl: string;
  key: SqlPrimaryKey;
  hlc: string;
  site: string;
};

export type RowExistsOp = BaseCrdtOp & {
  kind: 'row_exists';
  exists: boolean;
};

export type CellLwwOp = BaseCrdtOp & {
  kind: 'cell_lww';
  col: string;
  val: SqlValue;
};

export type CellCounterOp = BaseCrdtOp & {
  kind: 'cell_counter';
  col: string;
  d: 'inc' | 'dec';
  n: number;
};

export type CellOrSetAddOp = BaseCrdtOp & {
  kind: 'cell_or_set_add';
  col: string;
  val: SqlValue;
};

export type CellOrSetRemoveOp = BaseCrdtOp & {
  kind: 'cell_or_set_remove';
  col: string;
  tags: SetRemoveTag[];
};

export type CellMvRegisterOp = BaseCrdtOp & {
  kind: 'cell_mv_register';
  col: string;
  val: SqlValue;
};

export type EncodedCrdtOp =
  | RowExistsOp
  | CellLwwOp
  | CellCounterOp
  | CellOrSetAddOp
  | CellOrSetRemoveOp
  | CellMvRegisterOp;

export type SqlColumnCrdt = 'scalar' | 'lww' | 'pn_counter' | 'or_set' | 'mv_register';

export type SqlTableSchema = {
  pk: string;
  partitionBy?: string | null;
  columns: Record<string, { crdt: SqlColumnCrdt }>;
};

export type SqlSchema = Record<string, SqlTableSchema>;

export type RemoveTagResolverInput = {
  table: string;
  key: SqlPrimaryKey;
  column: string;
  value: SqlValue;
  where: SqlWhereCondition[];
};

export type CrdtOpGenerationContext = {
  schema: SqlSchema;
  site: string;
  nextHlc: () => string;
  resolveSetRemoveTags?: (input: RemoveTagResolverInput) => SetRemoveTag[];
};

export type SqlExecutionPlan =
  | { kind: 'ddl_create_table'; table: string; schema: SqlTableSchema }
  | { kind: 'ddl_drop_table'; table: string }
  | { kind: 'read'; select: SelectQueryPlan }
  | {
      kind: 'write';
      statementKind: InsertStatement['kind']
      | UpdateStatement['kind']
      | IncStatement['kind']
      | DecStatement['kind']
      | AddStatement['kind']
      | RemoveStatement['kind']
      | DeleteStatement['kind'];
      ops: EncodedCrdtOp[];
    };

const COMPARISON_OPERATORS = new Set<SqlComparisonOp>(['=', '!=', '<', '>', '<=', '>=']);

type Token =
  | { kind: 'identifier'; text: string }
  | { kind: 'string'; value: string }
  | { kind: 'number'; value: number }
  | { kind: 'symbol'; text: string }
  | { kind: 'eof' };

const SINGLE_CHAR_SYMBOLS = new Set(['(', ')', ',', ';', '*', '<', '>', '=', '.']);

function isWhitespace(char: string): boolean {
  return /\s/u.test(char);
}

function isDigit(char: string): boolean {
  return char >= '0' && char <= '9';
}

function isIdentifierStart(char: string): boolean {
  return (char >= 'a' && char <= 'z') || (char >= 'A' && char <= 'Z') || char === '_';
}

function isIdentifierPart(char: string): boolean {
  return isIdentifierStart(char) || isDigit(char);
}

function tokenize(input: string): Token[] {
  const tokens: Token[] = [];
  let index = 0;

  while (index < input.length) {
    const char = input[index]!;
    if (isWhitespace(char)) {
      index += 1;
      continue;
    }

    const nextTwo = input.slice(index, index + 2);
    if (nextTwo === '<=' || nextTwo === '>=' || nextTwo === '!=') {
      tokens.push({ kind: 'symbol', text: nextTwo });
      index += 2;
      continue;
    }

    if (char === "'") {
      index += 1;
      let value = '';
      let closed = false;
      while (index < input.length) {
        const next = input[index]!;
        if (next === "'") {
          if (input[index + 1] === "'") {
            value += "'";
            index += 2;
            continue;
          }
          index += 1;
          closed = true;
          break;
        }
        value += next;
        index += 1;
      }
      if (!closed) {
        throw new Error('unterminated string literal');
      }
      tokens.push({ kind: 'string', value });
      continue;
    }

    if (isDigit(char) || (char === '-' && isDigit(input[index + 1] ?? ''))) {
      const start = index;
      if (input[index] === '-') {
        index += 1;
      }
      while (index < input.length && isDigit(input[index]!)) {
        index += 1;
      }
      if (input[index] === '.') {
        index += 1;
        if (!isDigit(input[index] ?? '')) {
          throw new Error('invalid number literal');
        }
        while (index < input.length && isDigit(input[index]!)) {
          index += 1;
        }
      }
      const raw = input.slice(start, index);
      const value = Number(raw);
      if (!Number.isFinite(value)) {
        throw new Error(`invalid number literal: ${raw}`);
      }
      tokens.push({ kind: 'number', value });
      continue;
    }

    if (isIdentifierStart(char)) {
      const start = index;
      index += 1;
      while (index < input.length && isIdentifierPart(input[index]!)) {
        index += 1;
      }
      tokens.push({ kind: 'identifier', text: input.slice(start, index) });
      continue;
    }

    if (SINGLE_CHAR_SYMBOLS.has(char)) {
      tokens.push({ kind: 'symbol', text: char });
      index += 1;
      continue;
    }

    throw new Error(`unexpected character '${char}'`);
  }

  tokens.push({ kind: 'eof' });
  return tokens;
}

class Parser {
  private index = 0;

  constructor(private readonly tokens: Token[]) {}

  parse(): SqlStatement {
    const statement = this.parseStatement();
    this.matchSymbol(';');
    this.expectEof();
    return statement;
  }

  private parseStatement(): SqlStatement {
    if (this.matchKeyword('CREATE')) return this.parseCreateTable();
    if (this.matchKeyword('DROP')) return this.parseDropTable();
    if (this.matchKeyword('INSERT')) return this.parseInsert();
    if (this.matchKeyword('UPDATE')) return this.parseUpdate();
    if (this.matchKeyword('SELECT')) return this.parseSelect();
    if (this.matchKeyword('DELETE')) return this.parseDelete();
    if (this.matchKeyword('INC')) return this.parseCounterMutation('inc');
    if (this.matchKeyword('DEC')) return this.parseCounterMutation('dec');
    if (this.matchKeyword('ADD')) return this.parseSetMutation('add');
    if (this.matchKeyword('REMOVE')) return this.parseSetMutation('remove');
    this.raise(`unsupported SQL statement, got ${this.describeToken(this.peek())}`);
  }

  private parseCreateTable(): CreateTableStatement {
    this.expectKeyword('TABLE');
    const table = this.expectIdentifier();
    this.expectSymbol('(');
    const columns = this.parseCreateColumns();
    this.expectSymbol(')');

    const partitionBy = this.matchKeyword('PARTITION')
      ? this.parsePartitionBy()
      : undefined;

    return partitionBy
      ? { kind: 'create_table', table, columns, partitionBy }
      : { kind: 'create_table', table, columns };
  }

  private parsePartitionBy(): string {
    this.expectKeyword('BY');
    return this.expectIdentifier();
  }

  private parseCreateColumns(): SqlCreateColumn[] {
    const columns: SqlCreateColumn[] = [this.parseCreateColumn()];
    while (this.matchSymbol(',')) {
      columns.push(this.parseCreateColumn());
    }
    return columns;
  }

  private parseCreateColumn(): SqlCreateColumn {
    const name = this.expectIdentifier();
    if (this.matchKeyword('PRIMARY')) {
      this.expectKeyword('KEY');
      // Primary key is structural (non-CRDT), represented internally as scalar.
      return { name, type: { kind: 'scalar', scalar: 'STRING' }, primaryKey: true };
    }
    const type = this.parseColumnType();
    if (this.matchKeyword('PRIMARY')) {
      this.expectKeyword('KEY');
      this.raise(
        `PRIMARY KEY column '${name}' must be declared as '${name} PRIMARY KEY' without a type`,
      );
    }
    return { name, type };
  }

  private parseColumnType(): SqlColumnType {
    if (this.matchKeyword('COUNTER')) {
      return { kind: 'counter' };
    }
    if (this.matchKeyword('LWW')) {
      this.expectSymbol('<');
      const scalar = this.parseScalarType();
      this.expectSymbol('>');
      return { kind: 'lww', scalar };
    }
    if (this.matchKeyword('SET')) {
      this.expectSymbol('<');
      const scalar = this.parseScalarType();
      this.expectSymbol('>');
      return { kind: 'set', scalar };
    }
    if (this.matchKeyword('REGISTER')) {
      this.expectSymbol('<');
      const scalar = this.parseScalarType();
      this.expectSymbol('>');
      return { kind: 'register', scalar };
    }
    this.raise(`expected CRDT column type (LWW<...>, COUNTER, SET<...>, REGISTER<...>)`);
  }

  private parseScalarType(): SqlScalarType {
    if (this.matchKeyword('STRING')) return 'STRING';
    if (this.matchKeyword('NUMBER')) return 'NUMBER';
    if (this.matchKeyword('BOOLEAN')) return 'BOOLEAN';
    this.raise(`expected scalar type, got ${this.describeToken(this.peek())}`);
  }

  private parseDropTable(): DropTableStatement {
    this.expectKeyword('TABLE');
    const table = this.expectIdentifier();
    return { kind: 'drop_table', table };
  }

  private parseInsert(): InsertStatement {
    this.expectKeyword('INTO');
    const table = this.expectIdentifier();
    this.expectSymbol('(');
    const columns = this.parseIdentifierList();
    this.expectSymbol(')');
    this.expectKeyword('VALUES');
    this.expectSymbol('(');
    const values = this.parseLiteralList();
    this.expectSymbol(')');

    if (columns.length !== values.length) {
      this.raise(
        `INSERT columns/values length mismatch (${columns.length} columns, ${values.length} values)`,
      );
    }
    return { kind: 'insert', table, columns, values };
  }

  private parseUpdate(): UpdateStatement {
    const table = this.expectIdentifier();
    this.expectKeyword('SET');
    const assignments = this.parseAssignments();
    const where = this.parseWhere(true);
    return { kind: 'update', table, assignments, where };
  }

  private parseAssignments(): SqlAssignment[] {
    const assignments: SqlAssignment[] = [this.parseAssignment()];
    while (this.matchSymbol(',')) {
      assignments.push(this.parseAssignment());
    }
    return assignments;
  }

  private parseAssignment(): SqlAssignment {
    const column = this.expectIdentifier();
    this.expectSymbol('=');
    const value = this.parseLiteral();
    return { column, value };
  }

  private parseSelect(): SelectStatement {
    const columns = this.matchSymbol('*') ? '*' : this.parseIdentifierList();
    this.expectKeyword('FROM');
    const table = this.expectIdentifier();
    const where = this.parseWhere(false);
    return where
      ? { kind: 'select', table, columns, where }
      : { kind: 'select', table, columns };
  }

  private parseDelete(): DeleteStatement {
    this.expectKeyword('FROM');
    const table = this.expectIdentifier();
    const where = this.parseWhere(true);
    return { kind: 'delete', table, where };
  }

  private parseCounterMutation(kind: 'inc' | 'dec'): IncStatement | DecStatement {
    const { table, column } = this.parseQualifiedColumn();
    this.expectKeyword('BY');
    const amount = this.parseNumericLiteral();
    const where = this.parseWhere(true);
    return { kind, table, column, amount, where };
  }

  private parseSetMutation(kind: 'add' | 'remove'): AddStatement | RemoveStatement {
    const value = this.parseLiteral();
    if (kind === 'add') {
      this.expectKeyword('TO');
    } else {
      this.expectKeyword('FROM');
    }
    const { table, column } = this.parseQualifiedColumn();
    const where = this.parseWhere(true);
    return { kind, table, column, value, where };
  }

  private parseQualifiedColumn(): { table: string; column: string } {
    const table = this.expectIdentifier();
    this.expectSymbol('.');
    const column = this.expectIdentifier();
    return { table, column };
  }

  private parseWhere(required: true): SqlWhereCondition[];
  private parseWhere(required: false): SqlWhereCondition[] | undefined;
  private parseWhere(required: boolean): SqlWhereCondition[] | undefined {
    if (!this.matchKeyword('WHERE')) {
      if (required) {
        this.raise('expected WHERE clause');
      }
      return undefined;
    }

    const conditions: SqlWhereCondition[] = [this.parseWhereCondition()];
    while (this.matchKeyword('AND')) {
      conditions.push(this.parseWhereCondition());
    }
    return conditions;
  }

  private parseWhereCondition(): SqlWhereCondition {
    const column = this.expectIdentifier();
    const op = this.parseComparisonOp();
    const value = this.parseLiteral();
    return { column, op, value };
  }

  private parseComparisonOp(): SqlComparisonOp {
    const token = this.peek();
    if (token.kind === 'symbol' && COMPARISON_OPERATORS.has(token.text as SqlComparisonOp)) {
      this.index += 1;
      return token.text as SqlComparisonOp;
    }
    this.raise(`expected comparison operator, got ${this.describeToken(token)}`);
  }

  private parseNumericLiteral(): number {
    const token = this.peek();
    if (token.kind !== 'number') {
      this.raise(`expected numeric literal, got ${this.describeToken(token)}`);
    }
    this.index += 1;
    return token.value;
  }

  private parseLiteralList(): SqlValue[] {
    const values: SqlValue[] = [this.parseLiteral()];
    while (this.matchSymbol(',')) {
      values.push(this.parseLiteral());
    }
    return values;
  }

  private parseIdentifierList(): string[] {
    const identifiers: string[] = [this.expectIdentifier()];
    while (this.matchSymbol(',')) {
      identifiers.push(this.expectIdentifier());
    }
    return identifiers;
  }

  private parseLiteral(): SqlValue {
    const token = this.peek();
    if (token.kind === 'string') {
      this.index += 1;
      return token.value;
    }
    if (token.kind === 'number') {
      this.index += 1;
      return token.value;
    }
    if (token.kind === 'identifier') {
      const upper = token.text.toUpperCase();
      if (upper === 'TRUE') {
        this.index += 1;
        return true;
      }
      if (upper === 'FALSE') {
        this.index += 1;
        return false;
      }
      if (upper === 'NULL') {
        this.index += 1;
        return null;
      }
    }
    this.raise(`expected SQL literal, got ${this.describeToken(token)}`);
  }

  private matchKeyword(keyword: string): boolean {
    const token = this.peek();
    if (token.kind !== 'identifier') return false;
    if (token.text.toUpperCase() !== keyword) return false;
    this.index += 1;
    return true;
  }

  private expectKeyword(keyword: string): void {
    if (!this.matchKeyword(keyword)) {
      this.raise(`expected keyword ${keyword}, got ${this.describeToken(this.peek())}`);
    }
  }

  private matchSymbol(symbol: string): boolean {
    const token = this.peek();
    if (token.kind !== 'symbol' || token.text !== symbol) return false;
    this.index += 1;
    return true;
  }

  private expectSymbol(symbol: string): void {
    if (!this.matchSymbol(symbol)) {
      this.raise(`expected symbol '${symbol}', got ${this.describeToken(this.peek())}`);
    }
  }

  private expectIdentifier(): string {
    const token = this.peek();
    if (token.kind !== 'identifier') {
      this.raise(`expected identifier, got ${this.describeToken(token)}`);
    }
    this.index += 1;
    return token.text;
  }

  private expectEof(): void {
    if (this.peek().kind !== 'eof') {
      this.raise(`unexpected trailing input: ${this.describeToken(this.peek())}`);
    }
  }

  private peek(): Token {
    return this.tokens[this.index]!;
  }

  private describeToken(token: Token): string {
    switch (token.kind) {
      case 'identifier':
        return `identifier(${token.text})`;
      case 'string':
        return `string(${token.value})`;
      case 'number':
        return `number(${token.value})`;
      case 'symbol':
        return `symbol(${token.text})`;
      case 'eof':
        return 'EOF';
    }
  }

  private raise(message: string): never {
    throw new Error(`${message} at token index ${this.index}`);
  }
}

export function parseSql(sql: string): SqlStatement {
  return new Parser(tokenize(sql)).parse();
}

export function printSqlLiteral(value: SqlValue): string {
  if (value === null) return 'NULL';
  if (typeof value === 'string') return `'${value.replace(/'/g, "''")}'`;
  if (typeof value === 'boolean') return value ? 'TRUE' : 'FALSE';
  if (typeof value === 'number' && Number.isFinite(value)) return String(value);
  throw new Error(`unsupported SQL literal: ${String(value)}`);
}

function printComparison(condition: SqlWhereCondition): string {
  return `${condition.column} ${condition.op} ${printSqlLiteral(condition.value)}`;
}

function printWhere(where: SqlWhereCondition[] | undefined): string {
  if (!where || where.length === 0) return '';
  return ` WHERE ${where.map(printComparison).join(' AND ')}`;
}

function printScalarType(scalar: SqlScalarType): string {
  return scalar;
}

function printColumnType(type: SqlColumnType): string {
  switch (type.kind) {
    case 'scalar':
      return printScalarType(type.scalar);
    case 'lww':
      return `LWW<${printScalarType(type.scalar)}>`;
    case 'counter':
      return 'COUNTER';
    case 'set':
      return `SET<${printScalarType(type.scalar)}>`;
    case 'register':
      return `REGISTER<${printScalarType(type.scalar)}>`;
  }
}

export function printSql(statement: SqlStatement): string {
  switch (statement.kind) {
    case 'create_table': {
      const columns = statement.columns
        .map((column) => {
          if (column.primaryKey) {
            return `${column.name} PRIMARY KEY`;
          }
          return `${column.name} ${printColumnType(column.type)}`;
        })
        .join(', ');
      const partition = statement.partitionBy ? ` PARTITION BY ${statement.partitionBy}` : '';
      return `CREATE TABLE ${statement.table} (${columns})${partition}`;
    }
    case 'drop_table':
      return `DROP TABLE ${statement.table}`;
    case 'insert':
      return `INSERT INTO ${statement.table} (${statement.columns.join(', ')}) VALUES (${statement.values
        .map(printSqlLiteral)
        .join(', ')})`;
    case 'update':
      return `UPDATE ${statement.table} SET ${statement.assignments
        .map((assignment) => `${assignment.column} = ${printSqlLiteral(assignment.value)}`)
        .join(', ')}${printWhere(statement.where)}`;
    case 'select': {
      const projection =
        statement.columns === '*' ? '*' : statement.columns.join(', ');
      return `SELECT ${projection} FROM ${statement.table}${printWhere(statement.where)}`;
    }
    case 'delete':
      return `DELETE FROM ${statement.table}${printWhere(statement.where)}`;
    case 'inc':
      return `INC ${statement.table}.${statement.column} BY ${statement.amount}${printWhere(
        statement.where,
      )}`;
    case 'dec':
      return `DEC ${statement.table}.${statement.column} BY ${statement.amount}${printWhere(
        statement.where,
      )}`;
    case 'add':
      return `ADD ${printSqlLiteral(statement.value)} TO ${statement.table}.${statement.column}${printWhere(
        statement.where,
      )}`;
    case 'remove':
      return `REMOVE ${printSqlLiteral(statement.value)} FROM ${statement.table}.${statement.column}${printWhere(
        statement.where,
      )}`;
  }
}

function toPartitionKey(value: SqlValue): string {
  return value === null ? 'NULL' : String(value);
}

function pickPartitionCondition(
  where: SqlWhereCondition[],
  partitionBy: string,
): { partition: string; remaining: SqlWhereCondition[] } | null {
  const index = where.findIndex(
    (condition) => condition.column === partitionBy && condition.op === '=',
  );
  if (index < 0) {
    return null;
  }

  const selected = where[index]!;
  return {
    partition: toPartitionKey(selected.value),
    remaining: where.filter((_, conditionIndex) => conditionIndex !== index),
  };
}

export function buildSelectPlan(
  statement: SelectStatement,
  schema: SelectPlannerSchema = {},
): SelectQueryPlan {
  const partitionBy = schema.partitionBy ?? null;
  const where = statement.where ? [...statement.where] : [];
  if (partitionBy === null) {
    return {
      table: statement.table,
      columns: statement.columns,
      partitionBy: null,
      route: { kind: 'single_partition', partition: '_default' },
      filters: where,
    };
  }

  const routed = pickPartitionCondition(where, partitionBy);
  if (!routed) {
    return {
      table: statement.table,
      columns: statement.columns,
      partitionBy,
      route: { kind: 'all_partitions' },
      filters: where,
    };
  }

  return {
    table: statement.table,
    columns: statement.columns,
    partitionBy,
    route: { kind: 'single_partition', partition: routed.partition },
    filters: routed.remaining,
  };
}

export function buildSelectPlanFromSql(
  sql: string,
  schema: SelectPlannerSchema = {},
): SelectQueryPlan {
  const statement = parseSql(sql);
  if (statement.kind !== 'select') {
    throw new Error(`expected SELECT statement, got ${statement.kind}`);
  }
  return buildSelectPlan(statement, schema);
}

export function buildSelectQuery(spec: SelectQuerySpec): string {
  const statement: SelectStatement = spec.where
    ? { kind: 'select', table: spec.table, columns: spec.columns, where: spec.where }
    : { kind: 'select', table: spec.table, columns: spec.columns };
  return printSql(statement);
}

function columnTypeToSchema(type: SqlColumnType): SqlColumnCrdt {
  switch (type.kind) {
    case 'scalar':
      return 'scalar';
    case 'lww':
      return 'lww';
    case 'counter':
      return 'pn_counter';
    case 'set':
      return 'or_set';
    case 'register':
      return 'mv_register';
  }
}

export function tableSchemaFromCreate(statement: CreateTableStatement): SqlTableSchema {
  const primaryKeys = statement.columns.filter((column) => column.primaryKey);
  if (primaryKeys.length !== 1) {
    throw new Error(
      `CREATE TABLE ${statement.table} must declare exactly one PRIMARY KEY column`,
    );
  }

  const columns: SqlTableSchema['columns'] = {};
  const pkName = primaryKeys[0]!.name;
  for (const column of statement.columns) {
    if (columns[column.name]) {
      throw new Error(
        `CREATE TABLE ${statement.table} has duplicate column '${column.name}'`,
      );
    }
    if (column.type.kind === 'scalar' && column.name !== pkName) {
      columns[column.name] = { crdt: 'lww' };
      continue;
    }
    columns[column.name] = { crdt: columnTypeToSchema(column.type) };
  }

  return {
    pk: pkName,
    partitionBy: statement.partitionBy ?? null,
    columns,
  };
}

export function applyDdlToSchema(
  schema: SqlSchema,
  statement: CreateTableStatement | DropTableStatement,
): SqlSchema {
  if (statement.kind === 'create_table') {
    return {
      ...schema,
      [statement.table]: tableSchemaFromCreate(statement),
    };
  }
  const next = { ...schema };
  delete next[statement.table];
  return next;
}

function requireTableSchema(schema: SqlSchema, table: string): SqlTableSchema {
  const tableSchema = schema[table];
  if (!tableSchema) {
    throw new Error(`unknown table '${table}'`);
  }
  return tableSchema;
}

function requireColumnSchema(tableSchema: SqlTableSchema, table: string, column: string): { crdt: SqlColumnCrdt } {
  const columnSchema = tableSchema.columns[column];
  if (!columnSchema) {
    throw new Error(`unknown column '${column}' for table '${table}'`);
  }
  return columnSchema;
}

function assertPrimaryKeyValue(value: SqlValue, table: string, pk: string): SqlPrimaryKey {
  if (typeof value !== 'string' && typeof value !== 'number') {
    throw new Error(
      `primary key '${table}.${pk}' must be STRING or NUMBER, got ${String(value)}`,
    );
  }
  return value;
}

function findPrimaryKeyInWhere(
  where: SqlWhereCondition[],
  table: string,
  pk: string,
): SqlPrimaryKey {
  const condition = where.find((item) => item.column === pk && item.op === '=');
  if (!condition) {
    throw new Error(`write on '${table}' requires WHERE ${pk} = <value>`);
  }
  return assertPrimaryKeyValue(condition.value, table, pk);
}

function ensureCounterAmount(amount: number, table: string, column: string): number {
  if (!Number.isFinite(amount) || amount < 0) {
    throw new Error(`counter mutation requires non-negative finite BY amount for ${table}.${column}`);
  }
  return amount;
}

function createOp(
  context: CrdtOpGenerationContext,
  table: string,
  key: SqlPrimaryKey,
): BaseCrdtOp {
  return {
    tbl: table,
    key,
    hlc: context.nextHlc(),
    site: context.site,
  };
}

function createRowExistsOp(
  context: CrdtOpGenerationContext,
  table: string,
  key: SqlPrimaryKey,
  exists: boolean,
): EncodedCrdtOp {
  const op = createOp(context, table, key);
  return { ...op, kind: 'row_exists', exists };
}

function createInsertColumnOp(
  statement: InsertStatement,
  tableSchema: SqlTableSchema,
  context: CrdtOpGenerationContext,
  key: SqlPrimaryKey,
  column: string,
  value: SqlValue,
): EncodedCrdtOp | null {
  const columnSchema = requireColumnSchema(tableSchema, statement.table, column);
  switch (columnSchema.crdt) {
    case 'scalar':
      if (column === tableSchema.pk) {
        return null;
      }
      return {
        ...createOp(context, statement.table, key),
        kind: 'cell_lww',
        col: column,
        val: value,
      };
    case 'lww':
      return {
        ...createOp(context, statement.table, key),
        kind: 'cell_lww',
        col: column,
        val: value,
      };
    case 'mv_register':
      return {
        ...createOp(context, statement.table, key),
        kind: 'cell_mv_register',
        col: column,
        val: value,
      };
    case 'pn_counter':
      if (typeof value !== 'number') {
        throw new Error(`INSERT for counter column '${statement.table}.${column}' requires NUMBER`);
      }
      return {
        ...createOp(context, statement.table, key),
        kind: 'cell_counter',
        col: column,
        d: 'inc',
        n: value,
      };
    case 'or_set':
      return {
        ...createOp(context, statement.table, key),
        kind: 'cell_or_set_add',
        col: column,
        val: value,
      };
  }
}

function createUpdateColumnOp(
  statement: UpdateStatement,
  tableSchema: SqlTableSchema,
  context: CrdtOpGenerationContext,
  key: SqlPrimaryKey,
  assignment: SqlAssignment,
): EncodedCrdtOp {
  const columnSchema = requireColumnSchema(tableSchema, statement.table, assignment.column);
  switch (columnSchema.crdt) {
    case 'lww':
      return {
        ...createOp(context, statement.table, key),
        kind: 'cell_lww',
        col: assignment.column,
        val: assignment.value,
      };
    case 'mv_register':
      return {
        ...createOp(context, statement.table, key),
        kind: 'cell_mv_register',
        col: assignment.column,
        val: assignment.value,
      };
    case 'scalar':
      if (assignment.column === tableSchema.pk) {
        throw new Error(`UPDATE cannot target primary key column '${statement.table}.${assignment.column}'`);
      }
      return {
        ...createOp(context, statement.table, key),
        kind: 'cell_lww',
        col: assignment.column,
        val: assignment.value,
      };
    case 'pn_counter':
      throw new Error(`UPDATE cannot target counter column '${statement.table}.${assignment.column}'; use INC/DEC`);
    case 'or_set':
      throw new Error(`UPDATE cannot target set column '${statement.table}.${assignment.column}'; use ADD/REMOVE`);
  }
}

function generateInsertOps(
  statement: InsertStatement,
  tableSchema: SqlTableSchema,
  context: CrdtOpGenerationContext,
): EncodedCrdtOp[] {
  const valuesByColumn = new Map<string, SqlValue>();
  for (let index = 0; index < statement.columns.length; index += 1) {
    valuesByColumn.set(statement.columns[index]!, statement.values[index]!);
  }

  const primaryValue = valuesByColumn.get(tableSchema.pk);
  if (primaryValue === undefined) {
    throw new Error(`INSERT into '${statement.table}' must include primary key column '${tableSchema.pk}'`);
  }
  const key = assertPrimaryKeyValue(primaryValue, statement.table, tableSchema.pk);

  const ops: EncodedCrdtOp[] = [createRowExistsOp(context, statement.table, key, true)];
  for (let index = 0; index < statement.columns.length; index += 1) {
    const column = statement.columns[index]!;
    if (column === tableSchema.pk) {
      continue;
    }
    const op = createInsertColumnOp(
      statement,
      tableSchema,
      context,
      key,
      column,
      statement.values[index]!,
    );
    if (op) {
      ops.push(op);
    }
  }
  return ops;
}

function generateUpdateOps(
  statement: UpdateStatement,
  tableSchema: SqlTableSchema,
  context: CrdtOpGenerationContext,
): EncodedCrdtOp[] {
  const key = findPrimaryKeyInWhere(statement.where, statement.table, tableSchema.pk);
  return [
    createRowExistsOp(context, statement.table, key, true),
    ...statement.assignments.map((assignment) =>
      createUpdateColumnOp(statement, tableSchema, context, key, assignment),
    ),
  ];
}

function generateCounterOps(
  statement: IncStatement | DecStatement,
  tableSchema: SqlTableSchema,
  context: CrdtOpGenerationContext,
): EncodedCrdtOp[] {
  const key = findPrimaryKeyInWhere(statement.where, statement.table, tableSchema.pk);
  const columnSchema = requireColumnSchema(tableSchema, statement.table, statement.column);
  if (columnSchema.crdt !== 'pn_counter') {
    throw new Error(`column '${statement.table}.${statement.column}' is not a COUNTER`);
  }
  return [
    createRowExistsOp(context, statement.table, key, true),
    {
      ...createOp(context, statement.table, key),
      kind: 'cell_counter',
      col: statement.column,
      d: statement.kind,
      n: ensureCounterAmount(statement.amount, statement.table, statement.column),
    },
  ];
}

function generateSetAddOps(
  statement: AddStatement,
  tableSchema: SqlTableSchema,
  context: CrdtOpGenerationContext,
): EncodedCrdtOp[] {
  const key = findPrimaryKeyInWhere(statement.where, statement.table, tableSchema.pk);
  const columnSchema = requireColumnSchema(tableSchema, statement.table, statement.column);
  if (columnSchema.crdt !== 'or_set') {
    throw new Error(`column '${statement.table}.${statement.column}' is not a SET`);
  }
  return [
    createRowExistsOp(context, statement.table, key, true),
    {
      ...createOp(context, statement.table, key),
      kind: 'cell_or_set_add',
      col: statement.column,
      val: statement.value,
    },
  ];
}

function generateSetRemoveOps(
  statement: RemoveStatement,
  tableSchema: SqlTableSchema,
  context: CrdtOpGenerationContext,
): EncodedCrdtOp[] {
  const key = findPrimaryKeyInWhere(statement.where, statement.table, tableSchema.pk);
  const columnSchema = requireColumnSchema(tableSchema, statement.table, statement.column);
  if (columnSchema.crdt !== 'or_set') {
    throw new Error(`column '${statement.table}.${statement.column}' is not a SET`);
  }
  const tags = context.resolveSetRemoveTags
    ? context.resolveSetRemoveTags({
        table: statement.table,
        key,
        column: statement.column,
        value: statement.value,
        where: statement.where,
      })
    : [];
  if (tags.length === 0) {
    return [];
  }
  return [
    createRowExistsOp(context, statement.table, key, true),
    {
      ...createOp(context, statement.table, key),
      kind: 'cell_or_set_remove',
      col: statement.column,
      tags,
    },
  ];
}

function generateDeleteOps(
  statement: DeleteStatement,
  tableSchema: SqlTableSchema,
  context: CrdtOpGenerationContext,
): EncodedCrdtOp[] {
  const key = findPrimaryKeyInWhere(statement.where, statement.table, tableSchema.pk);
  return [createRowExistsOp(context, statement.table, key, false)];
}

export function generateCrdtOps(
  statement:
    | InsertStatement
    | UpdateStatement
    | IncStatement
    | DecStatement
    | AddStatement
    | RemoveStatement
    | DeleteStatement,
  context: CrdtOpGenerationContext,
): EncodedCrdtOp[] {
  const tableSchema = requireTableSchema(context.schema, statement.table);

  switch (statement.kind) {
    case 'insert':
      return generateInsertOps(statement, tableSchema, context);
    case 'update':
      return generateUpdateOps(statement, tableSchema, context);
    case 'inc':
    case 'dec':
      return generateCounterOps(statement, tableSchema, context);
    case 'add':
      return generateSetAddOps(statement, tableSchema, context);
    case 'remove':
      return generateSetRemoveOps(statement, tableSchema, context);
    case 'delete':
      return generateDeleteOps(statement, tableSchema, context);
  }
}

export function generateCrdtOpsFromSql(
  sql: string,
  context: CrdtOpGenerationContext,
): EncodedCrdtOp[] {
  const statement = parseSql(sql);
  if (statement.kind === 'select' || statement.kind === 'create_table' || statement.kind === 'drop_table') {
    throw new Error(`statement '${statement.kind}' does not generate CRDT ops`);
  }
  return generateCrdtOps(statement, context);
}

export function buildSqlExecutionPlanFromStatement(
  statement: SqlStatement,
  context: Partial<CrdtOpGenerationContext> = {},
): SqlExecutionPlan {
  switch (statement.kind) {
    case 'create_table':
      return {
        kind: 'ddl_create_table',
        table: statement.table,
        schema: tableSchemaFromCreate(statement),
      };
    case 'drop_table':
      return {
        kind: 'ddl_drop_table',
        table: statement.table,
      };
    case 'select': {
      const tableSchema =
        context.schema && context.schema[statement.table]
          ? context.schema[statement.table]
          : null;
      return {
        kind: 'read',
        select: buildSelectPlan(statement, {
          partitionBy: tableSchema?.partitionBy ?? null,
        }),
      };
    }
    case 'insert':
    case 'update':
    case 'inc':
    case 'dec':
    case 'add':
    case 'remove':
    case 'delete': {
      if (!context.schema || !context.site || !context.nextHlc) {
        throw new Error('write planning requires schema, site, and nextHlc');
      }
      return {
        kind: 'write',
        statementKind: statement.kind,
        ops: generateCrdtOps(statement, {
          schema: context.schema,
          site: context.site,
          nextHlc: context.nextHlc,
          resolveSetRemoveTags: context.resolveSetRemoveTags,
        }),
      };
    }
  }
}

export function buildSqlExecutionPlanFromSql(
  sql: string,
  context: Partial<CrdtOpGenerationContext> = {},
): SqlExecutionPlan {
  return buildSqlExecutionPlanFromStatement(parseSql(sql), context);
}

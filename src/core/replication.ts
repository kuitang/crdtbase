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

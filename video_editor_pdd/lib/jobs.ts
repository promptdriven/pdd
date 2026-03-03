// server-only guard — enforced by Next.js bundler in production
try { require('server-only'); } catch {}

import * as crypto from "crypto";
import type { Job, JobStatus, PipelineStage, SseSend } from "./types";
import { getDb } from "./db";

type Executor = (
  onLog: (msg: string) => void,
  onProgress?: (percent: number) => void
) => Promise<void>;

export type ExecutorFactory = (
  params: Record<string, unknown>,
  send: SseSend
) => Executor;

const executorRegistry = new Map<PipelineStage, ExecutorFactory>();
const jobSendRegistry = new Map<string, SseSend>();

const noopSend: SseSend = () => {
  // Intentionally empty
};

const DAG: Record<PipelineStage, PipelineStage[]> = {
  setup: [],
  script: ["setup"],
  "tts-script": ["script"],
  "tts-render": ["tts-script"],
  "audio-sync": ["tts-render"],
  specs: ["script"],
  veo: ["specs"],
  compositions: ["audio-sync", "veo"],
  render: ["compositions"],
  audit: ["render"],
};

function isoNow(): string {
  return new Date(Date.now()).toISOString();
}

function parseParams(raw: unknown): Record<string, unknown> {
  if (raw && typeof raw === "string") {
    try {
      return JSON.parse(raw) as Record<string, unknown>;
    } catch {
      return {};
    }
  }
  if (raw && typeof raw === "object") {
    return raw as Record<string, unknown>;
  }
  return {};
}

function appendLog(jobId: string, message: string): void {
  const db = getDb();
  const line = message.endsWith("\n") ? message : `${message}\n`;
  try {
    db.prepare(
      `UPDATE jobs
       SET logs = COALESCE(logs, '') || ?,
           updatedAt = ?
       WHERE id = ?`
    ).run(line, isoNow(), jobId);
  } catch {
    // The logs column might not exist in older schemas; ignore if so.
  }
}

function updateProgress(jobId: string, percent: number): number {
  const normalized = Math.max(0, Math.min(100, Math.round(percent)));
  const db = getDb();
  db.prepare(`UPDATE jobs SET progress = ?, updatedAt = ? WHERE id = ?`).run(
    normalized,
    isoNow(),
    jobId
  );
  return normalized;
}

function upsertPipelineStatus(
  stage: PipelineStage,
  status: JobStatus,
  jobId: string,
  error: string | null
): void {
  const db = getDb();
  db.prepare(
    `INSERT OR REPLACE INTO pipeline_status (stage, status, lastJobId, error, updatedAt)
     VALUES (?, ?, ?, ?, ?)`
  ).run(stage, status, jobId, error, isoNow());
}

function getPipelineStatus(stage: PipelineStage): {
  status: JobStatus;
  lastJobId: string | null;
} | null {
  const db = getDb();
  const row = db
    .prepare(`SELECT status, lastJobId FROM pipeline_status WHERE stage = ?`)
    .get(stage) as { status: JobStatus; lastJobId: string | null } | undefined;

  return row ?? null;
}

export function registerExecutor(stage: PipelineStage, factory: ExecutorFactory): void {
  executorRegistry.set(stage, factory);
}

export function createJob(
  stage: PipelineStage,
  params: Record<string, unknown> = {}
): string {
  const db = getDb();
  const id = crypto.randomUUID();
  const now = isoNow();

  const payload = JSON.stringify(params ?? {});
  try {
    db.prepare(
      `INSERT INTO jobs (id, stage, status, progress, error, params, logs, createdAt, updatedAt)
       VALUES (?, ?, 'pending', 0, NULL, ?, '', ?, ?)`
    ).run(id, stage, payload, now, now);
  } catch {
    db.prepare(
      `INSERT INTO jobs (id, stage, status, progress, error, params, createdAt, updatedAt)
       VALUES (?, ?, 'pending', 0, NULL, ?, ?, ?)`
    ).run(id, stage, payload, now, now);
  }

  return id;
}

export function getJob(jobId: string): Job | undefined {
  const db = getDb();
  const row = db.prepare(`SELECT * FROM jobs WHERE id = ?`).get(jobId) as
    | {
        id: string;
        stage: PipelineStage;
        status: JobStatus;
        progress: number;
        error: string | null;
        params: string | Record<string, unknown>;
        createdAt: string;
        updatedAt: string;
      }
    | undefined;

  if (!row) return undefined;

  return {
    id: row.id,
    stage: row.stage,
    status: row.status,
    progress: row.progress ?? 0,
    error: row.error ?? null,
    params: parseParams(row.params),
    createdAt: row.createdAt,
    updatedAt: row.updatedAt,
  };
}

export async function runJob(
  jobId: string,
  executor: (onLog: (msg: string) => void) => Promise<void>
): Promise<void> {
  const db = getDb();
  const row = db
    .prepare(`SELECT stage FROM jobs WHERE id = ?`)
    .get(jobId) as { stage: PipelineStage } | undefined;

  if (!row) {
    throw new Error(`Job not found: ${jobId}`);
  }

  const stage = row.stage;
  db.prepare(
    `UPDATE jobs SET status = 'running', progress = 0, error = NULL, updatedAt = ? WHERE id = ?`
  ).run(isoNow(), jobId);
  upsertPipelineStatus(stage, "running", jobId, null);

  const send = jobSendRegistry.get(jobId) ?? noopSend;

  const onLog = (message: string): void => {
    appendLog(jobId, message);
    send({ type: "log", message, jobId });
  };

  const onProgress = (percent: number): void => {
    const normalized = updateProgress(jobId, percent);
    send({ type: "progress", percent: normalized, jobId });
  };

  // Attach progress callback to onLog so executors can use onLog.progress(percent)
  (onLog as unknown as { progress: typeof onProgress }).progress = onProgress;

  try {
    await executor(onLog);

    db.prepare(
      `UPDATE jobs SET status = 'done', progress = 100, updatedAt = ? WHERE id = ?`
    ).run(isoNow(), jobId);
    upsertPipelineStatus(stage, "done", jobId, null);
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    db.prepare(
      `UPDATE jobs SET status = 'error', error = ?, updatedAt = ? WHERE id = ?`
    ).run(message, isoNow(), jobId);
    upsertPipelineStatus(stage, "error", jobId, message);
    throw error;
  } finally {
    jobSendRegistry.delete(jobId);
  }
}

export async function retryJob(jobId: string): Promise<void> {
  const job = getJob(jobId);
  if (!job) {
    throw new Error(`Job not found: ${jobId}`);
  }

  const factory = executorRegistry.get(job.stage);
  if (!factory) {
    throw new Error(`No executor registered for stage "${job.stage}"`);
  }

  const db = getDb();
  db.prepare(
    `UPDATE jobs SET status = 'pending', progress = 0, error = NULL, updatedAt = ? WHERE id = ?`
  ).run(isoNow(), jobId);

  const executor = factory(job.params, noopSend);
  await runJob(jobId, executor);
}

export async function runPipelineStage(
  stage: PipelineStage,
  params: Record<string, unknown>,
  send: SseSend
): Promise<string> {
  const memo = new Map<PipelineStage, Promise<string>>();

  const ensureStage = async (target: PipelineStage): Promise<string> => {
    if (memo.has(target)) {
      return memo.get(target)!;
    }

    const promise = (async (): Promise<string> => {
      const statusRow = getPipelineStatus(target);
      if (statusRow?.status === "done" && statusRow.lastJobId) {
        return statusRow.lastJobId;
      }

      const prereqs = DAG[target] ?? [];
      await Promise.all(prereqs.map((req) => ensureStage(req)));

      const factory = executorRegistry.get(target);
      if (!factory) {
        throw new Error(`No executor registered for stage "${target}"`);
      }

      const jobId = createJob(target, params);
      jobSendRegistry.set(jobId, send);
      const executor = factory(params, send);
      await runJob(jobId, executor);

      return jobId;
    })();

    memo.set(target, promise);
    return promise;
  };

  return ensureStage(stage);
}

export { DAG, DAG as PIPELINE_DAG };
// lib/jobs.ts
try { require('server-only'); } catch { /* running outside Next.js bundler */ }

import * as crypto from 'crypto';
import type { PipelineStage, Job, JobStatus, SseSend, OnLog } from './types';
import { getDb } from './db';

export type ExecutorFactory = (
  params: Record<string, unknown>,
  send: SseSend
) => (onLog: (msg: string) => void) => Promise<void>;

// Persist on globalThis so registrations survive Next.js dev-mode HMR.
const _g = globalThis as typeof globalThis & {
  __pipelineExecutors?: Map<PipelineStage, ExecutorFactory>;
  __jobSendMap?: Map<string, SseSend>;
  __pipelineExecutorLoads?: Map<PipelineStage, Promise<void>>;
};
if (!_g.__pipelineExecutors) _g.__pipelineExecutors = new Map();
if (!_g.__jobSendMap) _g.__jobSendMap = new Map();
if (!_g.__pipelineExecutorLoads) _g.__pipelineExecutorLoads = new Map();

const EXECUTORS: Map<PipelineStage, ExecutorFactory> = _g.__pipelineExecutors;
const EXECUTOR_LOADS: Map<PipelineStage, Promise<void>> = _g.__pipelineExecutorLoads;

export function registerExecutor(stage: PipelineStage, factory: ExecutorFactory): void {
  EXECUTORS.set(stage, factory);
}

/** Remove all registered executors (test helper). */
export function clearExecutors(): void {
  EXECUTORS.clear();
  EXECUTOR_LOADS.clear();
}

const EXECUTOR_IMPORTERS: Partial<Record<PipelineStage, () => Promise<unknown>>> = {
  'tts-script': () => import('../app/api/pipeline/tts-script/run/route'),
  'tts-render': () => import('../app/api/pipeline/tts-render/run/route'),
  'audio-sync': () => import('../app/api/pipeline/audio-sync/run/route'),
  specs: () => import('../app/api/pipeline/specs/run/route'),
  veo: () => import('../app/api/pipeline/veo/run/route'),
  compositions: () => import('../app/api/pipeline/compositions/run/route'),
  render: () => import('../app/api/pipeline/render/run/route'),
  audit: () => import('../app/api/pipeline/audit/run/route'),
};

async function ensureExecutorRegistered(stage: PipelineStage): Promise<void> {
  if (EXECUTORS.has(stage)) {
    return;
  }

  const importer = EXECUTOR_IMPORTERS[stage];
  if (!importer) {
    return;
  }

  let loadPromise = EXECUTOR_LOADS.get(stage);
  if (!loadPromise) {
    loadPromise = importer()
      .then(() => undefined)
      .finally(() => {
        EXECUTOR_LOADS.delete(stage);
      });
    EXECUTOR_LOADS.set(stage, loadPromise);
  }

  await loadPromise;
}

// ---------------------------------------------------------------------------
// Pipeline DAG
// ---------------------------------------------------------------------------
export const PIPELINE_DAG: Record<PipelineStage, PipelineStage[]> = {
  setup: [],
  script: ['setup'],
  'tts-script': ['script'],
  'tts-render': ['tts-script'],
  'audio-sync': ['tts-render'],
  specs: ['script'],
  veo: ['specs'],
  compositions: ['audio-sync', 'veo'],
  render: ['compositions'],
  audit: ['render'],
};

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

const NOOP_SEND: SseSend = () => {
  // intentionally empty
};

function nowIso(): string {
  return new Date(Date.now()).toISOString();
}

const JOB_LOG_PREFIX = "__ts__:";

function serializeJobLogLine(message: string, timestamp: string): string {
  const normalizedMessage = message.endsWith("\n")
    ? message.slice(0, -1)
    : message;
  return `${JOB_LOG_PREFIX}${timestamp}\t${normalizedMessage}\n`;
}

export function parseStoredJobLogLine(
  line: string
): { message: string; timestamp?: string } {
  if (!line.startsWith(JOB_LOG_PREFIX)) {
    return { message: line };
  }

  const payload = line.slice(JOB_LOG_PREFIX.length);
  const separatorIndex = payload.indexOf("\t");
  if (separatorIndex === -1) {
    return { message: line };
  }

  const timestamp = payload.slice(0, separatorIndex).trim();
  const message = payload.slice(separatorIndex + 1);
  return timestamp ? { message, timestamp } : { message };
}

function getStageStatus(stage: PipelineStage): {
  status: string;
  lastJobId: string | null;
} | null {
  const db = getDb();
  const row = db
    .prepare(
      `SELECT status, lastJobId FROM pipeline_status WHERE stage = ? LIMIT 1`
    )
    .get(stage) as { status: string; lastJobId: string | null } | undefined;

  return row ?? null;
}

function upsertPipelineStatus(
  stage: PipelineStage,
  status: string,
  lastJobId: string,
  error: string | null = null
): void {
  const db = getDb();
  const updatedAt = nowIso();
  db.prepare(
    `INSERT INTO pipeline_status (stage, status, lastJobId, error, updatedAt)
     VALUES (?, ?, ?, ?, ?)
     ON CONFLICT(stage) DO UPDATE SET
       status = excluded.status,
       lastJobId = excluded.lastJobId,
       error = excluded.error,
       updatedAt = excluded.updatedAt`
  ).run(stage, status, lastJobId, error, updatedAt);
}

function safeAppendLog(jobId: string, msg: string): string {
  const db = getDb();
  const updatedAt = nowIso();
  const line = serializeJobLogLine(msg, updatedAt);

  try {
    db.prepare(
      `UPDATE jobs
       SET logs = COALESCE(logs, '') || ?, updatedAt = ?
       WHERE id = ?`
    ).run(line, updatedAt, jobId);
  } catch {
    // logs column might not exist in older schema; ignore gracefully
  }

  return updatedAt;
}

function updateProgress(jobId: string, percent: number): void {
  const db = getDb();
  db.prepare(
    `UPDATE jobs
     SET progress = ?, updatedAt = ?, status = 'running'
     WHERE id = ?`
  ).run(percent, nowIso(), jobId);
}

function parseJobParams(raw: unknown): Record<string, unknown> {
  if (raw && typeof raw === 'object') {
    return raw as Record<string, unknown>;
  }

  if (typeof raw !== 'string') {
    return {};
  }

  const trimmed = raw.trim();
  if (!trimmed) {
    return {};
  }

  try {
    const parsed = JSON.parse(trimmed);
    return parsed && typeof parsed === 'object'
      ? (parsed as Record<string, unknown>)
      : {};
  } catch {
    return {};
  }
}

// ---------------------------------------------------------------------------
// API
// ---------------------------------------------------------------------------

export function createJob(
  stage: PipelineStage,
  params: Record<string, unknown>,
  retryOf?: string
): string {
  const db = getDb();
  const id = crypto.randomUUID();
  const now = nowIso();

  const jsonParams = JSON.stringify(params ?? {});

  try {
    // Prefer insert with logs and retryOf columns
    db.prepare(
      `INSERT INTO jobs (id, stage, status, progress, error, params, logs, createdAt, updatedAt, retryOf)
       VALUES (?, ?, 'pending', 0, NULL, ?, '', ?, ?, ?)`
    ).run(id, stage, jsonParams, now, now, retryOf ?? null);
  } catch {
    // Fallback if retryOf column missing
    db.prepare(
      `INSERT INTO jobs (id, stage, status, progress, error, params, logs, createdAt, updatedAt)
       VALUES (?, ?, 'pending', 0, NULL, ?, '', ?, ?)`
    ).run(id, stage, jsonParams, now, now);
  }

  return id;
}

export function getJob(jobId: string): Job | undefined {
  const db = getDb();
  const row = db
    .prepare(`SELECT * FROM jobs WHERE id = ? LIMIT 1`)
    .get(jobId) as Record<string, unknown> | undefined;

  if (!row) return undefined;

  const params = parseJobParams(row.params);

  return {
    id: row.id as string,
    stage: row.stage as PipelineStage,
    status: row.status as JobStatus,
    progress: (row.progress as number) ?? 0,
    error: (row.error as string | null) ?? null,
    params,
    logs: (row.logs as string) ?? '',
    retryOf: (row.retryOf as string | null) ?? null,
    createdAt: row.createdAt as string,
    updatedAt: row.updatedAt as string,
  };
}

/**
 * Run a job with an executor that accepts an onLog callback.
 * The onLog handler appends logs to DB and emits SSE events.
 * Progress can be emitted from executor via:
 *   (onLog as any).progress?.(percent)
 */
export async function runJob(
  jobId: string,
  executor: (onLog: OnLog) => Promise<void>
): Promise<void> {
  const db = getDb();
  const jobRow = db
    .prepare(`SELECT stage FROM jobs WHERE id = ? LIMIT 1`)
    .get(jobId) as { stage: PipelineStage } | undefined;

  if (!jobRow) {
    throw new Error(`Job not found: ${jobId}`);
  }

  const stage = jobRow.stage;
  const updatedAt = nowIso();

  db.prepare(
    `UPDATE jobs
     SET status = 'running', updatedAt = ?
     WHERE id = ?`
  ).run(updatedAt, jobId);

  upsertPipelineStatus(stage, 'running', jobId);

  const send = JOB_SEND_MAP.get(jobId) ?? NOOP_SEND;

  // Emit jobId immediately so the frontend can start tracking the job
  // before the executor produces any output.
  send({ type: 'started', jobId });

  const onLog: OnLog = Object.assign(
    (msg: string): void => {
      const timestamp = safeAppendLog(jobId, msg);
      send({ type: 'log', message: msg, timestamp, jobId });
    },
    {
      progress: (percent: number): void => {
        updateProgress(jobId, percent);
        send({ type: 'progress', percent, jobId });
      },
    }
  );

  try {
    await executor(onLog);

    db.prepare(
      `UPDATE jobs
       SET status = 'done', progress = 100, error = NULL, updatedAt = ?
       WHERE id = ?`
    ).run(nowIso(), jobId);

    upsertPipelineStatus(stage, 'done', jobId, null);
  } catch (err) {
    const message =
      err instanceof Error ? err.message : 'Unknown job error';

    db.prepare(
      `UPDATE jobs
       SET status = 'error', error = ?, updatedAt = ?
       WHERE id = ?`
    ).run(message, nowIso(), jobId);

    upsertPipelineStatus(stage, 'error', jobId, message);
  }
}

/**
 * Retry a failed job by creating a NEW job linked to the original via retryOf.
 * The original job is NOT mutated — it keeps its error status.
 * Returns the new job ID.
 */
export async function retryJob(jobId: string): Promise<string> {
  const db = getDb();
  const row = db
    .prepare(`SELECT stage, params FROM jobs WHERE id = ? LIMIT 1`)
    .get(jobId) as { stage: PipelineStage; params: string } | undefined;

  if (!row) {
    throw new Error(`Job not found: ${jobId}`);
  }

  const params = parseJobParams(row.params);

  await ensureExecutorRegistered(row.stage);
  const factory = EXECUTORS.get(row.stage);
  if (!factory) {
    throw new Error(`No executor registered for stage "${row.stage}"`);
  }

  // Create a new job linked to the original
  const newJobId = createJob(row.stage, params as Record<string, unknown>, jobId);

  const executor = factory(params as Record<string, unknown>, NOOP_SEND);
  await runJob(newJobId, executor);

  return newJobId;
}

const JOB_SEND_MAP: Map<string, SseSend> = _g.__jobSendMap!;

export function setJobSend(jobId: string, send: SseSend): void {
  JOB_SEND_MAP.set(jobId, send);
}

export function clearJobSend(jobId: string): void {
  JOB_SEND_MAP.delete(jobId);
}

/**
 * Create a job and start its executor in the background (fire-and-forget).
 * Returns the jobId immediately so the caller can return it to the client.
 * The client should connect to GET /api/jobs/[id]/stream for live updates.
 */
export function startJobInBackground(
  stage: PipelineStage,
  params: Record<string, unknown> = {}
): string {
  const factory = EXECUTORS.get(stage);
  const jobId = createJob(stage, params);

  if (!factory) {
    console.warn(`No executor registered for stage "${stage}"; job created but not started`);
    return jobId;
  }

  const executor = factory(params, NOOP_SEND);
  runJob(jobId, executor).catch((err) => {
    console.error(`Background job ${jobId} (${stage}) failed:`, err);
  });

  return jobId;
}

/**
 * Orchestrate DAG execution. Upstream stages are auto-run concurrently
 * if not already complete, then the requested stage is run.
 */
export async function runPipelineStage(
  stage: PipelineStage,
  params: Record<string, unknown>,
  send: SseSend
): Promise<string> {
  const memo = new Map<PipelineStage, Promise<string | undefined>>();

  const runStageWithDeps = async (
    current: PipelineStage,
    forceRun: boolean
  ): Promise<string | undefined> => {
    if (memo.has(current)) {
      return memo.get(current)!;
    }

    const promise = (async (): Promise<string | undefined> => {
      const deps = PIPELINE_DAG[current] ?? [];
      await Promise.all(deps.map((dep) => runStageWithDeps(dep, false)));

      if (!forceRun) {
        const status = getStageStatus(current);
        if (status?.status === 'done' && status.lastJobId) {
          return status.lastJobId;
        }
      }

      await ensureExecutorRegistered(current);
      const factory = EXECUTORS.get(current);
      if (!factory) {
        if (!forceRun) {
          // UI-only stage (e.g. setup, script) — no executor needed.
          return undefined;
        }
        throw new Error(`No executor registered for stage "${current}"`);
      }

      const jobId = createJob(current, params);

      // Notify the client immediately so SseLogPanel can connect
      // while the executor is still running.
      if (forceRun) {
        send({ type: "job", jobId });
      }

      // Store send handler for runJob's onLog
      JOB_SEND_MAP.set(jobId, send);

      try {
        const executor = factory(params, send);
        await runJob(jobId, executor);
      } finally {
        JOB_SEND_MAP.delete(jobId);
      }

      return jobId;
    })();

    memo.set(current, promise);
    return promise;
  };

  const jobId = await runStageWithDeps(stage, true);
  if (!jobId) {
    throw new Error(`Failed to run stage "${stage}"`);
  }
  return jobId;
}

export async function runPipelineStageDirect(
  stage: PipelineStage,
  params: Record<string, unknown>,
  send: SseSend
): Promise<string> {
  await ensureExecutorRegistered(stage);
  const factory = EXECUTORS.get(stage);
  if (!factory) {
    throw new Error(`No executor registered for stage "${stage}"`);
  }

  const jobId = createJob(stage, params);
  send({ type: "job", jobId });
  JOB_SEND_MAP.set(jobId, send);

  try {
    const executor = factory(params, send);
    await runJob(jobId, executor);
  } finally {
    JOB_SEND_MAP.delete(jobId);
  }

  return jobId;
}

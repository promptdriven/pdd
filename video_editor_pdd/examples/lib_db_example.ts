// example_usage.ts
// Comprehensive usage example for lib/db.ts
// This file demonstrates how to use the SQLite persistence layer
// for the video production pipeline editor.
//
// IMPORTANT: This module is server-only. It can only be imported in:
//   - Next.js Route Handlers (app/api/**/route.ts)
//   - Server Actions
//   - Server Components
//   - Other server-only modules
//
// Attempting to import it in a Client Component will throw a build error
// thanks to the "server-only" guard.

// Use an in-memory database for this example so each run starts fresh
process.env.DB_PATH = ":memory:";

import { getDb, runMigrations, recoverCrashedJobs } from "../lib/db";
import type { Database } from "better-sqlite3";
import { randomUUID } from "crypto";

// ============================================================================
// Example 1: Basic singleton access with getDb()
// ============================================================================

/**
 * getDb() returns the singleton better-sqlite3 Database instance.
 *
 * - On first call: opens (or creates) the SQLite file at
 *   `process.env.DB_PATH` (default: `<cwd>/pipeline.db`),
 *   enables WAL journal mode, runs schema migrations, and
 *   recovers any jobs left in "running" state from a prior crash.
 * - On subsequent calls: returns the cached instance immediately.
 *
 * @returns {Database} The better-sqlite3 Database instance (synchronous API).
 */
const db: Database = getDb();

console.log("Database connection established. WAL mode active.");

// ============================================================================
// Example 2: Creating a new pipeline job
// ============================================================================

/**
 * Insert a new job into the `jobs` table.
 *
 * Table schema:
 *   id        TEXT PRIMARY KEY  — UUID identifying the job
 *   stage     TEXT              — pipeline stage (e.g. 'tts-render', 'veo', 'render')
 *   status    TEXT              — lifecycle state: 'pending' | 'running' | 'done' | 'error'
 *   progress  REAL              — completion percentage 0.0–100.0
 *   error     TEXT              — error message or null
 *   params    TEXT              — JSON-serialized Record<string, unknown>
 *   createdAt TEXT              — ISO 8601 timestamp
 *   updatedAt TEXT              — ISO 8601 timestamp
 */
function createJob(
  stage: string,
  params: Record<string, unknown> = {}
): string {
  const db = getDb();
  const id = randomUUID();
  const now = new Date().toISOString();

  db.prepare(
    `INSERT INTO jobs (id, stage, status, progress, error, params, createdAt, updatedAt)
     VALUES (?, ?, 'pending', 0, NULL, ?, ?, ?)`
  ).run(id, stage, JSON.stringify(params), now, now);

  console.log(`Created job ${id} for stage "${stage}"`);
  return id;
}

const jobId = createJob("tts-render", {
  sectionId: "intro",
  voice: "en-US-Neural2-F",
});

// ============================================================================
// Example 3: Updating job status and progress
// ============================================================================

/**
 * Transition a job to "running" status and update its progress.
 *
 * @param jobId    — The UUID of the job to update
 * @param progress — Completion percentage (0–100)
 */
function updateJobProgress(jobId: string, progress: number): void {
  const db = getDb();
  const now = new Date().toISOString();

  const result = db
    .prepare(
      `UPDATE jobs SET status='running', progress=?, updatedAt=? WHERE id=?`
    )
    .run(progress, now, jobId);

  console.log(`Updated job ${jobId}: progress=${progress}%, rows changed=${result.changes}`);
}

/**
 * Mark a job as completed successfully.
 *
 * @param jobId — The UUID of the job to complete
 */
function completeJob(jobId: string): void {
  const db = getDb();
  const now = new Date().toISOString();

  db.prepare(
    `UPDATE jobs SET status='done', progress=100, updatedAt=? WHERE id=?`
  ).run(now, jobId);

  console.log(`Job ${jobId} completed successfully.`);
}

/**
 * Mark a job as failed with an error message.
 *
 * @param jobId   — The UUID of the job
 * @param error   — Human-readable error description
 */
function failJob(jobId: string, error: string): void {
  const db = getDb();
  const now = new Date().toISOString();

  db.prepare(
    `UPDATE jobs SET status='error', error=?, updatedAt=? WHERE id=?`
  ).run(error, now, jobId);

  console.log(`Job ${jobId} failed: ${error}`);
}

// Simulate a job lifecycle
updateJobProgress(jobId, 25);
updateJobProgress(jobId, 50);
updateJobProgress(jobId, 75);
completeJob(jobId);

// ============================================================================
// Example 4: Querying jobs by stage
// ============================================================================

/**
 * Retrieve all jobs for a given pipeline stage, ordered by creation time.
 *
 * @param stage — The pipeline stage to filter by (e.g. 'tts-render')
 * @returns Array of job row objects. The `params` field is a JSON string
 *          that must be parsed with JSON.parse() by the caller.
 */
function getJobsByStage(stage: string): Array<Record<string, unknown>> {
  const db = getDb();

  const rows = db
    .prepare(`SELECT * FROM jobs WHERE stage = ? ORDER BY createdAt DESC`)
    .all(stage) as Array<Record<string, unknown>>;

  console.log(`Found ${rows.length} jobs for stage "${stage}"`);
  return rows;
}

const ttsJobs = getJobsByStage("tts-render");
for (const job of ttsJobs) {
  // Parse the JSON params column back into an object
  const params =
    typeof job.params === "string" ? JSON.parse(job.params) : job.params;
  console.log(`  Job ${job.id}: status=${job.status}, params=`, params);
}

// ============================================================================
// Example 5: Creating and querying annotations
// ============================================================================

/**
 * Insert an annotation into the `annotations` table.
 *
 * Table schema:
 *   id               TEXT PRIMARY KEY  — UUID
 *   sectionId        TEXT              — which video section this targets
 *   timestamp        REAL              — playback time in seconds
 *   text             TEXT              — user description of the issue
 *   videoFile        TEXT              — path to the video file (nullable)
 *   drawingDataUrl   TEXT              — base64 data URL of drawing (nullable)
 *   compositeDataUrl TEXT              — base64 data URL of frame+drawing (nullable)
 *   analysis         TEXT              — JSON-serialized AnnotationAnalysis (nullable)
 *   resolved         INTEGER           — 0 = unresolved, 1 = resolved
 *   resolveJobId     TEXT              — job ID that fixed this (nullable)
 *   createdAt        TEXT              — ISO 8601 timestamp
 *
 * @param sectionId — The section this annotation belongs to
 * @param timestamp — Playback position in seconds
 * @param text      — User's description of the issue
 * @param videoFile — Path to the video file being annotated
 * @returns The generated annotation ID
 */
function createAnnotation(
  sectionId: string,
  timestamp: number,
  text: string,
  videoFile: string | null = null
): string {
  const db = getDb();
  const id = randomUUID();
  const now = new Date().toISOString();

  db.prepare(
    `INSERT INTO annotations (id, sectionId, timestamp, text, videoFile, drawingDataUrl, compositeDataUrl, analysis, resolved, resolveJobId, createdAt)
     VALUES (?, ?, ?, ?, ?, NULL, NULL, NULL, 0, NULL, ?)`
  ).run(id, sectionId, timestamp, text, videoFile, now);

  console.log(`Created annotation ${id} on section "${sectionId}" at ${timestamp}s`);
  return id;
}

/**
 * Store Claude's analysis result on an existing annotation.
 *
 * @param annotationId — The annotation to update
 * @param analysis     — The AnnotationAnalysis object (will be JSON-serialized)
 */
function setAnnotationAnalysis(
  annotationId: string,
  analysis: {
    severity: string;
    fixType: string;
    technicalAssessment: string;
    suggestedFixes: string[];
    confidence: number;
  }
): void {
  const db = getDb();

  db.prepare(`UPDATE annotations SET analysis = ? WHERE id = ?`).run(
    JSON.stringify(analysis),
    annotationId
  );

  console.log(
    `Set analysis on annotation ${annotationId}: severity=${analysis.severity}, fixType=${analysis.fixType}`
  );
}

/**
 * Get all unresolved annotations for a section.
 *
 * @param sectionId — The section to query
 * @returns Array of annotation rows. The `analysis` field is a JSON string
 *          (or null) that must be parsed by the caller.
 */
function getUnresolvedAnnotations(
  sectionId: string
): Array<Record<string, unknown>> {
  const db = getDb();

  return db
    .prepare(
      `SELECT * FROM annotations WHERE sectionId = ? AND resolved = 0 ORDER BY timestamp ASC`
    )
    .all(sectionId) as Array<Record<string, unknown>>;
}

const annId = createAnnotation(
  "intro",
  3.2,
  "Text is cut off on the right side",
  "output/sections/intro.mp4"
);

setAnnotationAnalysis(annId, {
  severity: "major",
  fixType: "remotion",
  technicalAssessment:
    "Text overlay at 3.2s is clipped by the safe-zone boundary.",
  suggestedFixes: ["Reduce font size from 48px to 40px"],
  confidence: 0.87,
});

const unresolvedAnns = getUnresolvedAnnotations("intro");
console.log(`Unresolved annotations for "intro":`, unresolvedAnns.length);

// ============================================================================
// Example 6: Managing pipeline_status for stage badges
// ============================================================================

/**
 * Upsert the pipeline status for a given stage.
 * The `pipeline_status` table provides a fast lookup for UI stage badges
 * without scanning the entire jobs table.
 *
 * Table schema:
 *   stage     TEXT PRIMARY KEY  — pipeline stage name
 *   status    TEXT              — 'not_started' | 'running' | 'done' | 'error'
 *   lastJobId TEXT              — most recent job ID for this stage
 *   error     TEXT              — error message (nullable)
 *   updatedAt TEXT              — ISO 8601 timestamp
 *
 * @param stage     — The pipeline stage (e.g. 'tts-render')
 * @param status    — The new status
 * @param lastJobId — The job ID that triggered this status change
 * @param error     — Optional error message
 */
function upsertPipelineStatus(
  stage: string,
  status: string,
  lastJobId: string,
  error: string | null = null
): void {
  const db = getDb();
  const now = new Date().toISOString();

  db.prepare(
    `INSERT INTO pipeline_status (stage, status, lastJobId, error, updatedAt)
     VALUES (?, ?, ?, ?, ?)
     ON CONFLICT(stage) DO UPDATE SET
       status = excluded.status,
       lastJobId = excluded.lastJobId,
       error = excluded.error,
       updatedAt = excluded.updatedAt`
  ).run(stage, status, lastJobId, error, now);

  console.log(`Pipeline status: stage="${stage}" → ${status}`);
}

/**
 * Get the current status of all pipeline stages.
 *
 * @returns Array of pipeline_status rows
 */
function getAllPipelineStatuses(): Array<Record<string, unknown>> {
  const db = getDb();
  return db
    .prepare(`SELECT * FROM pipeline_status ORDER BY updatedAt DESC`)
    .all() as Array<Record<string, unknown>>;
}

upsertPipelineStatus("tts-render", "running", jobId);
upsertPipelineStatus("tts-render", "done", jobId);

const statuses = getAllPipelineStatuses();
console.log("Pipeline statuses:", statuses);

// ============================================================================
// Example 7: Using transactions for atomic multi-table updates
// ============================================================================

/**
 * Resolve an annotation by marking it resolved and linking the fix job.
 * Uses a transaction to ensure both the annotation update and the
 * pipeline status update happen atomically.
 *
 * @param annotationId — The annotation to resolve
 * @param fixJobId     — The job that performed the fix
 * @param stage        — The pipeline stage for status update
 */
function resolveAnnotation(
  annotationId: string,
  fixJobId: string,
  stage: string
): void {
  const db = getDb();

  const resolveTransaction = db.transaction(() => {
    // Mark annotation as resolved
    db.prepare(
      `UPDATE annotations SET resolved = 1, resolveJobId = ? WHERE id = ?`
    ).run(fixJobId, annotationId);

    // Update the fix job to done
    const now = new Date().toISOString();
    db.prepare(
      `UPDATE jobs SET status = 'done', progress = 100, updatedAt = ? WHERE id = ?`
    ).run(now, fixJobId);

    // Update pipeline status
    upsertPipelineStatus(stage, "done", fixJobId);
  });

  resolveTransaction();
  console.log(
    `Annotation ${annotationId} resolved by job ${fixJobId}`
  );
}

// Create a fix job and resolve the annotation
const fixJobId = createJob("audit", { annotationId: annId, fixType: "remotion" });
resolveAnnotation(annId, fixJobId, "audit");

// ============================================================================
// Example 8: Crash recovery demonstration
// ============================================================================

/**
 * recoverCrashedJobs(db) is called automatically by getDb() on first
 * initialization. It finds all jobs with status='running' and marks them
 * as status='error' with the message "Server restarted during pipeline".
 *
 * This handles the case where the Node.js process crashed or was killed
 * while a pipeline job was in progress.
 *
 * You typically don't call this manually — it's shown here for illustration.
 */

// Simulate a "crashed" job by inserting one with status='running'
const crashedJobId = randomUUID();
const now = new Date().toISOString();
db.prepare(
  `INSERT INTO jobs (id, stage, status, progress, error, params, createdAt, updatedAt)
   VALUES (?, 'veo', 'running', 33, NULL, '{}', ?, ?)`
).run(crashedJobId, now, now);

console.log(`\nSimulated crashed job: ${crashedJobId}`);

// Manually invoke crash recovery (normally done by getDb() on startup)
recoverCrashedJobs(db);

// Verify the crashed job was recovered
const recoveredJob = db
  .prepare(`SELECT id, status, error FROM jobs WHERE id = ?`)
  .get(crashedJobId) as Record<string, unknown>;

console.log("Recovered job:", recoveredJob);
// => { id: '...', status: 'error', error: 'Server restarted during pipeline' }

// ============================================================================
// Example 9: Using getDb() in a Next.js Route Handler
// ============================================================================

/**
 * In a real Next.js app, you'd use getDb() inside Route Handlers like this:
 *
 * ```typescript
 * // app/api/jobs/route.ts
 * import { getDb } from '@/lib/db';
 * import { NextResponse } from 'next/server';
 *
 * export async function GET(request: Request) {
 *   const db = getDb();
 *   const url = new URL(request.url);
 *   const stage = url.searchParams.get('stage');
 *
 *   let jobs;
 *   if (stage) {
 *     jobs = db.prepare('SELECT * FROM jobs WHERE stage = ? ORDER BY createdAt DESC').all(stage);
 *   } else {
 *     jobs = db.prepare('SELECT * FROM jobs ORDER BY createdAt DESC LIMIT 50').all();
 *   }
 *
 *   // Parse JSON params for each job
 *   const parsed = jobs.map((job: any) => ({
 *     ...job,
 *     params: job.params ? JSON.parse(job.params) : null,
 *   }));
 *
 *   return NextResponse.json(parsed);
 * }
 *
 * export async function POST(request: Request) {
 *   const db = getDb();
 *   const body = await request.json();
 *   const id = randomUUID();
 *   const now = new Date().toISOString();
 *
 *   db.prepare(
 *     `INSERT INTO jobs (id, stage, status, progress, error, params, createdAt, updatedAt)
 *      VALUES (?, ?, 'pending', 0, NULL, ?, ?, ?)`
 *   ).run(id, body.stage, JSON.stringify(body.params ?? {}), now, now);
 *
 *   return NextResponse.json({ id, status: 'pending' }, { status: 201 });
 * }
 * ```
 *
 * Because better-sqlite3 is synchronous and Node.js is single-threaded,
 * concurrent requests are safe without any locking mechanism.
 */

// ============================================================================
// Example 10: Custom DB_PATH via environment variable
// ============================================================================

/**
 * To use a custom database file location, set the DB_PATH environment variable
 * before the first call to getDb():
 *
 *   DB_PATH=/data/my-project/pipeline.db npm run dev
 *
 * Or in .env.local:
 *   DB_PATH=./data/pipeline.db
 *
 * If DB_PATH is not set, the database defaults to `<cwd>/pipeline.db`.
 */

// ============================================================================
// Cleanup: Show final state of all tables
// ============================================================================

console.log("\n=== Final Database State ===");

const allJobs = db.prepare("SELECT id, stage, status, progress FROM jobs").all();
console.log("Jobs:", allJobs);

const allAnnotations = db
  .prepare("SELECT id, sectionId, resolved, timestamp FROM annotations")
  .all();
console.log("Annotations:", allAnnotations);

const allStatuses = db.prepare("SELECT * FROM pipeline_status").all();
console.log("Pipeline statuses:", allStatuses);
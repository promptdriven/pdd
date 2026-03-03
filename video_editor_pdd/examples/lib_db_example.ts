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

// --- Standalone execution setup ---
// When running outside Next.js (e.g., via tsx), the "server-only" package
// unconditionally throws because the "react-server" export condition is not
// active.  We register a no-op in the require cache so the guard is skipped
// for this standalone demo while keeping db.ts unchanged for production.
const _serverOnlyResolved = require.resolve("server-only");
require.cache[_serverOnlyResolved] = {
  id: _serverOnlyResolved,
  filename: _serverOnlyResolved,
  loaded: true,
  exports: {},
  children: [],
  paths: [],
} as any;

// Use an in-memory database for this example so each run starts fresh
process.env.DB_PATH = ":memory:";

// Use require() instead of import to guarantee ordering after the mock above
// (ES import declarations are hoisted above statements by the transpiler).
const { getDb, runMigrations, recoverCrashedJobs } = require("../lib/db") as typeof import("../lib/db");
import { randomUUID } from "crypto";

// ============================================================================
// Example 1: Initialize the database
// ============================================================================

/**
 * getDb() returns the singleton better-sqlite3 Database instance.
 * On first call it enables WAL mode, runs migrations, and recovers
 * any crashed jobs automatically.
 */
const db = getDb();

console.log("Database connection established. WAL mode active.");

// ============================================================================
// Example 2: Creating a new pipeline job
// ============================================================================

/**
 * Insert a new job into the `jobs` table.
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

function completeJob(jobId: string): void {
  const db = getDb();
  const now = new Date().toISOString();

  db.prepare(
    `UPDATE jobs SET status='done', progress=100, updatedAt=? WHERE id=?`
  ).run(now, jobId);

  console.log(`Job ${jobId} completed successfully.`);
}

// Simulate a job lifecycle
updateJobProgress(jobId, 25);
updateJobProgress(jobId, 50);
updateJobProgress(jobId, 75);
completeJob(jobId);

// ============================================================================
// Example 4: Querying jobs by stage
// ============================================================================

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
  const params =
    typeof job.params === "string" ? JSON.parse(job.params) : job.params;
  console.log(`  Job ${job.id}: status=${job.status}, params=`, params);
}

// ============================================================================
// Example 5: Creating and querying annotations
// ============================================================================

function createAnnotation(
  jobId: string,
  sectionId: string,
  timestamp: number,
  text: string,
  videoFile: string | null = null
): string {
  const db = getDb();
  const id = randomUUID();
  const now = new Date().toISOString();

  db.prepare(
    `INSERT INTO annotations (id, sectionId, timestamp, text, videoFile, createdAt)
     VALUES (?, ?, ?, ?, ?, ?)`
  ).run(id, sectionId, timestamp, text, videoFile, now);

  console.log(`Created annotation ${id} on section "${sectionId}" at ${timestamp}s`);
  return id;
}

function setAnnotationAnalysis(
  annotationId: string,
  analysisResult: string
): void {
  const db = getDb();

  db.prepare(`UPDATE annotations SET analysis = ? WHERE id = ?`).run(
    analysisResult,
    annotationId
  );

  console.log(`Set analysis on annotation ${annotationId}`);
}

function getAnnotationsBySection(
  sectionId: string
): Array<Record<string, unknown>> {
  const db = getDb();

  return db
    .prepare(
      `SELECT * FROM annotations WHERE sectionId = ? ORDER BY timestamp ASC`
    )
    .all(sectionId) as Array<Record<string, unknown>>;
}

const annId = createAnnotation(
  jobId,
  "intro",
  3.2,
  "Text is cut off on the right side",
  "output/sections/intro.mp4"
);

setAnnotationAnalysis(annId, JSON.stringify({
  severity: "major",
  fixType: "remotion",
  technicalAssessment:
    "Text overlay at 3.2s is clipped by the safe-zone boundary.",
  suggestedFixes: ["Reduce font size from 48px to 40px"],
  confidence: 0.87,
}));

const sectionAnnotations = getAnnotationsBySection("intro");
console.log(`Annotations for section "intro":`, sectionAnnotations.length);

// ============================================================================
// Example 6: Managing pipeline_status
// ============================================================================

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

  console.log(`Pipeline status: stage="${stage}" -> ${status}`);
}

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
// Example 7: Recording job costs
// ============================================================================

function recordJobCost(
  jobId: string,
  stage: string,
  provider: string,
  model: string,
  inputTokens: number,
  outputTokens: number,
  cost: number
): void {
  const db = getDb();
  const id = randomUUID();
  const now = new Date().toISOString();

  db.prepare(
    `INSERT INTO job_costs (id, jobId, stage, provider, model, inputTokens, outputTokens, cost, createdAt)
     VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)`
  ).run(id, jobId, stage, provider, model, inputTokens, outputTokens, cost, now);

  console.log(`Recorded cost for job ${jobId}: ${provider}/${model} = $${cost}`);
}

recordJobCost(jobId, "tts-render", "google", "tts-neural2", 0, 0, 0.015);
recordJobCost(jobId, "tts-render", "anthropic", "claude-3-opus", 1200, 350, 0.042);

const totalCost = (db.prepare(
  `SELECT SUM(cost) as total FROM job_costs WHERE jobId = ?`
).get(jobId) as any)?.total ?? 0;
console.log(`Total cost for job ${jobId}: $${totalCost}`);

// ============================================================================
// Example 8: Crash recovery demonstration
// ============================================================================

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

// ============================================================================
// Cleanup: Show final state of all tables
// ============================================================================

console.log("\n=== Final Database State ===");

const allJobs = db.prepare("SELECT id, stage, status, progress FROM jobs").all();
console.log("Jobs:", allJobs);

const allAnnotations = db
  .prepare("SELECT id, sectionId, videoFile, resolved FROM annotations")
  .all();
console.log("Annotations:", allAnnotations);

const allStatuses = db.prepare("SELECT * FROM pipeline_status").all();
console.log("Pipeline statuses:", allStatuses);

const allCosts = db.prepare("SELECT * FROM job_costs").all();
console.log("Job costs:", allCosts);

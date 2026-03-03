// example_usage.ts
// Comprehensive usage example for lib/jobs.ts
//
// This module is server-only and manages the full lifecycle of pipeline jobs:
//   - Creating jobs in SQLite
//   - Running jobs with executor functions that stream logs via SSE
//   - DAG-based pipeline orchestration (auto-running prerequisites)
//   - Retry support with executor registry
//
// IMPORTANT: This module can only be used in server-side contexts (Route Handlers,
// Server Actions, Server Components) due to the 'server-only' guard.

// Set up in-memory DB for demonstration
process.env.DB_PATH = ':memory:';

import {
  createJob,
  getJob,
  runJob,
  retryJob,
  runPipelineStage,
  registerExecutor,
  PIPELINE_DAG,
  type ExecutorFactory,
} from '../lib/jobs';
import type { PipelineStage, SseSend } from '../lib/types';

// ============================================================================
// Example 1: Understanding the Pipeline DAG
// ============================================================================

/**
 * PIPELINE_DAG defines the dependency graph for the 10-stage video pipeline.
 * Each key is a stage, and its value is an array of prerequisite stages
 * that must complete before it can run.
 *
 * The DAG structure:
 *
 *   setup
 *     └─ script
 *         ├─ tts-script → tts-render → audio-sync ─┐
 *         └─ specs → veo ──────────────────────────┤
 *                                                   └─ compositions → render → audit
 *
 * Audio track (tts-script → tts-render → audio-sync) and visual track
 * (specs → veo) run in parallel after 'script' completes.
 */

console.log('=== Pipeline DAG ===');
for (const [stage, deps] of Object.entries(PIPELINE_DAG)) {
  console.log(`  ${stage}: depends on [${deps.join(', ') || 'nothing'}]`);
}
// Output:
//   setup: depends on [nothing]
//   script: depends on [setup]
//   tts-script: depends on [script]
//   tts-render: depends on [tts-script]
//   audio-sync: depends on [tts-render]
//   specs: depends on [script]
//   veo: depends on [specs]
//   compositions: depends on [audio-sync, veo]
//   render: depends on [compositions]
//   audit: depends on [render]

// ============================================================================
// Example 2: Registering Executor Factories
// ============================================================================

/**
 * registerExecutor(stage, factory) registers an ExecutorFactory for a pipeline stage.
 *
 * An ExecutorFactory has the signature:
 *   (params: Record<string, unknown>, send: SseSend) =>
 *     (onLog: (msg: string) => void) => Promise<void>
 *
 * - `params`  — The job parameters (deserialized from the DB `params` JSON column).
 * - `send`    — The SSE send callback for streaming events to the client.
 * - Returns an executor function that accepts an `onLog` callback.
 *   - `onLog(msg)` writes log lines to the DB and emits SSE log events.
 *   - `(onLog as any).progress?.(percent)` emits progress updates (0–100).
 *
 * Executors are typically registered at module load time in API route files.
 */

// Register a mock executor for every stage so the examples work end-to-end
const ALL_STAGES: PipelineStage[] = [
  'setup',
  'script',
  'tts-script',
  'tts-render',
  'audio-sync',
  'specs',
  'veo',
  'compositions',
  'render',
  'audit',
];

for (const stage of ALL_STAGES) {
  const factory: ExecutorFactory = (params, _send) => {
    // The factory returns the actual executor function
    return async (onLog) => {
      onLog(`[${stage}] Starting with params: ${JSON.stringify(params)}`);

      // Simulate work with progress updates
      const progressFn = (onLog as unknown as { progress?: (p: number) => void })
        .progress;

      for (let i = 25; i <= 100; i += 25) {
        // Simulate async work
        await new Promise((resolve) => setTimeout(resolve, 10));
        progressFn?.(i);
        onLog(`[${stage}] Progress: ${i}%`);
      }

      onLog(`[${stage}] Completed successfully`);
    };
  };

  registerExecutor(stage, factory);
}

console.log('\nAll executor factories registered.');

// ============================================================================
// Example 3: Creating a Job with createJob()
// ============================================================================

/**
 * createJob(stage, params) inserts a new job record into the `jobs` table.
 *
 * @param stage  — The PipelineStage this job belongs to
 *                 (e.g. 'tts-render', 'veo', 'script')
 * @param params — Arbitrary parameters stored as JSON in the DB.
 *                 These are passed back to the executor factory on run/retry.
 * @returns      — The generated job ID (UUID v4 string)
 *
 * The job is created with:
 *   status: 'pending'
 *   progress: 0
 *   error: null
 *   logs: '' (empty string)
 */

const jobId = createJob('tts-render', {
  sectionId: 'intro',
  voice: 'en-US-Neural2-F',
  rate: 1.0,
});

console.log(`\n=== Created Job ===`);
console.log(`Job ID: ${jobId}`);

// ============================================================================
// Example 4: Inspecting a Job with getJob()
// ============================================================================

/**
 * getJob(jobId) retrieves a job from the database by its ID.
 *
 * @param jobId — The UUID of the job to retrieve
 * @returns     — A Job object if found, or undefined if not found.
 *
 * The returned Job object has these fields:
 *   id:        string                    — UUID
 *   stage:     PipelineStage             — e.g. 'tts-render'
 *   status:    JobStatus                 — 'pending' | 'running' | 'done' | 'error'
 *   progress:  number                    — 0–100
 *   error:     string | null             — error message or null
 *   params:    Record<string, unknown>   — deserialized from JSON
 *   createdAt: string                    — ISO 8601 timestamp
 *   updatedAt: string                    — ISO 8601 timestamp
 */

const job = getJob(jobId);
if (job) {
  console.log(`\n=== Job Details ===`);
  console.log(`  ID:       ${job.id}`);
  console.log(`  Stage:    ${job.stage}`);
  console.log(`  Status:   ${job.status}`);
  console.log(`  Progress: ${job.progress}%`);
  console.log(`  Error:    ${job.error}`);
  console.log(`  Params:   ${JSON.stringify(job.params)}`);
  console.log(`  Created:  ${job.createdAt}`);
}

// Non-existent job returns undefined
const missing = getJob('non-existent-id');
console.log(`\nMissing job lookup: ${missing}`); // undefined

// ============================================================================
// Example 5: Running a Job with runJob()
// ============================================================================

/**
 * runJob(jobId, executor) executes a job and manages its lifecycle in the DB.
 *
 * @param jobId    — The UUID of an existing job (must be in the `jobs` table)
 * @param executor — An async function with signature:
 *                   (onLog: (msg: string) => void) => Promise<void>
 *
 * Lifecycle:
 *   1. Sets job status to 'running' in DB
 *   2. Updates pipeline_status for the job's stage to 'running'
 *   3. Calls executor(onLog)
 *      - onLog(msg) appends log lines to the job's `logs` column
 *        and emits SSE events: { type: 'log', message, jobId }
 *      - (onLog as any).progress(percent) updates progress in DB
 *        and emits SSE events: { type: 'progress', percent, jobId }
 *   4. On success: sets status='done', progress=100
 *   5. On error: sets status='error', stores error message
 *   6. Updates pipeline_status accordingly
 *
 * Note: SSE events are only emitted if a send function was registered
 * for this jobId via runPipelineStage(). Direct runJob() calls use a
 * no-op sender unless you register one via the internal JOB_SEND_MAP.
 */

async function example5_runJob(): Promise<void> {
  console.log('\n=== Example 5: Running a Job ===');

  const myJobId = createJob('script', { topic: 'Product Launch' });

  // Define an executor inline
  const executor = async (onLog: (msg: string) => void): Promise<void> => {
    onLog('Generating script outline...');

    // Access the progress callback attached to onLog
    const progressFn = (onLog as unknown as { progress?: (p: number) => void })
      .progress;

    progressFn?.(25);
    onLog('Outline complete. Writing sections...');

    progressFn?.(50);
    onLog('Sections drafted. Polishing...');

    progressFn?.(75);
    onLog('Script finalized.');

    progressFn?.(100);
  };

  await runJob(myJobId, executor);

  const completedJob = getJob(myJobId);
  console.log(`  Status after run: ${completedJob?.status}`);   // 'done'
  console.log(`  Progress: ${completedJob?.progress}%`);         // 100
}

// ============================================================================
// Example 6: Handling Job Errors
// ============================================================================

/**
 * When an executor throws an error, runJob catches it and:
 *   - Sets job status to 'error'
 *   - Stores the error message in the `error` column
 *   - Updates pipeline_status to 'error' for the stage
 *
 * The error does NOT propagate to the caller of runJob().
 */

async function example6_errorHandling(): Promise<void> {
  console.log('\n=== Example 6: Error Handling ===');

  const failJobId = createJob('veo', { sectionId: 'intro' });

  const failingExecutor = async (onLog: (msg: string) => void): Promise<void> => {
    onLog('Starting video generation...');
    onLog('Contacting Veo API...');
    throw new Error('Veo API rate limit exceeded');
  };

  try {
    await runJob(failJobId, failingExecutor);
  } catch {
    // Expected — runJob re-throws executor errors after recording them in DB
  }

  const failedJob = getJob(failJobId);
  console.log(`  Status: ${failedJob?.status}`);   // 'error'
  console.log(`  Error:  ${failedJob?.error}`);     // 'Veo API rate limit exceeded'
  console.log(`  Progress: ${failedJob?.progress}%`); // stays at 0 (or wherever it was)
}

// ============================================================================
// Example 7: Retrying a Failed Job with retryJob()
// ============================================================================

/**
 * retryJob(jobId) resets a job to 'pending' and re-runs it using the
 * executor factory registered for the job's stage.
 *
 * @param jobId — The UUID of the job to retry
 * @throws      — If the job is not found or no executor is registered
 *
 * How it works:
 *   1. Reads the job's stage and params from the DB
 *   2. Resets status to 'pending', progress to 0, error to null
 *   3. Looks up the ExecutorFactory registered for the stage
 *   4. Creates a new executor from the factory using stored params
 *   5. Calls runJob(jobId, executor) to re-execute
 *
 * IMPORTANT: You must have called registerExecutor(stage, factory) for the
 * job's stage before calling retryJob(), otherwise it throws.
 */

async function example7_retryJob(): Promise<void> {
  console.log('\n=== Example 7: Retrying a Job ===');

  // Create and fail a job
  const retryJobId = createJob('specs', { sectionId: 'main' });

  // First run: simulate failure
  let attemptCount = 0;

  // Re-register specs executor that fails on first attempt
  registerExecutor('specs', (params, _send) => {
    return async (onLog) => {
      attemptCount++;
      onLog(`Attempt #${attemptCount}`);
      if (attemptCount === 1) {
        throw new Error('Transient network error');
      }
      onLog('Specs generated successfully on retry');
    };
  });

  try {
    await runJob(retryJobId, (onLog) => {
      attemptCount++;
      onLog(`Attempt #${attemptCount}`);
      throw new Error('Transient network error');
    });
  } catch {
    // Expected — runJob re-throws executor errors after recording them in DB
  }

  const afterFail = getJob(retryJobId);
  console.log(`  After first run: status=${afterFail?.status}, error=${afterFail?.error}`);

  // Retry — the registered executor checks attemptCount and only
  // throws on the first attempt, so the second attempt succeeds.
  await retryJob(retryJobId);

  const afterRetry = getJob(retryJobId);
  console.log(`  After retry: status=${afterRetry?.status}, error=${afterRetry?.error}`);

  // Re-register the normal mock executor for specs
  registerExecutor('specs', (params, _send) => {
    return async (onLog) => {
      onLog(`[specs] Running with params: ${JSON.stringify(params)}`);
      const progressFn = (onLog as unknown as { progress?: (p: number) => void }).progress;
      progressFn?.(100);
      onLog('[specs] Done');
    };
  });
}

// ============================================================================
// Example 8: Full DAG Orchestration with runPipelineStage()
// ============================================================================

/**
 * runPipelineStage(stage, params, send) is the main orchestration entry point.
 * It automatically runs all prerequisite stages (per the DAG) before running
 * the requested stage.
 *
 * @param stage  — The target PipelineStage to run
 * @param params — Parameters passed to ALL executor factories (upstream and target)
 * @param send   — SSE send callback for streaming events to the client.
 *                 All upstream and downstream log/progress events flow through
 *                 this single send function.
 * @returns      — The job ID of the target stage's job
 *
 * Orchestration behavior:
 *   1. Walks the DAG recursively from the target stage
 *   2. For each prerequisite stage:
 *      - If pipeline_status shows 'done', skips it (uses cached result)
 *      - Otherwise, creates a new job and runs it
 *   3. Parallel prerequisites run concurrently via Promise.all
 *      (e.g., audio track and visual track run in parallel)
 *   4. The target stage is always force-run (even if previously 'done')
 *   5. Returns the job ID of the target stage
 *
 * Example: Running 'compositions' will auto-run:
 *   setup → script → (tts-script → tts-render → audio-sync) ∥ (specs → veo)
 *   Then run compositions itself.
 */

async function example8_pipelineOrchestration(): Promise<void> {
  console.log('\n=== Example 8: Pipeline Orchestration ===');

  // Create a mock SSE send function that logs events
  const sseEvents: object[] = [];
  const mockSend: SseSend = (data: object) => {
    sseEvents.push(data);
    const d = data as Record<string, unknown>;
    if (d.type === 'log') {
      console.log(`  SSE log: ${d.message}`);
    } else if (d.type === 'progress') {
      console.log(`  SSE progress: ${d.percent}% (job: ${d.jobId})`);
    }
  };

  // Run 'compositions' — this will auto-run all upstream stages:
  //   setup → script → tts-script → tts-render → audio-sync (audio track)
  //   setup → script → specs → veo (visual track, parallel with audio)
  //   Then: compositions
  const compositionsJobId = await runPipelineStage(
    'compositions',
    {
      projectName: 'Product Launch Video',
      voice: 'en-US-Neural2-F',
      veoModel: 'veo-2.0-generate-001',
    },
    mockSend
  );

  console.log(`\n  Compositions job ID: ${compositionsJobId}`);
  console.log(`  Total SSE events emitted: ${sseEvents.length}`);

  const compositionsJob = getJob(compositionsJobId);
  console.log(`  Compositions status: ${compositionsJob?.status}`);
}

// ============================================================================
// Example 9: Running a Single Stage (with prerequisites already done)
// ============================================================================

/**
 * If upstream stages are already 'done' in pipeline_status, they are skipped.
 * Only the target stage is executed.
 */

async function example9_singleStage(): Promise<void> {
  console.log('\n=== Example 9: Single Stage (deps already done) ===');

  const events: object[] = [];
  const send: SseSend = (data: object) => {
    events.push(data);
  };

  // After Example 8, all stages up to 'compositions' are 'done'.
  // Running 'render' should only execute 'render' itself (compositions is done).
  const renderJobId = await runPipelineStage(
    'render',
    { fps: 30, width: 1920, height: 1080 },
    send
  );

  const renderJob = getJob(renderJobId);
  console.log(`  Render job status: ${renderJob?.status}`);
  console.log(`  SSE events for render only: ${events.length}`);
}

// ============================================================================
// Example 10: Using in a Next.js API Route Handler (pattern)
// ============================================================================

/**
 * In a real Next.js app, you'd use these functions in Route Handlers like this:
 *
 * ```typescript
 * // app/api/pipeline/[stage]/route.ts
 * import { createSseStream } from '@/lib/sse';
 * import { runPipelineStage, registerExecutor } from '@/lib/jobs';
 * import type { PipelineStage } from '@/lib/types';
 *
 * // Register executor at module load time
 * registerExecutor('script', (params, send) => {
 *   return async (onLog) => {
 *     const progress = (onLog as any).progress;
 *     onLog('Calling Claude to generate script...');
 *     progress?.(10);
 *
 *     // ... actual Claude API call ...
 *     const result = await generateScript(params);
 *
 *     onLog(`Script generated: ${result.sections.length} sections`);
 *     progress?.(100);
 *   };
 * });
 *
 * export async function POST(
 *   request: Request,
 *   { params }: { params: { stage: string } }
 * ) {
 *   const stage = params.stage as PipelineStage;
 *   const body = await request.json();
 *   const { stream, send, done, error } = createSseStream();
 *
 *   // Fire-and-forget: run pipeline in background, stream results via SSE
 *   (async () => {
 *     try {
 *       const jobId = await runPipelineStage(stage, body, send);
 *       send({ type: 'complete', jobId });
 *       done();
 *     } catch (err) {
 *       error(err instanceof Error ? err.message : 'Unknown error');
 *     }
 *   })();
 *
 *   return new Response(stream, {
 *     headers: {
 *       'Content-Type': 'text/event-stream',
 *       'Cache-Control': 'no-cache',
 *       Connection: 'keep-alive',
 *     },
 *   });
 * }
 * ```
 *
 * // app/api/jobs/[jobId]/retry/route.ts
 * ```typescript
 * import { retryJob, getJob } from '@/lib/jobs';
 * import { NextResponse } from 'next/server';
 *
 * export async function POST(
 *   _request: Request,
 *   { params }: { params: { jobId: string } }
 * ) {
 *   const job = getJob(params.jobId);
 *   if (!job) {
 *     return NextResponse.json({ error: 'Job not found' }, { status: 404 });
 *   }
 *   if (job.status !== 'error') {
 *     return NextResponse.json(
 *       { error: 'Only failed jobs can be retried' },
 *       { status: 400 }
 *     );
 *   }
 *
 *   await retryJob(params.jobId);
 *   const updated = getJob(params.jobId);
 *   return NextResponse.json(updated);
 * }
 * ```
 */

console.log('\n=== Example 10: Next.js Route Handler Pattern ===');
console.log('  (See code comments for the full pattern)');

// ============================================================================
// Example 11: Custom Executor with Detailed Logging and Progress
// ============================================================================

/**
 * Demonstrates writing a realistic executor factory that uses both
 * onLog() for log messages and onLog.progress() for progress updates.
 */

async function example11_detailedExecutor(): Promise<void> {
  console.log('\n=== Example 11: Detailed Executor ===');

  // Register a more realistic executor for 'tts-render'
  registerExecutor('tts-render', (params, _send) => {
    return async (onLog) => {
      const voice = (params.voice as string) ?? 'default';
      const sectionId = (params.sectionId as string) ?? 'unknown';
      const progressFn = (onLog as unknown as { progress?: (p: number) => void })
        .progress;

      onLog(`TTS Render starting for section "${sectionId}" with voice "${voice}"`);
      progressFn?.(0);

      // Simulate multi-step TTS rendering
      const steps = [
        'Tokenizing script text',
        'Generating phoneme sequence',
        'Synthesizing audio waveform',
        'Applying prosody adjustments',
        'Encoding to MP3',
      ];

      for (let i = 0; i < steps.length; i++) {
        await new Promise((resolve) => setTimeout(resolve, 5));
        const percent = Math.round(((i + 1) / steps.length) * 100);
        onLog(`  Step ${i + 1}/${steps.length}: ${steps[i]}`);
        progressFn?.(percent);
      }

      onLog(`TTS Render complete. Output: output/tts/${sectionId}.mp3`);
    };
  });

  // Create and run the job
  const ttsJobId = createJob('tts-render', {
    sectionId: 'intro',
    voice: 'en-US-Neural2-F',
  });

  // Use the registered executor
  const factory = (await import('../lib/jobs')).default;
  // Since we can't access EXECUTORS directly, we'll use runPipelineStage
  // or manually create the executor from the factory pattern

  // For direct runJob usage, create the executor manually:
  const executor = async (onLog: (msg: string) => void): Promise<void> => {
    const progressFn = (onLog as unknown as { progress?: (p: number) => void })
      .progress;

    onLog('TTS Render starting for section "intro"');
    progressFn?.(25);
    onLog('  Synthesizing audio...');
    progressFn?.(50);
    onLog('  Encoding to MP3...');
    progressFn?.(75);
    onLog('  Finalizing...');
    progressFn?.(100);
    onLog('TTS Render complete.');
  };

  await runJob(ttsJobId, executor);

  const result = getJob(ttsJobId);
  console.log(`  Job ${result?.id}: status=${result?.status}, progress=${result?.progress}%`);
}

// ============================================================================
// Run all async examples
// ============================================================================

async function main(): Promise<void> {
  await example5_runJob();
  await example6_errorHandling();
  await example7_retryJob();
  await example8_pipelineOrchestration();
  await example9_singleStage();
  await example11_detailedExecutor();

  console.log('\n=== All examples completed successfully ===');
}

main().catch(console.error);
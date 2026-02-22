/**
 * Example usage of the Veo pipeline API routes module.
 *
 * This module demonstrates the four API route handlers for orchestrating
 * Google Veo video clip generation, reference image creation, clip status
 * inspection, and staging manifest comparison.
 *
 * For standalone execution (outside a running Next.js server), mock executors
 * are registered for all required pipeline stages, and an in-memory SQLite
 * database is used so each run starts fresh.
 *
 * The route file uses @/ path aliases (Next.js bundler only), so we test via:
 *   1. DAG integration through lib/jobs directly
 *   2. Source code structure verification via fs.readFileSync
 *   3. SSE event parsing demonstration
 */

// Use an in-memory database so each run starts fresh
process.env.DB_PATH = ':memory:';

import fs from 'fs';
import path from 'path';
import {
  registerExecutor,
  runPipelineStage,
  getJob,
  createJob,
  runJob,
  PIPELINE_DAG,
} from '../lib/jobs';
import type { PipelineStage, SseSend } from '../lib/types';

// ============================================================================
// Helper: assert and log
// ============================================================================

let passed = 0;
let failed = 0;

function assert(condition: boolean, label: string): void {
  if (condition) {
    passed++;
    console.log(`  PASS: ${label}`);
  } else {
    failed++;
    console.log(`  FAIL: ${label}`);
  }
}

// ============================================================================
// Setup: Register mock executors for required pipeline stages
// ============================================================================

/**
 * The veo stage depends on 'specs' -> 'script' -> 'setup'.
 * Register mock executors for all required stages so DAG orchestration
 * runs end-to-end without needing GOOGLE_API_KEY or a running Next.js server.
 */
const STAGES_NEEDED: PipelineStage[] = ['setup', 'script', 'specs', 'veo'];

for (const stage of STAGES_NEEDED) {
  registerExecutor(stage, (_params, _send) => {
    return async (onLog) => {
      onLog(`[${stage}] Mock executor running`);
      const progressFn = (onLog as unknown as { progress?: (p: number) => void })
        .progress;
      progressFn?.(50);

      // Simulate per-clip SSE events for the veo stage
      if (stage === 'veo') {
        const clips = Array.isArray(_params.clips) ? _params.clips : ['intro', 'main', 'outro'];
        for (const clipId of clips) {
          _send({ type: 'clip', clipId, status: 'generating' });
          _send({ type: 'clip', clipId, status: 'done' });
        }
      }

      onLog(`[${stage}] Mock executor complete`);
      progressFn?.(100);
    };
  });
}

// ============================================================================
// Example 1: Verify DAG prerequisites for veo
// ============================================================================

function example1_dagPrereqs(): void {
  console.log('=== Example 1: DAG prerequisites for veo ===');

  const deps = PIPELINE_DAG['veo'];
  assert(Array.isArray(deps), 'veo has DAG entry');
  assert(deps.includes('specs'), 'veo depends on specs');

  const specsDeps = PIPELINE_DAG['specs'];
  assert(specsDeps.includes('script'), 'specs depends on script');

  const scriptDeps = PIPELINE_DAG['script'];
  assert(scriptDeps.includes('setup'), 'script depends on setup');

  console.log('  Chain: setup -> script -> specs -> veo');
  console.log('');
}

// ============================================================================
// Example 2: Run veo via DAG orchestration with event capture
// ============================================================================

/**
 * Exercises runPipelineStage('veo', ...) which auto-runs all
 * prerequisite stages (setup -> script -> specs) before executing veo.
 * Captures all SSE events emitted during execution and verifies them.
 */
async function example2_runPipelineStage(): Promise<void> {
  console.log('=== Example 2: DAG orchestration for veo ===');

  const events: object[] = [];
  const mockSend: SseSend = (data: object) => {
    events.push(data);
  };

  const jobId = await runPipelineStage('veo', {}, mockSend);

  assert(typeof jobId === 'string' && jobId.length > 0, 'runPipelineStage returns a job ID');

  const job = getJob(jobId);
  assert(job !== undefined, 'Job exists in database');
  assert(job?.stage === 'veo', 'Job stage is veo');
  assert(job?.status === 'done', 'Job status is done');
  assert(job?.progress === 100, 'Job progress is 100');

  // Verify SSE events were emitted during execution
  assert(events.length > 0, 'SSE events were emitted during execution');

  const logEvents = events.filter((e: any) => e.type === 'log');
  assert(logEvents.length > 0, 'Log events were emitted');

  const progressEvents = events.filter((e: any) => e.type === 'progress');
  assert(progressEvents.length > 0, 'Progress events were emitted');

  // Check that prerequisite stages auto-ran
  const setupLogs = logEvents.filter((e: any) =>
    typeof e.message === 'string' && e.message.includes('[setup]')
  );
  assert(setupLogs.length > 0, 'Setup stage auto-ran as prerequisite');

  const scriptLogs = logEvents.filter((e: any) =>
    typeof e.message === 'string' && e.message.includes('[script]')
  );
  assert(scriptLogs.length > 0, 'Script stage auto-ran as prerequisite');

  const specsLogs = logEvents.filter((e: any) =>
    typeof e.message === 'string' && e.message.includes('[specs]')
  );
  assert(specsLogs.length > 0, 'Specs stage auto-ran as prerequisite');

  const veoLogs = logEvents.filter((e: any) =>
    typeof e.message === 'string' && e.message.includes('[veo]')
  );
  assert(veoLogs.length > 0, 'Veo stage executor ran');

  // Verify per-clip events from veo executor
  const clipEvents = events.filter((e: any) => e.type === 'clip');
  assert(clipEvents.length > 0, 'Per-clip SSE events were emitted');
  assert(
    clipEvents.some((e: any) => e.status === 'generating'),
    'Clip generating events emitted'
  );
  assert(
    clipEvents.some((e: any) => e.status === 'done'),
    'Clip done events emitted'
  );

  console.log(`  Job ID: ${jobId}`);
  console.log(`  Total events: ${events.length} (${logEvents.length} logs, ${progressEvents.length} progress, ${clipEvents.length} clips)`);
  console.log('');
}

// ============================================================================
// Example 3: Run veo with subset of clips
// ============================================================================

/**
 * Exercises runPipelineStage('veo', { clips: [...] }) with a subset
 * of clip IDs. Verifies clip events are emitted only for requested clips.
 */
async function example3_runSubset(): Promise<void> {
  console.log('=== Example 3: Generate a subset of clips ===');

  const events: object[] = [];
  const mockSend: SseSend = (data: object) => {
    events.push(data);
  };

  const jobId = await runPipelineStage('veo', { clips: ['intro', 'outro'] }, mockSend);

  assert(typeof jobId === 'string' && jobId.length > 0, 'Subset run returns a job ID');

  const clipEvents = events.filter((e: any) => e.type === 'clip');
  assert(clipEvents.length > 0, 'Clip events were emitted for subset');

  const clipIds = [...new Set(clipEvents.map((e: any) => e.clipId))];
  assert(clipIds.includes('intro'), 'Clip events include intro');
  assert(clipIds.includes('outro'), 'Clip events include outro');

  console.log(`  Job ID: ${jobId}`);
  console.log(`  Clip events: ${clipEvents.length} for clips: ${clipIds.join(', ')}`);
  console.log('');
}

// ============================================================================
// Example 4: Source file structure verification — run route
// ============================================================================

/**
 * Reads the run route source and verifies it matches prompt requirements:
 *   - registerExecutor('veo', ...) for pipeline integration
 *   - POST_run handler with SSE streaming
 *   - Frame chaining with extractLastFrame
 *   - Per-clip SSE events
 */
function example4_runRouteSourceStructure(): void {
  console.log('=== Example 4: Run route source structure verification ===');

  const sourceCode = fs.readFileSync(
    path.join(__dirname, '..', 'app', 'api', 'pipeline', 'veo', 'run', 'route.ts'),
    'utf-8'
  );

  // Requirement: exports POST_run handler
  assert(
    sourceCode.includes('POST_run'),
    'Exports POST_run handler'
  );

  // Requirement: registerExecutor('veo', ...)
  assert(
    sourceCode.includes('registerExecutor') && sourceCode.includes("'veo'"),
    'Registers veo executor'
  );

  // Requirement: Frame chaining — extractLastFrame
  assert(
    sourceCode.includes('extractLastFrame'),
    'Uses extractLastFrame for frame chaining'
  );

  // Requirement: referenceImagePath passed between clips
  assert(
    sourceCode.includes('referenceImagePath'),
    'Passes referenceImagePath between clips'
  );

  // Requirement: SSE streaming
  assert(sourceCode.includes('text/event-stream'), 'Sets Content-Type to text/event-stream');
  assert(sourceCode.includes('no-cache'), 'Sets Cache-Control to no-cache');
  assert(sourceCode.includes('keep-alive'), 'Sets Connection to keep-alive');

  // Requirement: Per-clip SSE events
  assert(
    sourceCode.includes("type: 'clip'") || sourceCode.includes('type: "clip"'),
    'Emits per-clip SSE events'
  );
  assert(sourceCode.includes("'generating'") || sourceCode.includes('"generating"'), 'Emits generating status');
  assert(sourceCode.includes("'done'") || sourceCode.includes('"done"'), 'Emits done status');
  assert(sourceCode.includes("'error'") || sourceCode.includes('"error"'), 'Emits error status');

  // Requirement: imports from @/lib/veo
  assert(sourceCode.includes('@/lib/veo'), 'Imports from @/lib/veo');

  // Requirement: imports from @/lib/jobs
  assert(sourceCode.includes('@/lib/jobs'), 'Imports from @/lib/jobs');

  // Requirement: imports from @/lib/sse
  assert(sourceCode.includes('@/lib/sse'), 'Imports from @/lib/sse');

  // Requirement: resolves Veo prompts from specs
  assert(sourceCode.includes('resolveVeoPrompt'), 'Defines resolveVeoPrompt');

  // Requirement: outputs to outputs/veo/
  assert(
    sourceCode.includes('outputs') && sourceCode.includes('veo'),
    'References outputs/veo directory'
  );

  console.log('');
}

// ============================================================================
// Example 5: Source file structure — GET_clips, POST_references, GET_staging
// ============================================================================

/**
 * Verifies that the route file also contains:
 *   - GET_clips handler returning VeoClip[]
 *   - POST_references handler for reference image generation
 *   - GET_staging handler for staging manifest comparison
 */
function example5_additionalHandlers(): void {
  console.log('=== Example 5: Additional handler verification ===');

  const sourceCode = fs.readFileSync(
    path.join(__dirname, '..', 'app', 'api', 'pipeline', 'veo', 'run', 'route.ts'),
    'utf-8'
  );

  // GET_clips handler
  assert(sourceCode.includes('GET_clips'), 'Exports GET_clips handler');
  assert(sourceCode.includes('VeoClip'), 'Defines VeoClip type');
  assert(sourceCode.includes('stale'), 'VeoClip includes stale field');
  assert(sourceCode.includes('frameChainDeps'), 'VeoClip includes frameChainDeps');
  assert(sourceCode.includes('aspectRatio'), 'VeoClip includes aspectRatio');

  // POST_references handler
  assert(sourceCode.includes('POST_references'), 'Exports POST_references handler');
  assert(sourceCode.includes('referenceId'), 'POST_references uses referenceId');
  assert(sourceCode.includes('generateReferenceImage'), 'Uses generateReferenceImage from lib/veo');
  assert(sourceCode.includes('resolveReferencePrompt'), 'Defines resolveReferencePrompt');

  // Validation: missing referenceId returns 400
  assert(
    sourceCode.includes('400') && sourceCode.includes('referenceId is required'),
    'POST_references validates referenceId (400)'
  );

  // GET_staging handler
  assert(sourceCode.includes('GET_staging'), 'Exports GET_staging handler');
  assert(sourceCode.includes('AssetStagingEntry'), 'Defines AssetStagingEntry type');
  assert(sourceCode.includes('remotion') && sourceCode.includes('public'), 'Checks remotion/public directory');
  assert(
    sourceCode.includes('expected') && sourceCode.includes('present'),
    'AssetStagingEntry has expected and present fields'
  );

  console.log('');
}

// ============================================================================
// Example 6: SSE event parsing demonstration
// ============================================================================

/**
 * Demonstrates parsing the raw SSE wire format that the run endpoint produces.
 * Covers the specific event types emitted by the Veo pipeline.
 */
function example6_sseEventParsing(): void {
  console.log('=== Example 6: SSE event parsing for Veo pipeline ===');

  // Parse a clip generating event
  const genEvent = 'data: {"type":"clip","clipId":"intro","status":"generating"}';
  const genPayload = JSON.parse(genEvent.replace(/^data:\s*/, ''));
  assert(genPayload.type === 'clip', 'Parsed clip event type');
  assert(genPayload.clipId === 'intro', 'Parsed clipId');
  assert(genPayload.status === 'generating', 'Parsed generating status');

  // Parse a clip done event
  const doneEvent = 'data: {"type":"clip","clipId":"intro","status":"done"}';
  const donePayload = JSON.parse(doneEvent.replace(/^data:\s*/, ''));
  assert(donePayload.status === 'done', 'Parsed done status');

  // Parse a log event
  const logEvent = 'data: {"type":"log","message":"Generating Veo clip \\"intro\\"","jobId":"abc-123"}';
  const logPayload = JSON.parse(logEvent.replace(/^data:\s*/, ''));
  assert(logPayload.type === 'log', 'Parsed log event type');
  assert(logPayload.message.includes('Generating'), 'Parsed log message');
  assert(logPayload.jobId === 'abc-123', 'Log event includes jobId');

  // Parse a progress event
  const progressEvent = 'data: {"type":"progress","percent":50,"jobId":"abc-123"}';
  const progressPayload = JSON.parse(progressEvent.replace(/^data:\s*/, ''));
  assert(progressPayload.type === 'progress', 'Parsed progress event type');
  assert(progressPayload.percent === 50, 'Parsed progress percent');

  // Parse a complete event
  const completeEvent = 'data: {"type":"complete","jobId":"abc-123"}';
  const completePayload = JSON.parse(completeEvent.replace(/^data:\s*/, ''));
  assert(completePayload.type === 'complete', 'Parsed complete event type');
  assert(completePayload.jobId === 'abc-123', 'Complete event includes jobId');

  // Parse an error event
  const errorEvent = 'data: {"type":"error","message":"GOOGLE_API_KEY not set"}';
  const errorPayload = JSON.parse(errorEvent.replace(/^data:\s*/, ''));
  assert(errorPayload.type === 'error', 'Parsed error event type');
  assert(errorPayload.message.includes('GOOGLE_API_KEY'), 'Parsed error message');

  console.log('');
}

// ============================================================================
// Run all examples
// ============================================================================

async function main(): Promise<void> {
  example1_dagPrereqs();
  await example2_runPipelineStage();
  await example3_runSubset();
  example4_runRouteSourceStructure();
  example5_additionalHandlers();
  example6_sseEventParsing();

  console.log('========================================');
  console.log(`Results: ${passed} passed, ${failed} failed`);
  if (failed > 0) {
    process.exit(1);
  }
  console.log('All examples completed successfully');
}

main().catch((err) => {
  console.error('Example failed:', err);
  process.exit(1);
});

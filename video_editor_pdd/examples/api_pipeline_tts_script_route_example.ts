// api_pipeline_tts_script_route_example.ts
//
// Comprehensive usage example for app/api/pipeline/tts-script/run/route.ts
//
// This file verifies the TTS script generation endpoint by:
//   1. Exercising the DAG orchestration (auto-runs prerequisite stages)
//   2. Testing the SSE stream response pattern used by the POST handler
//   3. Verifying the source file structure matches prompt requirements
//   4. Demonstrating SSE event parsing
//
// For standalone execution (outside a running Next.js server), mock executors
// are registered for all required pipeline stages, and an in-memory SQLite
// database is used so each run starts fresh.

// Use an in-memory database for this example so each run starts fresh
process.env.DB_PATH = ':memory:';

import fs from 'fs';
import path from 'path';
import { createSseStream } from '../lib/sse';
import {
  registerExecutor,
  runPipelineStage,
  getJob,
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
 * The tts-script stage depends on 'script', which depends on 'setup'.
 * Register mock executors for all three so the DAG orchestration can run
 * end-to-end without needing the Claude CLI or a running Next.js server.
 */
const STAGES_NEEDED: PipelineStage[] = ['setup', 'script', 'tts-script'];

for (const stage of STAGES_NEEDED) {
  registerExecutor(stage, (_params, _send) => {
    return async (onLog) => {
      onLog(`[${stage}] Mock executor running`);
      const progressFn = (onLog as unknown as { progress?: (p: number) => void })
        .progress;
      progressFn?.(50);
      onLog(`[${stage}] Mock executor complete`);
      progressFn?.(100);
    };
  });
}

// ============================================================================
// Example 1: Verify DAG prerequisites for tts-script
// ============================================================================

function example1_dagPrereqs(): void {
  console.log('=== Example 1: DAG prerequisites for tts-script ===');

  const deps = PIPELINE_DAG['tts-script'];
  assert(Array.isArray(deps), 'tts-script has DAG entry');
  assert(deps.includes('script'), 'tts-script depends on script');

  const scriptDeps = PIPELINE_DAG['script'];
  assert(scriptDeps.includes('setup'), 'script depends on setup');

  console.log(`  Chain: setup -> script -> tts-script`);
  console.log('');
}

// ============================================================================
// Example 2: Run tts-script via DAG orchestration with event capture
// ============================================================================

/**
 * Exercises runPipelineStage('tts-script', ...) which auto-runs all
 * prerequisite stages (setup -> script) before executing tts-script.
 * Captures all SSE events emitted during execution and verifies them.
 */
async function example2_runPipelineStage(): Promise<void> {
  console.log('=== Example 2: DAG orchestration for tts-script ===');

  const events: object[] = [];
  const mockSend: SseSend = (data: object) => {
    events.push(data);
  };

  const jobId = await runPipelineStage('tts-script', {}, mockSend);

  assert(typeof jobId === 'string' && jobId.length > 0, 'runPipelineStage returns a job ID');

  const job = getJob(jobId);
  assert(job !== undefined, 'Job exists in database');
  assert(job?.stage === 'tts-script', 'Job stage is tts-script');
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

  const ttsLogs = logEvents.filter((e: any) =>
    typeof e.message === 'string' && e.message.includes('[tts-script]')
  );
  assert(ttsLogs.length > 0, 'tts-script stage executor ran');

  console.log(`  Job ID: ${jobId}`);
  console.log(`  Total events: ${events.length} (${logEvents.length} logs, ${progressEvents.length} progress)`);
  console.log('');
}

// ============================================================================
// Example 3: POST handler SSE stream response pattern
// ============================================================================

/**
 * Recreates the exact POST handler pattern from route.ts:
 *   1. createSseStream() to get stream + send/done/error callbacks
 *   2. Fire-and-forget async execution of runPipelineStage
 *   3. Return Response(stream) with status 202 and SSE headers
 *   4. Read back and verify the SSE stream contents
 */
async function example3_postHandlerPattern(): Promise<void> {
  console.log('=== Example 3: POST handler SSE stream pattern ===');

  const { stream, send, done, error } = createSseStream();

  // Fire-and-forget execution (same pattern as route.ts POST handler)
  const execution = (async () => {
    try {
      const jobId = await runPipelineStage('tts-script', {}, send);
      send({ type: 'started', jobId });
      send({ type: 'complete', jobId });
      done();
    } catch (err) {
      const message = err instanceof Error ? err.message : 'Unknown error';
      error(message);
    }
  })();

  // Build Response (same as route.ts)
  const response = new Response(stream, {
    status: 202,
    headers: {
      'Content-Type': 'text/event-stream',
      'Cache-Control': 'no-cache',
      Connection: 'keep-alive',
    },
  });

  assert(response.status === 202, 'Response status is 202');
  assert(
    response.headers.get('Content-Type') === 'text/event-stream',
    'Content-Type is text/event-stream'
  );
  assert(
    response.headers.get('Cache-Control') === 'no-cache',
    'Cache-Control is no-cache'
  );

  // Wait for fire-and-forget to complete
  await execution;

  // Read back the SSE stream
  const reader = response.body!.getReader();
  const decoder = new TextDecoder();
  let body = '';

  while (true) {
    const { done: readerDone, value } = await reader.read();
    if (readerDone) break;
    body += decoder.decode(value, { stream: true });
  }
  body += decoder.decode(); // flush

  // Parse and verify SSE events
  const rawEvents = body.split('\n\n').filter(Boolean);
  assert(rawEvents.length > 0, 'Response body contains SSE events');

  const startedEvent = rawEvents.find(e => e.includes('"type":"started"'));
  assert(startedEvent !== undefined, 'Stream contains started event with jobId');

  const completeEvent = rawEvents.find(e => e.includes('"type":"complete"'));
  assert(completeEvent !== undefined, 'Stream contains complete event');

  const doneEvent = rawEvents.find(e => e.startsWith('event: done'));
  assert(doneEvent !== undefined, 'Stream ends with done event');

  console.log(`  SSE events in stream: ${rawEvents.length}`);
  console.log('');
}

// ============================================================================
// Example 4: Source file structure verification
// ============================================================================

/**
 * Reads the route.ts source and verifies it matches all prompt requirements:
 *   - Module-level TTS_SCRIPT_PROMPT constant
 *   - registerExecutor('tts-script', ...) with runClaudeFix
 *   - POST handler with SSE streaming
 *   - force-dynamic export
 *   - TTS annotation markers in the prompt
 */
function example4_sourceStructure(): void {
  console.log('=== Example 4: Source file structure verification ===');

  const sourceCode = fs.readFileSync(
    path.join(__dirname, '..', 'app', 'api', 'pipeline', 'tts-script', 'run', 'route.ts'),
    'utf-8'
  );

  // Requirement: export const dynamic = 'force-dynamic'
  assert(
    sourceCode.includes("dynamic = 'force-dynamic'") || sourceCode.includes('dynamic = "force-dynamic"'),
    'Has force-dynamic export'
  );

  // Requirement: export async function POST
  assert(
    /export\s+async\s+function\s+POST/.test(sourceCode),
    'Exports async POST handler'
  );

  // Requirement: TTS_SCRIPT_PROMPT module-level constant
  assert(sourceCode.includes('TTS_SCRIPT_PROMPT'), 'Defines TTS_SCRIPT_PROMPT constant');

  // Requirement: registerExecutor('tts-script', ...)
  assert(
    sourceCode.includes('registerExecutor') && sourceCode.includes('tts-script'),
    'Registers tts-script executor'
  );

  // Requirement: runClaudeFix in executor
  assert(sourceCode.includes('runClaudeFix'), 'Uses runClaudeFix in executor');

  // Requirement: Scope to narrative/ directory
  assert(sourceCode.includes('narrative'), 'Scopes executor to narrative/ directory');

  // Requirement: createSseStream for SSE
  assert(sourceCode.includes('createSseStream'), 'Uses createSseStream for SSE streaming');

  // Requirement: runPipelineStage for DAG orchestration
  assert(sourceCode.includes('runPipelineStage'), 'Uses runPipelineStage for DAG orchestration');

  // Requirement: TTS annotation markers in the prompt
  assert(sourceCode.includes('TONE'), 'TTS prompt includes TONE annotation marker');
  assert(sourceCode.includes('PACE'), 'TTS prompt includes PACE annotation marker');
  assert(sourceCode.includes('PAUSE'), 'TTS prompt includes PAUSE annotation marker');
  assert(sourceCode.includes('EMOTION'), 'TTS prompt includes EMOTION annotation marker');

  // Requirement: Read main_script.md and write tts_script.md
  assert(sourceCode.includes('main_script.md'), 'TTS prompt references main_script.md input');
  assert(sourceCode.includes('tts_script.md'), 'TTS prompt references tts_script.md output');

  // Requirement: Extract NARRATOR blocks
  assert(sourceCode.includes('NARRATOR'), 'TTS prompt mentions NARRATOR block extraction');

  // Requirement: Status 202
  assert(sourceCode.includes('202'), 'Returns 202 status code');

  // Requirement: text/event-stream Content-Type
  assert(sourceCode.includes('text/event-stream'), 'Sets Content-Type to text/event-stream');

  // Imports check
  assert(sourceCode.includes('lib/sse'), 'Imports from lib/sse');
  assert(sourceCode.includes('lib/jobs'), 'Imports from lib/jobs');
  assert(sourceCode.includes('lib/claude'), 'Imports from lib/claude');

  console.log('');
}

// ============================================================================
// Example 5: SSE event parsing demonstration
// ============================================================================

/**
 * Demonstrates parsing the raw SSE wire format that the endpoint produces.
 * Covers data events, named error events, and the done sentinel.
 */
function example5_sseParser(): void {
  console.log('=== Example 5: SSE event parsing ===');

  // Parse a standard data event
  const dataEvent = 'data: {"type":"started","jobId":"job-abc-123"}';
  const dataPayload = JSON.parse(dataEvent.replace(/^data:\s*/, ''));
  assert(dataPayload.type === 'started', 'Parsed started event type');
  assert(dataPayload.jobId === 'job-abc-123', 'Parsed jobId from started event');

  // Parse a log event
  const logEvent = 'data: {"type":"log","message":"[tts-script] Generating...","jobId":"job-456"}';
  const logPayload = JSON.parse(logEvent.replace(/^data:\s*/, ''));
  assert(logPayload.type === 'log', 'Parsed log event type');
  assert(logPayload.message.includes('[tts-script]'), 'Parsed log message');

  // Parse a named error event (event: error\ndata: {...})
  const errorEvent = 'event: error\ndata: {"message":"Claude CLI not found"}';
  const errorLines = errorEvent.split('\n');
  const eventType = errorLines[0].replace(/^event:\s*/, '');
  const errorData = JSON.parse(errorLines[1].replace(/^data:\s*/, ''));
  assert(eventType === 'error', 'Parsed error event name');
  assert(errorData.message === 'Claude CLI not found', 'Parsed error message');

  // Parse a done event
  const doneEventStr = 'event: done\ndata: {}';
  const doneLines = doneEventStr.split('\n');
  const doneType = doneLines[0].replace(/^event:\s*/, '');
  assert(doneType === 'done', 'Parsed done event name');

  console.log('');
}

// ============================================================================
// Run all examples
// ============================================================================

async function main(): Promise<void> {
  example1_dagPrereqs();
  await example2_runPipelineStage();
  await example3_postHandlerPattern();
  example4_sourceStructure();
  example5_sseParser();

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

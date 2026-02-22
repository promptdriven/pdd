// example_usage.ts
// Comprehensive usage example for app/api/jobs/[id]/stream/route.ts
//
// This file verifies the SSE streaming route by:
//   1. Importing and calling the actual GET handler from route.ts
//   2. Consuming the ReadableStream response and parsing SSE events
//   3. Testing all three terminal scenarios: done, error, not-found
//   4. Verifying response headers match SSE requirements
//   5. Verifying source file structure matches prompt requirements
//
// For standalone execution, an in-memory SQLite database is used
// and the @/ module path alias is resolved at runtime.

// ---------------------------------------------------------------------------
// 0. Environment setup (must run before any module that calls getDb())
// ---------------------------------------------------------------------------
process.env.DB_PATH = ':memory:';

// Register @/ path alias so route.ts's `import { getJob } from "@/lib/jobs"`
// resolves correctly when running outside the Next.js bundler.
const Module = require('module');
const pathMod = require('path');
const projectRoot = pathMod.resolve(__dirname, '..');
const origResolve = Module._resolveFilename;
Module._resolveFilename = function (request: string, ...args: unknown[]) {
  if (request.startsWith('@/')) {
    return origResolve.call(this, pathMod.join(projectRoot, request.slice(2)), ...args);
  }
  return origResolve.call(this, request, ...args);
};

// ---------------------------------------------------------------------------
// 1. Imports (safe now that alias is registered)
// ---------------------------------------------------------------------------
import fs from 'fs';
import path from 'path';
import { createJob, getJob, runJob } from '../lib/jobs';

// Dynamic require of route module (must be after alias registration above)
const routeModule = require('../app/api/jobs/[id]/stream/route') as {
  GET: (request: Request, context: { params: { id: string } }) => Promise<Response>;
  dynamic: string;
};

// ---------------------------------------------------------------------------
// 2. Assertion helper
// ---------------------------------------------------------------------------
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

// ---------------------------------------------------------------------------
// 3. SSE stream consumer helper
// ---------------------------------------------------------------------------

interface SseEvent {
  eventType: string | null; // null for default "message" events
  data: string;
}

async function consumeSseStream(response: Response): Promise<SseEvent[]> {
  const reader = response.body!.getReader();
  const decoder = new TextDecoder();
  let buffer = '';
  const events: SseEvent[] = [];

  while (true) {
    const { done, value } = await reader.read();
    if (done) break;
    buffer += decoder.decode(value, { stream: true });
  }
  buffer += decoder.decode(); // flush

  // Parse SSE frames (separated by double newline)
  const frames = buffer.split('\n\n').filter(Boolean);
  for (const frame of frames) {
    const lines = frame.split('\n');
    let eventType: string | null = null;
    let data = '';
    for (const line of lines) {
      if (line.startsWith('event: ')) {
        eventType = line.slice(7);
      } else if (line.startsWith('data: ')) {
        data = line.slice(6);
      }
    }
    if (data || eventType) {
      events.push({ eventType, data });
    }
  }
  return events;
}

// ---------------------------------------------------------------------------
// Example 1: Completed job — GET returns all log lines + done event
// ---------------------------------------------------------------------------

async function example1_completedJob(): Promise<void> {
  console.log('=== Example 1: Completed job — log lines + done event ===');

  const jobId = createJob('tts-render', { sectionId: 'intro' });

  // Run the job to completion (populates logs and sets status=done)
  await runJob(jobId, async (onLog) => {
    onLog('[tts-render] Starting with params: {"sectionId":"intro"}');
    onLog('[tts-render] Progress: 25%');
    onLog('[tts-render] Synthesizing audio waveform...');
    onLog('[tts-render] Progress: 50%');
    onLog('[tts-render] Encoding to MP3...');
    onLog('[tts-render] Progress: 75%');
    onLog('[tts-render] Progress: 100%');
    onLog('[tts-render] Completed successfully');
  });

  // Verify job is done in DB
  const job = getJob(jobId);
  assert(job?.status === 'done', 'Job status is done after runJob');

  // Call the actual route handler
  const request = new Request('http://localhost/api/jobs/' + jobId + '/stream');
  const response = await routeModule.GET(request, { params: { id: jobId } });
  const events = await consumeSseStream(response);

  // Verify log events
  const logEvents = events.filter((e) => e.eventType === null && JSON.parse(e.data).type === 'log');
  assert(logEvents.length === 8, `8 log events emitted (got ${logEvents.length})`);

  // Verify progress events
  const progressEvents = events.filter((e) => e.eventType === null && JSON.parse(e.data).type === 'progress');
  assert(progressEvents.length >= 1, `At least one progress event emitted (got ${progressEvents.length})`);

  // Verify first log event format: data: {"type":"log","message":"..."}
  const firstLog = JSON.parse(logEvents[0].data);
  assert(firstLog.type === 'log', 'Log event has type="log"');
  assert(
    firstLog.message === '[tts-render] Starting with params: {"sectionId":"intro"}',
    'First log message matches'
  );

  // Verify terminal done event
  const doneEvents = events.filter((e) => e.eventType === 'done');
  assert(doneEvents.length === 1, 'One done event emitted');
  assert(doneEvents[0].data === '{}', 'Done event data is empty object');

  // Total events: 8 log + at least 1 progress + 1 done = at least 10
  assert(events.length >= 10, `Total SSE events: ${events.length} (expected at least 10)`);

  // Display SSE frames
  console.log('\n  SSE frames emitted by the server:');
  for (const event of events) {
    if (event.eventType) {
      console.log(`    event: ${event.eventType}`);
    }
    console.log(`    data: ${event.data}`);
    console.log('    ---');
  }
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 2: Job not found — error event on first poll
// ---------------------------------------------------------------------------

async function example2_jobNotFound(): Promise<void> {
  console.log('=== Example 2: Job not found — error event ===');

  const fakeId = 'non-existent-job-id';

  const request = new Request('http://localhost/api/jobs/' + fakeId + '/stream');
  const response = await routeModule.GET(request, { params: { id: fakeId } });
  const events = await consumeSseStream(response);

  // Should emit exactly one error event
  assert(events.length === 1, `One event emitted (got ${events.length})`);
  assert(events[0].eventType === 'error', 'Event type is error');

  const errorData = JSON.parse(events[0].data);
  assert(errorData.message === 'Job not found', 'Error message is "Job not found"');

  console.log(`  SSE: event: error`);
  console.log(`  SSE: data: ${events[0].data}`);
  console.log('  Stream closes immediately.');
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 3: Job execution failure — log lines + error event
// ---------------------------------------------------------------------------

async function example3_jobError(): Promise<void> {
  console.log('=== Example 3: Job execution failure — error event ===');

  const jobId = createJob('veo', { sectionId: 'intro' });

  // Run a failing executor
  await runJob(jobId, async (onLog) => {
    onLog('[veo] Starting video generation...');
    onLog('[veo] Contacting Veo API...');
    throw new Error('Veo API rate limit exceeded');
  });

  // Verify job is in error state
  const job = getJob(jobId);
  assert(job?.status === 'error', 'Job status is error after failed run');
  assert(job?.error === 'Veo API rate limit exceeded', 'Error message stored in DB');

  // Call the actual route handler
  const request = new Request('http://localhost/api/jobs/' + jobId + '/stream');
  const response = await routeModule.GET(request, { params: { id: jobId } });
  const events = await consumeSseStream(response);

  // Verify log events before error
  const logEvents = events.filter((e) => e.eventType === null && JSON.parse(e.data).type === 'log');
  assert(logEvents.length === 2, `2 log events emitted (got ${logEvents.length})`);

  // Verify terminal error event
  const errorEvents = events.filter((e) => e.eventType === 'error');
  assert(errorEvents.length === 1, 'One error event emitted');

  const errorData = JSON.parse(errorEvents[0].data);
  assert(
    errorData.message === 'Veo API rate limit exceeded',
    'Error event contains correct message'
  );

  console.log(`  SSE log events: ${logEvents.length}`);
  console.log(`  SSE error event: ${errorEvents[0].data}`);
  console.log('  Stream closes after error event.');
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 4: Response headers verification
// ---------------------------------------------------------------------------

async function example4_responseHeaders(): Promise<void> {
  console.log('=== Example 4: Response headers ===');

  const jobId = createJob('setup', {});
  await runJob(jobId, async (onLog) => {
    onLog('[setup] Done');
  });

  const request = new Request('http://localhost/api/jobs/' + jobId + '/stream');
  const response = await routeModule.GET(request, { params: { id: jobId } });

  // Consume the stream so it doesn't leak
  await consumeSseStream(response);

  assert(
    response.headers.get('Content-Type') === 'text/event-stream',
    'Content-Type is text/event-stream'
  );
  assert(
    response.headers.get('Cache-Control') === 'no-cache',
    'Cache-Control is no-cache'
  );
  assert(
    response.headers.get('Connection') === 'keep-alive',
    'Connection is keep-alive'
  );

  console.log(`  Content-Type: ${response.headers.get('Content-Type')}`);
  console.log(`  Cache-Control: ${response.headers.get('Cache-Control')}`);
  console.log(`  Connection: ${response.headers.get('Connection')}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 5: Exported constants verification
// ---------------------------------------------------------------------------

function example5_exports(): void {
  console.log('=== Example 5: Exported constants ===');

  assert(routeModule.dynamic === 'force-dynamic', 'dynamic export is "force-dynamic"');
  assert(typeof routeModule.GET === 'function', 'GET is an exported function');

  console.log(`  dynamic: ${routeModule.dynamic}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 6: Source file structure verification
// ---------------------------------------------------------------------------

function example6_sourceStructure(): void {
  console.log('=== Example 6: Source file structure verification ===');

  const sourceCode = fs.readFileSync(
    path.join(__dirname, '..', 'app', 'api', 'jobs', '[id]', 'stream', 'route.ts'),
    'utf-8'
  );

  // Requirement: GET handler
  assert(
    /export\s+async\s+function\s+GET/.test(sourceCode),
    'Exports async GET handler'
  );

  // Requirement: force-dynamic
  assert(
    sourceCode.includes('force-dynamic'),
    'Exports dynamic = "force-dynamic"'
  );

  // Requirement: Imports getJob from @/lib/jobs
  assert(
    sourceCode.includes('getJob') && sourceCode.includes('@/lib/jobs'),
    'Imports getJob from @/lib/jobs'
  );

  // Requirement: SSE mechanism (manual ReadableStream or createSseStream)
  assert(
    sourceCode.includes('ReadableStream') || sourceCode.includes('createSseStream'),
    'Uses ReadableStream or createSseStream for SSE'
  );

  // Requirement: setInterval polling at 200ms
  assert(
    sourceCode.includes('setInterval') && sourceCode.includes('200'),
    'Uses setInterval with 200ms polling'
  );

  // Requirement: lastLineIndex tracking
  assert(sourceCode.includes('lastLineIndex'), 'Tracks lastLineIndex for incremental log delivery');

  // Requirement: Split logs on newline
  assert(
    sourceCode.includes('.split'),
    'Splits job.logs on newline'
  );

  // Requirement: SSE data format for logs
  assert(
    sourceCode.includes('"log"'),
    'Sends log events with type:"log"'
  );

  // Requirement: done event
  assert(
    sourceCode.includes('done()') || sourceCode.includes('event: done'),
    'Sends done event'
  );

  // Requirement: error event
  assert(
    sourceCode.includes('error(') || sourceCode.includes('event: error'),
    'Sends error event'
  );

  // Requirement: SSE headers
  assert(sourceCode.includes('text/event-stream'), 'Sets Content-Type: text/event-stream');
  assert(sourceCode.includes('no-cache'), 'Sets Cache-Control: no-cache');
  assert(sourceCode.includes('keep-alive'), 'Sets Connection: keep-alive');

  // Requirement: Job not found handling
  assert(
    sourceCode.includes('Job not found'),
    'Handles job-not-found case with error message'
  );

  // Requirement: clearInterval on close (prevents DB polling leaks)
  assert(
    sourceCode.includes('clearInterval'),
    'Clears interval on stream close'
  );

  // Requirement: cancel() handler or onCancel callback for client disconnect cleanup
  assert(
    sourceCode.includes('cancel()') || sourceCode.includes('onCancel') || sourceCode.includes('createSseStream('),
    'Has mechanism for client disconnect cleanup'
  );


  // Requirement: Params destructuring
  assert(
    sourceCode.includes('params') && sourceCode.includes('id'),
    'Uses params.id from route context'
  );

  console.log('');
}

// ---------------------------------------------------------------------------
// Example 7: Client EventSource consumption pattern
// ---------------------------------------------------------------------------

function example7_clientPattern(): void {
  console.log('=== Example 7: Client EventSource pattern ===');

  console.log('  Browser usage:');
  console.log('    const es = new EventSource("/api/jobs/<id>/stream");');
  console.log('    es.onmessage = (e) => {');
  console.log('      const { type, message } = JSON.parse(e.data);');
  console.log('      if (type === "log") appendLog(message);');
  console.log('    };');
  console.log('    es.addEventListener("done", () => { setStatus("done"); es.close(); });');
  console.log('    es.addEventListener("error", (e) => { handleError(e); es.close(); });');
  console.log('');
}

// ---------------------------------------------------------------------------
// Run all examples
// ---------------------------------------------------------------------------

async function main(): Promise<void> {
  console.log('========================================');
  console.log('SSE Job Stream Route - Module Verification');
  console.log('========================================\n');

  await example1_completedJob();
  await example2_jobNotFound();
  await example3_jobError();
  await example4_responseHeaders();
  example5_exports();
  example6_sourceStructure();
  example7_clientPattern();

  console.log('========================================');
  console.log(`Results: ${passed} passed, ${failed} failed`);
  if (failed > 0) {
    process.exit(1);
  }
  console.log('All examples completed successfully');
  console.log('========================================');
}

main().catch((err) => {
  console.error('Example failed:', err);
  process.exit(1);
});

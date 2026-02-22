// example_usage.ts
// Comprehensive usage example for app/api/jobs/[id]/stream/route.ts
//
// This file exercises the SSE streaming route's core behavior by using
// the same getJob/createJob/runJob functions the real route handler uses.
// It creates jobs in an in-memory SQLite database, runs them (which
// appends log lines to job.logs), and demonstrates the polling + SSE
// emission logic identical to what route.ts does.

// Use in-memory database for standalone execution
process.env.DB_PATH = ':memory:';

import { createJob, getJob, runJob } from '../lib/jobs';

// ============================================================================
// Helper
// ============================================================================

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

// ============================================================================
// Example 1: SSE stream — polling getJob() for log lines and status
// ============================================================================

/**
 * Demonstrates the exact SSE polling logic from route.ts:
 *   1. Poll getJob(id) every 200ms
 *   2. Split job.logs on newline, send only NEW lines since lastLineIndex
 *   3. When job.status === 'done', send event: done and close
 *   4. When job.status === 'error', send event: error and close
 *
 * This mirrors the start(controller) callback in route.ts but collects
 * SSE frames into an array instead of enqueuing into a ReadableStream.
 */
async function example1_ssePollingWithGetJob(): Promise<void> {
  console.log('=== Example 1: SSE polling with getJob() ===\n');

  // Create a job in the database
  const jobId = createJob('tts-render', { sectionId: 'intro' });
  console.log(`Created job: ${jobId}`);

  // Executor that logs progressively with sleeps between each line
  const executor = async (onLog: (msg: string) => void): Promise<void> => {
    onLog(`[tts-render] Starting with params: {"sectionId":"intro"}`);
    await sleep(50);
    onLog('[tts-render] Progress: 25%');
    await sleep(50);
    onLog('[tts-render] Synthesizing audio waveform...');
    await sleep(50);
    onLog('[tts-render] Progress: 50%');
    await sleep(50);
    onLog('[tts-render] Encoding to MP3...');
    await sleep(50);
    onLog('[tts-render] Progress: 75%');
    await sleep(50);
    onLog('[tts-render] Progress: 100%');
    await sleep(50);
    onLog('[tts-render] Completed successfully');
  };

  // Collect SSE frames using the same polling logic as route.ts
  const sseFrames: string[] = [];
  let lastLineIndex = 0;
  let streamDone = false;

  // Start polling (mirrors route.ts setInterval(poll, 200))
  const pollInterval = setInterval(() => {
    if (streamDone) return;

    const job = getJob(jobId);
    if (!job) return;

    // Split logs and send only new lines (mirrors route.ts logic)
    const lines = job.logs ? job.logs.split('\n') : [];
    // Exclude trailing empty string from final \n
    const lineCount =
      lines.length > 0 && lines[lines.length - 1] === ''
        ? lines.length - 1
        : lines.length;
    if (lineCount > lastLineIndex) {
      for (let i = lastLineIndex; i < lineCount; i++) {
        if (lines[i]) {
          sseFrames.push(`data: ${JSON.stringify({ type: 'log', message: lines[i] })}\n\n`);
        }
      }
      lastLineIndex = lineCount;
    }

    // Check terminal status (mirrors route.ts)
    if (job.status === 'done') {
      sseFrames.push('event: done\ndata: {}\n\n');
      streamDone = true;
      clearInterval(pollInterval);
    } else if (job.status === 'error') {
      sseFrames.push(`event: error\ndata: ${JSON.stringify({ message: job.error ?? 'Unknown error' })}\n\n`);
      streamDone = true;
      clearInterval(pollInterval);
    }
  }, 200);

  // Run the job concurrently — appends logs to DB via safeAppendLog
  await runJob(jobId, executor);

  // Wait for polling to pick up final status
  await sleep(500);
  clearInterval(pollInterval);

  // Verify getJob returns logs from the database
  const finalJob = getJob(jobId);
  console.log(`Job final status: ${finalJob?.status}`);
  console.log(`Job has logs: ${(finalJob?.logs?.length ?? 0) > 0}`);

  // Display SSE frames
  console.log('\nSSE frames emitted by the server:\n');
  for (const frame of sseFrames) {
    console.log(frame.replace(/\n/g, '\\n').replace(/\\n\\n$/, ''));
    console.log('---');
  }

  console.log(`\nTotal SSE frames: ${sseFrames.length}`);
  const logFrames = sseFrames.filter((f) => f.startsWith('data:'));
  const terminalFrames = sseFrames.filter((f) => f.startsWith('event:'));
  console.log(`  Log frames: ${logFrames.length}`);
  console.log(`  Terminal frame: ${terminalFrames.length} (done)`);
}

// ============================================================================
// Example 2: Job not found — error event on first poll
// ============================================================================

/**
 * When getJob(id) returns undefined on the first poll, route.ts sends:
 *   event: error\ndata: {"message":"Job not found"}\n\n
 * and closes the stream immediately.
 */
function example2_jobNotFound(): void {
  console.log('\n=== Example 2: Job not found ===\n');

  const fakeId = 'non-existent-job-id';
  const job = getJob(fakeId);

  console.log(`getJob("${fakeId}") returns: ${job}`);

  if (!job) {
    const frame = `event: error\ndata: ${JSON.stringify({ message: 'Job not found' })}\n\n`;
    console.log('SSE frame: ' + frame.replace(/\n/g, '\\n').replace(/\\n\\n$/, ''));
    console.log('Stream closes immediately.');
  }
}

// ============================================================================
// Example 3: Job error — error event after log lines
// ============================================================================

/**
 * When a job fails during execution, route.ts streams log lines while
 * the job is running, then sends an error event when status becomes 'error'.
 */
async function example3_jobError(): Promise<void> {
  console.log('\n=== Example 3: Job execution failure ===\n');

  const jobId = createJob('veo', { sectionId: 'intro' });

  // Run a failing executor
  await runJob(jobId, async (onLog) => {
    onLog('[veo] Starting video generation...');
    onLog('[veo] Contacting Veo API...');
    throw new Error('Veo API rate limit exceeded');
  });

  const failedJob = getJob(jobId);
  console.log(`Job status: ${failedJob?.status}`);
  console.log(`Job error: ${failedJob?.error}`);
  console.log(`Job has logs: ${(failedJob?.logs?.length ?? 0) > 0}`);

  // Show what route.ts would emit for this job
  if (failedJob?.logs) {
    const lines = failedJob.logs.split('\n').filter(Boolean);
    for (const line of lines) {
      console.log(`SSE: data: ${JSON.stringify({ type: 'log', message: line })}\\n\\n`);
    }
  }
  console.log(`SSE: event: error\\ndata: ${JSON.stringify({ message: failedJob?.error })}\\n\\n`);
  console.log('Stream closes after error event.');
}

// ============================================================================
// Example 4: Response headers and stream construction
// ============================================================================

/**
 * The route handler returns a Response with SSE headers:
 *   Content-Type: text/event-stream
 *   Cache-Control: no-cache
 *   Connection: keep-alive
 *
 * And exports: export const dynamic = 'force-dynamic'
 */
function example4_responseHeaders(): void {
  console.log('\n=== Example 4: Response headers ===\n');

  // Demonstrate the Response construction (mirrors route.ts)
  const encoder = new TextEncoder();
  const stream = new ReadableStream<Uint8Array>({
    start(controller) {
      controller.enqueue(encoder.encode('data: {"type":"log","message":"test"}\n\n'));
      controller.enqueue(encoder.encode('event: done\ndata: {}\n\n'));
      controller.close();
    },
  });

  const response = new Response(stream, {
    headers: {
      'Content-Type': 'text/event-stream',
      'Cache-Control': 'no-cache',
      Connection: 'keep-alive',
    },
  });

  console.log(`Content-Type: ${response.headers.get('Content-Type')}`);
  console.log(`Cache-Control: ${response.headers.get('Cache-Control')}`);
  console.log(`Connection: ${response.headers.get('Connection')}`);
  console.log('dynamic: force-dynamic (exported constant)');
}

// ============================================================================
// Example 5: Browser EventSource client pattern
// ============================================================================

/**
 * Shows how clients consume the SSE stream using EventSource.
 * Log lines arrive as default "message" events, while "done" and "error"
 * are named events that require addEventListener.
 */
function example5_clientPattern(): void {
  console.log('\n=== Example 5: Client EventSource pattern ===\n');

  console.log('Browser usage:');
  console.log('  const es = new EventSource("/api/jobs/<id>/stream");');
  console.log('  es.onmessage = (e) => {');
  console.log('    const { type, message } = JSON.parse(e.data);');
  console.log('    if (type === "log") appendLog(message);');
  console.log('  };');
  console.log('  es.addEventListener("done", () => { setStatus("done"); es.close(); });');
  console.log('  es.addEventListener("error", (e) => { handleError(e); es.close(); });');
}

// ============================================================================
// Example 6: Internal server error handling
// ============================================================================

/**
 * If getJob() or poll logic throws unexpectedly, route.ts catches the
 * error in a try/catch, sends an error event, and closes the stream.
 */
function example6_internalError(): void {
  console.log('\n=== Example 6: Internal server error ===\n');

  console.log('If poll() throws unexpectedly:');
  console.log(`  SSE: event: error\\ndata: {"message":"Internal Server Error"}\\n\\n`);
  console.log('  Stream closes. Error logged server-side via console.error().');
}

// ============================================================================
// Run all examples
// ============================================================================

async function main(): Promise<void> {
  console.log('========================================');
  console.log('SSE Job Stream Route - Usage Examples');
  console.log('========================================\n');

  await example1_ssePollingWithGetJob();
  example2_jobNotFound();
  await example3_jobError();
  example4_responseHeaders();
  example5_clientPattern();
  example6_internalError();

  console.log('\n========================================');
  console.log('All examples completed successfully');
  console.log('========================================');
}

if (require.main === module) {
  main().catch(console.error);
}

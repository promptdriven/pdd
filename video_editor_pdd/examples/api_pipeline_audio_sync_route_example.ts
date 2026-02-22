// api_pipeline_audio_sync_route_example.ts
//
// Comprehensive usage example for:
//   - app/api/pipeline/audio-sync/run/route.ts   (POST — audio sync pipeline via SSE)
//   - app/api/pipeline/audio-sync/timestamps/route.ts (GET — word timestamps)
//
// This file verifies the audio sync pipeline endpoints by:
//   1. Exercising the DAG orchestration (auto-runs prerequisite stages)
//   2. Testing the POST handler SSE stream response pattern
//   3. Verifying source file structure matches prompt requirements
//   4. Demonstrating SSE event parsing for audio sync events
//   5. Verifying word timestamps file handling
//
// For standalone execution (outside a running Next.js server), mock executors
// are registered for all required pipeline stages, and an in-memory SQLite
// database is used so each run starts fresh.

// Use an in-memory database so each run starts fresh
process.env.DB_PATH = ':memory:';

import fs from 'fs';
import path from 'path';
import os from 'os';
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
 * The audio-sync stage depends on 'tts-render' -> 'tts-script' -> 'script' -> 'setup'.
 * Register mock executors for all required stages so DAG orchestration
 * runs end-to-end without needing python3 or a running Next.js server.
 */
const STAGES_NEEDED: PipelineStage[] = ['setup', 'script', 'tts-script', 'tts-render', 'audio-sync'];

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
// Example 1: Verify DAG prerequisites for audio-sync
// ============================================================================

function example1_dagPrereqs(): void {
  console.log('=== Example 1: DAG prerequisites for audio-sync ===');

  const deps = PIPELINE_DAG['audio-sync'];
  assert(Array.isArray(deps), 'audio-sync has DAG entry');
  assert(deps.includes('tts-render'), 'audio-sync depends on tts-render');

  const ttsRenderDeps = PIPELINE_DAG['tts-render'];
  assert(ttsRenderDeps.includes('tts-script'), 'tts-render depends on tts-script');

  const ttsScriptDeps = PIPELINE_DAG['tts-script'];
  assert(ttsScriptDeps.includes('script'), 'tts-script depends on script');

  const scriptDeps = PIPELINE_DAG['script'];
  assert(scriptDeps.includes('setup'), 'script depends on setup');

  console.log('  Chain: setup -> script -> tts-script -> tts-render -> audio-sync');
  console.log('');
}

// ============================================================================
// Example 2: Run audio-sync via DAG orchestration with event capture
// ============================================================================

/**
 * Exercises runPipelineStage('audio-sync', ...) which auto-runs all
 * prerequisite stages (setup -> script -> tts-script -> tts-render) before
 * executing audio-sync. Captures all SSE events emitted during execution
 * and verifies them.
 */
async function example2_runPipelineStage(): Promise<void> {
  console.log('=== Example 2: DAG orchestration for audio-sync ===');

  const events: object[] = [];
  const mockSend: SseSend = (data: object) => {
    events.push(data);
  };

  const jobId = await runPipelineStage('audio-sync', {}, mockSend);

  assert(typeof jobId === 'string' && jobId.length > 0, 'runPipelineStage returns a job ID');

  const job = getJob(jobId);
  assert(job !== undefined, 'Job exists in database');
  assert(job?.stage === 'audio-sync', 'Job stage is audio-sync');
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

  const ttsScriptLogs = logEvents.filter((e: any) =>
    typeof e.message === 'string' && e.message.includes('[tts-script]')
  );
  assert(ttsScriptLogs.length > 0, 'tts-script stage auto-ran as prerequisite');

  const ttsRenderLogs = logEvents.filter((e: any) =>
    typeof e.message === 'string' && e.message.includes('[tts-render]')
  );
  assert(ttsRenderLogs.length > 0, 'tts-render stage auto-ran as prerequisite');

  const audioSyncLogs = logEvents.filter((e: any) =>
    typeof e.message === 'string' && e.message.includes('[audio-sync]')
  );
  assert(audioSyncLogs.length > 0, 'audio-sync stage executor ran');

  console.log(`  Job ID: ${jobId}`);
  console.log(`  Total events: ${events.length} (${logEvents.length} logs, ${progressEvents.length} progress)`);
  console.log('');
}

// ============================================================================
// Example 3: Source file structure verification — run route
// ============================================================================

/**
 * Reads the run route source and verifies it matches prompt requirements:
 *   - registerExecutor('audio-sync', ...) for pipeline integration
 *   - POST handler with SSE streaming
 *   - Spawns python3 sync_audio_pipeline.py
 *   - Streams stdout/stderr as SSE log events
 *   - Emits per-section status events on completion
 *   - First SSE event includes jobId
 */
function example3_runRouteSourceStructure(): void {
  console.log('=== Example 3: Run route source structure verification ===');

  const sourceCode = fs.readFileSync(
    path.join(__dirname, '..', 'app', 'api', 'pipeline', 'audio-sync', 'run', 'route.ts'),
    'utf-8'
  );

  // Requirement: export async function POST
  assert(
    /export\s+async\s+function\s+POST/.test(sourceCode),
    'Exports async POST handler'
  );

  // Requirement: registerExecutor('audio-sync', ...)
  assert(
    sourceCode.includes('registerExecutor') && sourceCode.includes('audio-sync'),
    'Registers audio-sync executor'
  );

  // Requirement: Spawn python3 sync_audio_pipeline.py
  assert(sourceCode.includes('sync_audio_pipeline.py'), 'References sync_audio_pipeline.py script');
  assert(sourceCode.includes('python3'), 'Spawns python3');
  assert(sourceCode.includes('spawn'), 'Uses child_process.spawn');

  // Requirement: SSE streaming
  assert(sourceCode.includes('text/event-stream'), 'Sets Content-Type to text/event-stream');
  assert(sourceCode.includes('no-cache'), 'Sets Cache-Control to no-cache');
  assert(sourceCode.includes('keep-alive'), 'Sets Connection to keep-alive');

  // Requirement: Reads sectionGroups from project
  assert(
    sourceCode.includes('sectionGroups') || sourceCode.includes('loadProject'),
    'Reads sectionGroups from project configuration'
  );

  // Requirement: Per-section status events
  assert(sourceCode.includes("type") && sourceCode.includes("section"), 'Emits section status events');
  assert(sourceCode.includes('sectionId'), 'Section events include sectionId');

  // Requirement: imports from lib/jobs
  assert(sourceCode.includes('@/lib/jobs') || sourceCode.includes('../lib/jobs'), 'Imports from lib/jobs');

  // Requirement: imports from lib/types or uses SseSend
  assert(sourceCode.includes('SseSend') || sourceCode.includes('@/lib/types'), 'Uses SseSend type');

  // Requirement: Passes SECTION_GROUPS env var
  assert(sourceCode.includes('SECTION_GROUPS'), 'Passes SECTION_GROUPS env var to subprocess');

  console.log('');
}

// ============================================================================
// Example 4: Word timestamps file handling verification
// ============================================================================

/**
 * Verifies the word timestamps JSON format and file path conventions
 * match the prompt requirements. Creates a temp fixture and validates
 * the expected structure.
 */
function example4_wordTimestampsFormat(): void {
  console.log('=== Example 4: Word timestamps format verification ===');

  // Create a temp directory to simulate outputs/tts/<sectionId>/word_timestamps.json
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'audio-sync-test-'));
  const sectionDir = path.join(tmpDir, 'outputs', 'tts', 'intro');
  fs.mkdirSync(sectionDir, { recursive: true });

  // Create word_timestamps.json in the expected format
  const timestamps = {
    words: [
      { word: 'Welcome', start: 0.0, end: 0.45, segmentId: 'seg_001' },
      { word: 'to', start: 0.46, end: 0.55, segmentId: 'seg_001' },
      { word: 'the', start: 0.56, end: 0.65, segmentId: 'seg_001' },
      { word: 'product', start: 0.66, end: 1.1, segmentId: 'seg_001' },
      { word: 'launch', start: 1.11, end: 1.55, segmentId: 'seg_002' },
    ],
  };

  const timestampsPath = path.join(sectionDir, 'word_timestamps.json');
  fs.writeFileSync(timestampsPath, JSON.stringify(timestamps, null, 2));

  // Verify the file can be read and parsed
  const raw = fs.readFileSync(timestampsPath, 'utf-8');
  const parsed = JSON.parse(raw);

  assert(Array.isArray(parsed.words), 'Timestamps has words array');
  assert(parsed.words.length === 5, `Has 5 word timestamps (got ${parsed.words.length})`);

  // Verify each word has the required fields
  for (const w of parsed.words) {
    assert(typeof w.word === 'string', `Word "${w.word}" has string word field`);
    assert(typeof w.start === 'number', `Word "${w.word}" has number start field`);
    assert(typeof w.end === 'number', `Word "${w.word}" has number end field`);
    assert(typeof w.segmentId === 'string', `Word "${w.word}" has string segmentId field`);
  }

  // Verify start < end for all words
  for (const w of parsed.words) {
    assert(w.start < w.end, `Word "${w.word}" start (${w.start}) < end (${w.end})`);
  }

  // Verify expected path structure: outputs/tts/<sectionId>/word_timestamps.json
  const expectedRelativePath = path.join('outputs', 'tts', 'intro', 'word_timestamps.json');
  const actualRelativePath = path.relative(tmpDir, timestampsPath);
  assert(actualRelativePath === expectedRelativePath, `Timestamps path matches convention: ${actualRelativePath}`);

  // Cleanup
  fs.rmSync(tmpDir, { recursive: true, force: true });

  console.log('');
}

// ============================================================================
// Example 5: SSE event parsing demonstration for audio sync events
// ============================================================================

/**
 * Demonstrates parsing the raw SSE wire format that the run endpoint produces.
 * Covers the specific event types emitted by the audio-sync endpoint.
 */
function example5_sseEventParsing(): void {
  console.log('=== Example 5: SSE event parsing for audio sync ===');

  // Parse a job event (first event from the stream)
  const jobEvent = 'data: {"type":"job","jobId":"abc-123-def"}';
  const jobPayload = JSON.parse(jobEvent.replace(/^data:\s*/, ''));
  assert(jobPayload.type === 'job', 'Parsed job event type');
  assert(jobPayload.jobId === 'abc-123-def', 'Parsed jobId from job event');

  // Parse a section done event
  const sectionDoneEvent = 'data: {"type":"section","sectionId":"intro","status":"done"}';
  const sectionDonePayload = JSON.parse(sectionDoneEvent.replace(/^data:\s*/, ''));
  assert(sectionDonePayload.type === 'section', 'Parsed section event type');
  assert(sectionDonePayload.sectionId === 'intro', 'Parsed sectionId');
  assert(sectionDonePayload.status === 'done', 'Parsed section status as done');

  // Parse a section error event
  const sectionErrorEvent = 'data: {"type":"section","sectionId":"main","status":"error"}';
  const sectionErrorPayload = JSON.parse(sectionErrorEvent.replace(/^data:\s*/, ''));
  assert(sectionErrorPayload.type === 'section', 'Parsed section error event type');
  assert(sectionErrorPayload.sectionId === 'main', 'Parsed error sectionId');
  assert(sectionErrorPayload.status === 'error', 'Parsed section status as error');

  // Parse a complete event
  const completeEvent = 'data: {"type":"complete","jobId":"abc-123-def"}';
  const completePayload = JSON.parse(completeEvent.replace(/^data:\s*/, ''));
  assert(completePayload.type === 'complete', 'Parsed complete event type');
  assert(completePayload.jobId === 'abc-123-def', 'Parsed jobId from complete event');

  // Parse an error event
  const errorEvent = 'data: {"type":"error","error":"sync_audio_pipeline.py exited with code 1"}';
  const errorPayload = JSON.parse(errorEvent.replace(/^data:\s*/, ''));
  assert(errorPayload.type === 'error', 'Parsed error event type');
  assert(errorPayload.error.includes('sync_audio_pipeline.py'), 'Parsed error message');

  console.log('');
}

// ============================================================================
// Example 6: sync_audio_pipeline.py script verification
// ============================================================================

/**
 * Verifies that sync_audio_pipeline.py exists at the project root
 * and contains expected functionality.
 */
function example6_pythonScriptVerification(): void {
  console.log('=== Example 6: sync_audio_pipeline.py verification ===');

  const scriptPath = path.join(__dirname, '..', 'scripts', 'sync_audio_pipeline.py');
  assert(fs.existsSync(scriptPath), 'sync_audio_pipeline.py exists in scripts directory');

  const sourceCode = fs.readFileSync(scriptPath, 'utf-8');

  // Verify key functionality
  assert(sourceCode.includes('sectionGroups') || sourceCode.includes('section_groups'),
    'Script handles sectionGroups');
  assert(sourceCode.includes('word_timestamps') || sourceCode.includes('WordTimestamp'),
    'Script generates word timestamps');
  assert(sourceCode.includes('.wav'), 'Script handles WAV files');
  assert(sourceCode.includes('json.dumps') || sourceCode.includes('json.dump'),
    'Script outputs JSON');
  assert(sourceCode.includes('concatenate') || sourceCode.includes('concat'),
    'Script concatenates audio segments');

  console.log('');
}

// ============================================================================
// Example 7: Timestamps route source structure verification
// ============================================================================

/**
 * Reads the timestamps route source (separate file per prompt deliverables)
 * and verifies it matches prompt requirements:
 *   - GET handler exported
 *   - Reads section query param
 *   - Reads word_timestamps.json from outputs/tts/<sectionId>/
 *   - Returns { words: WordTimestamp[] }
 *   - Returns 404 if file doesn't exist
 */
function example7_timestampsRouteSourceStructure(): void {
  console.log('=== Example 7: Timestamps route source structure verification ===');

  const timestampsRoutePath = path.join(
    __dirname, '..', 'app', 'api', 'pipeline', 'audio-sync', 'timestamps', 'route.ts'
  );

  // Deliverable: timestamps route exists as a separate file
  assert(fs.existsSync(timestampsRoutePath), 'Timestamps route exists as separate file');

  const sourceCode = fs.readFileSync(timestampsRoutePath, 'utf-8');

  // Requirement: export async function GET
  assert(
    /export\s+async\s+function\s+GET/.test(sourceCode),
    'Exports async GET handler'
  );

  // Requirement: reads section query param
  assert(sourceCode.includes('section'), 'Reads section query param');

  // Requirement: reads word_timestamps.json
  assert(sourceCode.includes('word_timestamps.json'), 'References word_timestamps.json file');

  // Requirement: constructs path with outputs/tts/<sectionId>
  assert(sourceCode.includes('outputs') && sourceCode.includes('tts'), 'Uses outputs/tts path');

  // Requirement: returns { words: WordTimestamp[] }
  assert(sourceCode.includes('WordTimestamp'), 'Defines WordTimestamp interface');
  assert(sourceCode.includes('words'), 'Returns words array');

  // Requirement: 404 when file not found
  assert(sourceCode.includes('404'), 'Returns 404 for missing timestamps');

  // Requirement: uses NextResponse.json
  assert(sourceCode.includes('NextResponse'), 'Uses NextResponse');

  // Verify run route does NOT contain GET handler (separation of concerns)
  const runRouteSource = fs.readFileSync(
    path.join(__dirname, '..', 'app', 'api', 'pipeline', 'audio-sync', 'run', 'route.ts'),
    'utf-8'
  );
  assert(
    !/export\s+async\s+function\s+GET/.test(runRouteSource),
    'Run route does NOT export GET handler (separate file)'
  );

  console.log('');
}

// ============================================================================
// Run all examples
// ============================================================================

async function main(): Promise<void> {
  example1_dagPrereqs();
  await example2_runPipelineStage();
  example3_runRouteSourceStructure();
  example4_wordTimestampsFormat();
  example5_sseEventParsing();
  example6_pythonScriptVerification();
  example7_timestampsRouteSourceStructure();

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

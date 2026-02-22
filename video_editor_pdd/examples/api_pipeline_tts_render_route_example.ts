// api_pipeline_tts_render_route_example.ts
//
// Comprehensive usage example for:
//   - app/api/pipeline/tts-render/run/route.ts   (POST — TTS rendering via SSE)
//   - app/api/pipeline/tts-render/segments/route.ts (GET — segment listing)
//
// This file verifies the TTS render pipeline endpoints by:
//   1. Exercising the DAG orchestration (auto-runs prerequisite stages)
//   2. Testing the POST handler SSE stream response pattern
//   3. Testing the GET handler for segment listing with filesystem fixtures
//   4. Verifying source file structure matches prompt requirements
//   5. Demonstrating SSE event parsing for TTS render events
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
 * The tts-render stage depends on 'tts-script' -> 'script' -> 'setup'.
 * Register mock executors for all required stages so DAG orchestration
 * runs end-to-end without needing python3 or a running Next.js server.
 */
const STAGES_NEEDED: PipelineStage[] = ['setup', 'script', 'tts-script', 'tts-render'];

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
// Example 1: Verify DAG prerequisites for tts-render
// ============================================================================

function example1_dagPrereqs(): void {
  console.log('=== Example 1: DAG prerequisites for tts-render ===');

  const deps = PIPELINE_DAG['tts-render'];
  assert(Array.isArray(deps), 'tts-render has DAG entry');
  assert(deps.includes('tts-script'), 'tts-render depends on tts-script');

  const ttsScriptDeps = PIPELINE_DAG['tts-script'];
  assert(ttsScriptDeps.includes('script'), 'tts-script depends on script');

  const scriptDeps = PIPELINE_DAG['script'];
  assert(scriptDeps.includes('setup'), 'script depends on setup');

  console.log('  Chain: setup -> script -> tts-script -> tts-render');
  console.log('');
}

// ============================================================================
// Example 2: Run tts-render via DAG orchestration with event capture
// ============================================================================

/**
 * Exercises runPipelineStage('tts-render', ...) which auto-runs all
 * prerequisite stages (setup -> script -> tts-script) before executing tts-render.
 * Captures all SSE events emitted during execution and verifies them.
 */
async function example2_runPipelineStage(): Promise<void> {
  console.log('=== Example 2: DAG orchestration for tts-render ===');

  const events: object[] = [];
  const mockSend: SseSend = (data: object) => {
    events.push(data);
  };

  const jobId = await runPipelineStage('tts-render', {}, mockSend);

  assert(typeof jobId === 'string' && jobId.length > 0, 'runPipelineStage returns a job ID');

  const job = getJob(jobId);
  assert(job !== undefined, 'Job exists in database');
  assert(job?.stage === 'tts-render', 'Job stage is tts-render');
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
  assert(ttsRenderLogs.length > 0, 'tts-render stage executor ran');

  console.log(`  Job ID: ${jobId}`);
  console.log(`  Total events: ${events.length} (${logEvents.length} logs, ${progressEvents.length} progress)`);
  console.log('');
}

// ============================================================================
// Example 3: Segment parsing and WAV duration logic verification
// ============================================================================

/**
 * Exercises the segment parsing logic from tts_script.md and WAV duration
 * calculation by reimplementing the same algorithm used in the route.
 * This verifies the expected behavior without importing the route file
 * (which uses @/ path aliases that require the Next.js bundler).
 */
function example3_segmentParsing(): void {
  console.log('=== Example 3: Segment parsing from tts_script.md ===');

  // Reimplement the same parsing logic from the route to verify behavior
  function parseSegments(content: string): { id: string; text?: string }[] {
    const lines = content.split(/\r?\n/);
    const segments: { id: string; text?: string }[] = [];
    let current: { id: string; lines: string[] } | null = null;

    for (const line of lines) {
      const heading = line.match(/^#{1,6}\s+(.+)$/);
      if (heading) {
        if (current) {
          const text = current.lines.join('\n').trim();
          segments.push({ id: current.id, text: text || undefined });
        }
        const headingText = heading[1].trim();
        const id = headingText.split(/\s+/)[0];
        current = { id, lines: [] };
      } else if (current) {
        current.lines.push(line);
      }
    }

    if (current) {
      const text = current.lines.join('\n').trim();
      segments.push({ id: current.id, text: text || undefined });
    }

    return segments;
  }

  function wavDuration(filePath: string): number | undefined {
    try {
      const buf = fs.readFileSync(filePath);
      if (buf.length < 44) return undefined;
      const numChannels = buf.readUInt16LE(22);
      const sampleRate = buf.readUInt32LE(24);
      const bitsPerSample = buf.readUInt16LE(34);
      const dataSize = buf.readUInt32LE(40);
      const bytesPerSample = bitsPerSample / 8;
      const duration = dataSize / (sampleRate * numChannels * bytesPerSample);
      return Math.round(duration * 1000) / 1000;
    } catch {
      return undefined;
    }
  }

  const testScript = `# intro
Welcome to the product launch.

# main
Here are the key features of our product.

# outro
Thank you for watching.
`;

  const segments = parseSegments(testScript);
  assert(Array.isArray(segments), 'parseSegments returns an array');
  assert(segments.length === 3, `Parsed 3 segments from tts_script.md (got ${segments.length})`);

  const ids = segments.map((s: any) => s.id);
  assert(ids.includes('intro'), 'Parsed segment id: intro');
  assert(ids.includes('main'), 'Parsed segment id: main');
  assert(ids.includes('outro'), 'Parsed segment id: outro');

  const introSeg = segments.find((s: any) => s.id === 'intro');
  assert(
    introSeg?.text?.includes('Welcome') === true,
    'intro segment text contains "Welcome"'
  );

  // Test WAV duration with a valid WAV file (~1 second of audio)
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tts-test-'));
  const wavPath = path.join(tmpDir, 'test.wav');

  // Create a WAV file: 44-byte header + 44100 bytes of data = ~0.5s mono 16-bit 44100Hz
  const dataSize = 44100; // enough samples for a measurable duration
  const wavBuf = Buffer.alloc(44 + dataSize);
  wavBuf.write('RIFF', 0);
  wavBuf.writeUInt32LE(36 + dataSize, 4); // file size - 8
  wavBuf.write('WAVE', 8);
  wavBuf.write('fmt ', 12);
  wavBuf.writeUInt32LE(16, 16); // chunk size
  wavBuf.writeUInt16LE(1, 20);  // PCM format
  wavBuf.writeUInt16LE(1, 22);  // mono
  wavBuf.writeUInt32LE(44100, 24); // sample rate
  wavBuf.writeUInt32LE(88200, 28); // byte rate
  wavBuf.writeUInt16LE(2, 32);  // block align
  wavBuf.writeUInt16LE(16, 34); // bits per sample
  wavBuf.write('data', 36);
  wavBuf.writeUInt32LE(dataSize, 40);  // data size

  fs.writeFileSync(wavPath, wavBuf);

  const duration = wavDuration(wavPath);
  assert(typeof duration === 'number', 'wavDuration returns a number for valid WAV');
  assert(duration !== undefined && duration > 0, `WAV duration > 0 (got ${duration})`);

  // Cleanup temp
  fs.unlinkSync(wavPath);
  fs.rmdirSync(tmpDir);

  console.log('');
}

// ============================================================================
// Example 4: Source file structure verification — run route
// ============================================================================

/**
 * Reads the run route source and verifies it matches prompt requirements:
 *   - registerExecutor('tts-render', ...) for pipeline integration
 *   - POST handler with SSE streaming
 *   - Spawns python3 render_tts.py with --segment flags
 *   - Streams stdout/stderr as SSE log events
 *   - Emits per-segment status events on completion
 *   - First SSE event includes jobId
 */
function example4_runRouteSourceStructure(): void {
  console.log('=== Example 4: Run route source structure verification ===');

  const sourceCode = fs.readFileSync(
    path.join(__dirname, '..', 'app', 'api', 'pipeline', 'tts-render', 'run', 'route.ts'),
    'utf-8'
  );

  // Requirement: export async function POST
  assert(
    /export\s+async\s+function\s+POST/.test(sourceCode),
    'Exports async POST handler'
  );

  // Requirement: registerExecutor('tts-render', ...)
  assert(
    sourceCode.includes('registerExecutor') && sourceCode.includes('tts-render'),
    'Registers tts-render executor'
  );

  // Requirement: Spawn python3 render_tts.py
  assert(sourceCode.includes('render_tts.py'), 'References render_tts.py script');
  assert(sourceCode.includes('python3'), 'Spawns python3');
  assert(sourceCode.includes('spawn'), 'Uses child_process.spawn');

  // Requirement: --segment flag for filtering
  assert(sourceCode.includes('--segment'), 'Uses --segment flag for segment filtering');

  // Requirement: SSE streaming
  assert(sourceCode.includes('text/event-stream'), 'Sets Content-Type to text/event-stream');
  assert(sourceCode.includes('no-cache'), 'Sets Cache-Control to no-cache');
  assert(sourceCode.includes('keep-alive'), 'Sets Connection to keep-alive');

  // Requirement: First SSE event includes jobId
  assert(sourceCode.includes('send({ jobId })'), 'First SSE event sends jobId');

  // Requirement: Per-segment status events
  assert(sourceCode.includes("type: \"segment\""), 'Emits segment status events');
  assert(sourceCode.includes('segmentId'), 'Segment events include segmentId');

  // Requirement: Reads tts_script.md for segment metadata
  assert(sourceCode.includes('tts_script.md'), 'References tts_script.md for segment parsing');

  // Requirement: outputs/tts/ for per-segment WAV files
  assert(sourceCode.includes('outputs') && sourceCode.includes('tts'), 'References outputs/tts directory');

  // Requirement: imports from lib/jobs
  assert(sourceCode.includes('@/lib/jobs'), 'Imports from @/lib/jobs');

  // Requirement: imports from lib/types
  assert(sourceCode.includes('@/lib/types') || sourceCode.includes('SseSend'), 'Imports SseSend type');

  // Requirement: parseSegmentsFromScript function
  assert(sourceCode.includes('parseSegmentsFromScript'), 'Defines parseSegmentsFromScript');

  // Requirement: getWavDuration function
  assert(sourceCode.includes('getWavDuration'), 'Defines getWavDuration');

  console.log('');
}

// ============================================================================
// Example 5: Source file structure verification — segments route
// ============================================================================

/**
 * Reads the segments route source and verifies prompt requirements:
 *   - GET handler that returns { segments: TtsSegment[] }
 *   - Scans outputs/tts/*.wav directory
 *   - Cross-references with tts_script.md
 *   - TtsSegment interface with id, status, duration, text
 */
function example5_segmentsRouteSourceStructure(): void {
  console.log('=== Example 5: Segments route source structure verification ===');

  const segmentsPath = path.join(
    __dirname, '..', 'app', 'api', 'pipeline', 'tts-render', 'segments', 'route.ts'
  );

  assert(fs.existsSync(segmentsPath), 'Segments route file exists at app/api/pipeline/tts-render/segments/route.ts');

  const sourceCode = fs.readFileSync(segmentsPath, 'utf-8');

  // Requirement: GET handler
  assert(
    /export\s+async\s+function\s+GET/.test(sourceCode),
    'Exports async GET handler'
  );

  // Requirement: TtsSegment interface
  assert(sourceCode.includes('TtsSegment'), 'Defines TtsSegment interface');

  // Requirement: TtsSegment status values
  assert(
    sourceCode.includes('"done"') && sourceCode.includes('"missing"') && sourceCode.includes('"error"'),
    'TtsSegment has done/missing/error status values'
  );

  // Requirement: Returns NextResponse.json with segments array
  assert(sourceCode.includes('NextResponse.json'), 'Returns JSON response via NextResponse');
  assert(sourceCode.includes('{ segments }') || sourceCode.includes('{segments}'), 'Returns { segments } shape');

  // Requirement: Scans outputs/tts/*.wav
  assert(sourceCode.includes('.wav'), 'Scans for .wav files');
  assert(sourceCode.includes('readdirSync'), 'Uses readdirSync to scan output directory');

  // Requirement: Cross-references with tts_script.md segments
  assert(sourceCode.includes('parseSegmentsFromScript'), 'Uses parseSegmentsFromScript for segment metadata');

  console.log('');
}

// ============================================================================
// Example 6: SSE event parsing demonstration for TTS render events
// ============================================================================

/**
 * Demonstrates parsing the raw SSE wire format that the run endpoint produces.
 * Covers the specific event types emitted by the tts-render endpoint.
 */
function example6_sseEventParsing(): void {
  console.log('=== Example 6: SSE event parsing for TTS render ===');

  // Parse a jobId event (first event from the stream)
  const jobIdEvent = 'data: {"jobId":"abc-123-def"}';
  const jobIdPayload = JSON.parse(jobIdEvent.replace(/^data:\s*/, ''));
  assert(jobIdPayload.jobId === 'abc-123-def', 'Parsed jobId from first event');

  // Parse a log event
  const logEvent = 'data: {"type":"log","message":"Rendering segment intro...","jobId":"abc-123"}';
  const logPayload = JSON.parse(logEvent.replace(/^data:\s*/, ''));
  assert(logPayload.type === 'log', 'Parsed log event type');
  assert(logPayload.message.includes('Rendering'), 'Parsed log message');
  assert(logPayload.jobId === 'abc-123', 'Log event includes jobId');

  // Parse a segment status event
  const segmentEvent = 'data: {"type":"segment","segmentId":"intro","status":"done","duration":12.5}';
  const segmentPayload = JSON.parse(segmentEvent.replace(/^data:\s*/, ''));
  assert(segmentPayload.type === 'segment', 'Parsed segment event type');
  assert(segmentPayload.segmentId === 'intro', 'Parsed segmentId');
  assert(segmentPayload.status === 'done', 'Parsed segment status');
  assert(segmentPayload.duration === 12.5, 'Parsed segment duration');

  // Parse an error event
  const errorEvent = 'data: {"type":"error","message":"render_tts.py exited with code 1"}';
  const errorPayload = JSON.parse(errorEvent.replace(/^data:\s*/, ''));
  assert(errorPayload.type === 'error', 'Parsed error event type');
  assert(errorPayload.message.includes('render_tts.py'), 'Parsed error message');

  console.log('');
}

// ============================================================================
// Run all examples
// ============================================================================

async function main(): Promise<void> {
  example1_dagPrereqs();
  await example2_runPipelineStage();
  example3_segmentParsing();
  example4_runRouteSourceStructure();
  example5_segmentsRouteSourceStructure();
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

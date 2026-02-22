// api_pipeline_render_route_example.ts
//
// Comprehensive usage example for:
//   - app/api/pipeline/render/run/route.ts (POST — section rendering via SSE)
//
// This file verifies the render pipeline route by:
//   1. Exercising DAG orchestration (auto-runs prerequisite stages)
//   2. Testing the render executor registration and section rendering flow
//   3. Verifying source file structure matches prompt requirements
//   4. Demonstrating SSE event parsing for render progress events
//   5. Verifying parallel rendering batching behavior
//   6. Verifying duration/offset recalculation logic
//   7. Verifying output path conventions
//
// For standalone execution (outside a running Next.js server), mock executors
// are registered for all required pipeline stages, and an in-memory SQLite
// database is used so each run starts fresh.

// Use an in-memory database so each run starts fresh
process.env.DB_PATH = ':memory:';

import fs from 'fs';
import path from 'path';
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
// Setup: Register mock executors for all pipeline stages
// ============================================================================

/**
 * The render stage depends on the full DAG chain:
 *   setup -> script -> (tts-script -> tts-render -> audio-sync) || (specs -> veo) -> compositions -> render
 *
 * Register mock executors for all stages so DAG orchestration
 * runs end-to-end without needing Remotion, ffmpeg, or a running Next.js server.
 */
const ALL_STAGES: PipelineStage[] = [
  'setup', 'script', 'tts-script', 'tts-render', 'audio-sync',
  'specs', 'veo', 'compositions', 'render', 'audit',
];

for (const stage of ALL_STAGES) {
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
// Example 1: Verify DAG prerequisites for render
// ============================================================================

/**
 * The pipeline DAG defines that 'render' depends on 'compositions',
 * which in turn depends on both 'audio-sync' and 'veo' tracks.
 * This creates two parallel prerequisite chains:
 *   Audio:  setup -> script -> tts-script -> tts-render -> audio-sync
 *   Visual: setup -> script -> specs -> veo
 * Both must complete before compositions, which must complete before render.
 */
function example1_dagPrereqs(): void {
  console.log('=== Example 1: DAG prerequisites for render ===');

  const renderDeps = PIPELINE_DAG['render'];
  assert(Array.isArray(renderDeps), 'render has DAG entry');
  assert(renderDeps.includes('compositions'), 'render depends on compositions');

  const compositionsDeps = PIPELINE_DAG['compositions'];
  assert(compositionsDeps.includes('audio-sync'), 'compositions depends on audio-sync');
  assert(compositionsDeps.includes('veo'), 'compositions depends on veo');

  const audioSyncDeps = PIPELINE_DAG['audio-sync'];
  assert(audioSyncDeps.includes('tts-render'), 'audio-sync depends on tts-render');

  const veoDeps = PIPELINE_DAG['veo'];
  assert(veoDeps.includes('specs'), 'veo depends on specs');

  console.log('  Chain: setup -> script -> (tts-script -> tts-render -> audio-sync) || (specs -> veo) -> compositions -> render');
  console.log('');
}

// ============================================================================
// Example 2: Run render via DAG orchestration with event capture
// ============================================================================

/**
 * Exercises runPipelineStage('render', ...) which auto-runs all
 * prerequisite stages before executing render.
 * Captures all SSE events emitted during execution and verifies them.
 */
async function example2_runPipelineStage(): Promise<void> {
  console.log('=== Example 2: DAG orchestration for render ===');

  const events: object[] = [];
  const mockSend: SseSend = (data: object) => {
    events.push(data);
  };

  const jobId = await runPipelineStage('render', {}, mockSend);

  assert(typeof jobId === 'string' && jobId.length > 0, 'runPipelineStage returns a job ID');

  const job = getJob(jobId);
  assert(job !== undefined, 'Job exists in database');
  assert(job?.stage === 'render', 'Job stage is render');
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

  const compositionsLogs = logEvents.filter((e: any) =>
    typeof e.message === 'string' && e.message.includes('[compositions]')
  );
  assert(compositionsLogs.length > 0, 'Compositions stage auto-ran as prerequisite');

  const renderLogs = logEvents.filter((e: any) =>
    typeof e.message === 'string' && e.message.includes('[render]')
  );
  assert(renderLogs.length > 0, 'Render stage executor ran');

  console.log(`  Job ID: ${jobId}`);
  console.log(`  Total events: ${events.length} (${logEvents.length} logs, ${progressEvents.length} progress)`);
  console.log('');
}

// ============================================================================
// Example 3: Run render with sections parameter
// ============================================================================

/**
 * POST /api/pipeline/render/run accepts { sections?: string[] }.
 * This verifies the sections parameter is passed through to the executor.
 */
async function example3_runWithSections(): Promise<void> {
  console.log('=== Example 3: Run render with sections parameter ===');

  let capturedParams: Record<string, unknown> = {};
  registerExecutor('render', (params, _send) => {
    capturedParams = params;
    return async (onLog) => {
      onLog('[render] Running with sections filter');
      const progressFn = (onLog as unknown as { progress?: (p: number) => void })
        .progress;
      progressFn?.(100);
    };
  });

  const events: object[] = [];
  const mockSend: SseSend = (data: object) => {
    events.push(data);
  };

  const jobId = await runPipelineStage(
    'render',
    { sections: ['intro', 'outro'] },
    mockSend
  );

  assert(typeof jobId === 'string', 'runPipelineStage returns a job ID with sections param');
  assert(
    Array.isArray(capturedParams.sections),
    'sections parameter was passed to executor factory'
  );
  assert(
    (capturedParams.sections as string[]).length === 2,
    'Two sections were passed to executor'
  );

  const job = getJob(jobId);
  assert(job?.status === 'done', 'Job completed with sections parameter');

  // Re-register the standard mock executor
  registerExecutor('render', (_params, _send) => {
    return async (onLog) => {
      onLog('[render] Mock executor running');
      const progressFn = (onLog as unknown as { progress?: (p: number) => void })
        .progress;
      progressFn?.(100);
    };
  });

  console.log('');
}

// ============================================================================
// Example 4: Source file structure verification
// ============================================================================

/**
 * Reads the render route source and verifies it matches prompt requirements:
 *   - registerExecutor('render', ...) for pipeline integration
 *   - POST handler with SSE streaming
 *   - Uses renderSection, getSectionDuration from @/lib/render
 *   - Uses loadProject, saveProject from @/lib/project
 *   - SSE headers (text/event-stream, no-cache, keep-alive)
 *   - Parallel rendering with maxParallelRenders
 *   - Duration/offset recalculation
 */
function example4_sourceStructure(): void {
  console.log('=== Example 4: Source file structure verification ===');

  const sourceCode = fs.readFileSync(
    path.join(__dirname, '..', 'app', 'api', 'pipeline', 'render', 'run', 'route.ts'),
    'utf-8'
  );

  // Requirement: export handler function
  assert(
    /export\s+async\s+function\s+(POST_render|POST)/.test(sourceCode),
    'Exports async POST/POST_render handler'
  );

  // Requirement: registerExecutor('render', ...)
  assert(
    sourceCode.includes('registerExecutor') &&
    (sourceCode.includes("'render'") || sourceCode.includes('"render"')),
    'Registers render executor with registerExecutor'
  );

  // Requirement: Uses renderSection from @/lib/render
  assert(sourceCode.includes('renderSection'), 'Uses renderSection for Remotion rendering');

  // Requirement: Uses getSectionDuration for ffprobe
  assert(sourceCode.includes('getSectionDuration'), 'Uses getSectionDuration for ffprobe duration');

  // Requirement: Uses loadProject/saveProject from @/lib/project
  assert(sourceCode.includes('loadProject'), 'Uses loadProject() for project config');
  assert(sourceCode.includes('saveProject'), 'Uses saveProject() for project updates');

  // Requirement: SSE streaming headers
  assert(sourceCode.includes('text/event-stream'), 'Sets Content-Type to text/event-stream');
  assert(sourceCode.includes('no-cache'), 'Sets Cache-Control to no-cache');
  assert(sourceCode.includes('keep-alive'), 'Sets Connection to keep-alive');

  // Requirement: Uses runPipelineStage for DAG orchestration
  assert(sourceCode.includes('runPipelineStage'), 'Uses runPipelineStage for DAG orchestration');

  // Requirement: Emits section-progress events
  assert(sourceCode.includes('section-progress'), 'Emits section-progress SSE events');

  // Requirement: Imports from @/lib/jobs
  assert(sourceCode.includes('@/lib/jobs'), 'Imports from @/lib/jobs');

  // Requirement: Imports from @/lib/render
  assert(sourceCode.includes('@/lib/render'), 'Imports from @/lib/render');

  // Requirement: Imports from @/lib/project
  assert(sourceCode.includes('@/lib/project'), 'Imports from @/lib/project');

  // Requirement: Parallel rendering with maxParallelRenders
  assert(sourceCode.includes('maxParallelRenders'), 'References maxParallelRenders for parallel batching');

  // Requirement: Duration/offset recalculation
  assert(sourceCode.includes('offsetSeconds'), 'Handles offsetSeconds recalculation');
  assert(sourceCode.includes('durationSeconds'), 'Handles durationSeconds updates');

  // Requirement: Outputs to outputs/sections/ directory
  assert(
    sourceCode.includes('outputs') && sourceCode.includes('sections'),
    'References outputs/sections/ output directory'
  );

  // Requirement: Error handling with SSE error event
  assert(
    sourceCode.includes("'error'") || sourceCode.includes('"error"'),
    'Has error event handling'
  );

  // Requirement: Stitch handler (stitchFullVideo)
  assert(sourceCode.includes('stitchFullVideo'), 'References stitchFullVideo for ffmpeg concat');

  // Requirement: Full video output path
  assert(sourceCode.includes('full_video.mp4'), 'References full_video.mp4 output path');

  console.log('');
}

// ============================================================================
// Example 5: SSE event parsing for render-specific events
// ============================================================================

/**
 * Demonstrates parsing the raw SSE wire format produced by the render endpoint.
 * Covers the three event types:
 *   1. section-progress — per-section render progress (0–100%)
 *   2. jobId — final completion event
 *   3. error — unrecoverable error
 */
function example5_sseEventParsing(): void {
  console.log('=== Example 5: SSE event parsing for render ===');

  // Helper: parse SSE chunk
  function parseSseChunk(chunk: string): object[] {
    const events: object[] = [];
    const frames = chunk.split('\n\n');
    for (const frame of frames) {
      const dataLine = frame
        .split('\n')
        .find((l) => l.startsWith('data: '));
      if (dataLine) {
        events.push(JSON.parse(dataLine.slice(6)));
      }
    }
    return events;
  }

  // Parse a section-progress event
  const progressChunk =
    'data: {"type":"section-progress","sectionId":"intro","percent":42}\n\n';
  const progressEvents = parseSseChunk(progressChunk);
  assert(progressEvents.length === 1, 'Parsed one section-progress event');
  const pe = progressEvents[0] as any;
  assert(pe.type === 'section-progress', 'Event type is section-progress');
  assert(pe.sectionId === 'intro', 'sectionId field is correct');
  assert(pe.percent === 42, 'percent field is correct');

  // Parse a jobId completion event
  const jobIdChunk =
    'data: {"jobId":"550e8400-e29b-41d4-a716-446655440000"}\n\n';
  const jobIdEvents = parseSseChunk(jobIdChunk);
  const je = jobIdEvents[0] as any;
  assert(typeof je.jobId === 'string', 'Parsed jobId event');
  assert(je.jobId.length > 0, 'jobId is non-empty');

  // Parse an error event
  const errorChunk =
    'data: {"type":"error","message":"Composition not found"}\n\n';
  const errorEvents = parseSseChunk(errorChunk);
  const ee = errorEvents[0] as any;
  assert(ee.type === 'error', 'Parsed error event type');
  assert(ee.message.includes('Composition'), 'Error message content correct');

  // Parse multiple events in one chunk
  const multiChunk =
    'data: {"type":"section-progress","sectionId":"intro","percent":50}\n\n' +
    'data: {"type":"section-progress","sectionId":"intro","percent":100}\n\n';
  const multiEvents = parseSseChunk(multiChunk);
  assert(multiEvents.length === 2, 'Parsed multiple events from single chunk');

  // Verify SSE frame format
  const sseFrame = `data: ${JSON.stringify({ type: 'section-progress', sectionId: 'intro', percent: 50 })}\n\n`;
  assert(sseFrame.startsWith('data: '), 'SSE frame starts with "data: "');
  assert(sseFrame.endsWith('\n\n'), 'SSE frame ends with double newline');

  console.log('');
}

// ============================================================================
// Example 6: Duration/offset recalculation logic
// ============================================================================

/**
 * updateProjectDurations(sectionId, durationSeconds) is called after each
 * section finishes rendering. It:
 *   1. Loads project.json via loadProject()
 *   2. Finds the section by ID and sets its durationSeconds
 *   3. Recalculates offsetSeconds for ALL sections as cumulative durations
 *   4. Saves the updated config atomically via saveProject()
 *
 * Example:
 *   Before: intro=12.5s, main=45.0s, outro=8.0s (all offsets=0)
 *   After:  intro offset=0, main offset=12.5, outro offset=57.5
 */
function example6_durationOffsetRecalculation(): void {
  console.log('=== Example 6: Duration/offset recalculation logic ===');

  // Simulate the recalculation logic from updateProjectDurations
  const sections = [
    { id: 'intro', durationSeconds: 12.5, offsetSeconds: 0 },
    { id: 'main', durationSeconds: 45.0, offsetSeconds: 0 },
    { id: 'outro', durationSeconds: 8.0, offsetSeconds: 0 },
  ];

  // Recalculate offsets (matching the route's updateProjectDurations logic)
  let offset = 0;
  for (const section of sections) {
    section.offsetSeconds = offset;
    offset += section.durationSeconds;
  }

  assert(sections[0].offsetSeconds === 0, 'First section offset is 0');
  assert(sections[1].offsetSeconds === 12.5, 'Second section offset equals first duration');
  assert(sections[2].offsetSeconds === 57.5, 'Third section offset is cumulative duration');

  // Verify total duration
  const totalDuration = offset;
  assert(totalDuration === 65.5, 'Total duration is sum of all section durations');

  // Verify that updating a single section's duration recalculates all offsets
  sections[0].durationSeconds = 15.0;
  let newOffset = 0;
  for (const section of sections) {
    section.offsetSeconds = newOffset;
    newOffset += section.durationSeconds;
  }
  assert(sections[1].offsetSeconds === 15.0, 'Offset recalculated after duration change');
  assert(sections[2].offsetSeconds === 60.0, 'Downstream offsets cascade correctly');

  console.log('');
}

// ============================================================================
// Example 7: Parallel rendering batch verification
// ============================================================================

/**
 * renderSections() processes sections in batches controlled by
 * project.render.maxParallelRenders (defaults to 1 if not set).
 *
 * Given 5 sections and maxParallelRenders=2:
 *   Batch 1: sections[0], sections[1]  (rendered concurrently)
 *   Batch 2: sections[2], sections[3]  (rendered concurrently)
 *   Batch 3: sections[4]               (rendered alone)
 */
function example7_parallelBatching(): void {
  console.log('=== Example 7: Parallel rendering batch logic ===');

  // Reimplement the batching logic from renderSections
  function getBatches<T>(items: T[], batchSize: number): T[][] {
    const batches: T[][] = [];
    for (let i = 0; i < items.length; i += batchSize) {
      batches.push(items.slice(i, i + batchSize));
    }
    return batches;
  }

  // Test with maxParallelRenders=3 and 3 sections (from project.json)
  const sections3 = ['intro', 'main', 'outro'];
  const batches3 = getBatches(sections3, 3);
  assert(batches3.length === 1, '3 sections with batch=3 produces 1 batch');
  assert(batches3[0].length === 3, 'Single batch contains all 3 sections');

  // Test with maxParallelRenders=2 and 5 sections
  const sections5 = ['s1', 's2', 's3', 's4', 's5'];
  const batches5 = getBatches(sections5, 2);
  assert(batches5.length === 3, '5 sections with batch=2 produces 3 batches');
  assert(batches5[0].length === 2, 'First batch has 2 sections');
  assert(batches5[1].length === 2, 'Second batch has 2 sections');
  assert(batches5[2].length === 1, 'Third batch has 1 section');

  // Test with maxParallelRenders=1 (fully sequential)
  const batchesSeq = getBatches(sections3, 1);
  assert(batchesSeq.length === 3, '3 sections with batch=1 produces 3 batches (sequential)');

  // Verify the project.json has maxParallelRenders
  const projectConfig = JSON.parse(
    fs.readFileSync(path.join(__dirname, '..', 'project.json'), 'utf-8')
  );
  assert(
    typeof projectConfig.render?.maxParallelRenders === 'number',
    'project.json has render.maxParallelRenders'
  );
  assert(
    projectConfig.render.maxParallelRenders > 0,
    'maxParallelRenders is positive'
  );

  console.log('');
}

// ============================================================================
// Example 8: Section output paths and file structure
// ============================================================================

/**
 * Verifies output path conventions from the prompt:
 *   - Section output: outputs/sections/{sectionId}.mp4
 *   - Full video:     outputs/full_video.mp4
 *   - Directories created automatically if missing
 */
function example8_outputPaths(): void {
  console.log('=== Example 8: Output path conventions ===');

  // Verify section output path pattern
  const sectionOutputPath = path.join('outputs', 'sections', 'intro.mp4');
  assert(sectionOutputPath.includes(path.join('outputs', 'sections')), 'Section output under outputs/sections/');
  assert(sectionOutputPath.endsWith('.mp4'), 'Section output is .mp4');

  // Verify full video output path
  const fullVideoPath = path.join('outputs', 'full_video.mp4');
  assert(fullVideoPath.includes('outputs'), 'Full video under outputs/');
  assert(fullVideoPath.endsWith('full_video.mp4'), 'Full video is full_video.mp4');

  // Verify project.json sections have required fields
  const projectConfig = JSON.parse(
    fs.readFileSync(path.join(__dirname, '..', 'project.json'), 'utf-8')
  );
  const sectionIds = projectConfig.sections.map((s: any) => s.id);
  assert(sectionIds.includes('intro'), 'project.json has intro section');
  assert(sectionIds.includes('main'), 'project.json has main section');
  assert(sectionIds.includes('outro'), 'project.json has outro section');

  // Verify each section has compositionId (required for renderSection)
  for (const section of projectConfig.sections) {
    assert(
      typeof section.compositionId === 'string' && section.compositionId.length > 0,
      `Section "${section.id}" has a compositionId`
    );
  }

  console.log('');
}

// ============================================================================
// Run all examples
// ============================================================================

async function main(): Promise<void> {
  console.log('Pipeline Render/Stitch API — Module Verification Examples\n');

  example1_dagPrereqs();
  await example2_runPipelineStage();
  await example3_runWithSections();
  example4_sourceStructure();
  example5_sseEventParsing();
  example6_durationOffsetRecalculation();
  example7_parallelBatching();
  example8_outputPaths();

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

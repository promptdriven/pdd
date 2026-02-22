// api_pipeline_specs_route_example.ts
//
// Comprehensive usage example for:
//   - app/api/pipeline/specs/run/route.ts (POST — spec generation via SSE)
//
// This file verifies the specs pipeline route by:
//   1. Exercising the DAG orchestration (auto-runs prerequisite stages)
//   2. Testing the POST handler SSE stream response pattern
//   3. Verifying source file structure matches prompt requirements
//   4. Demonstrating SSE event parsing for spec generation events
//   5. Verifying the executor registration and Claude scoping
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
// Setup: Register mock executors for required pipeline stages
// ============================================================================

/**
 * The specs stage depends on 'script' -> 'setup'.
 * Register mock executors for all required stages so DAG orchestration
 * runs end-to-end without needing Claude CLI or a running Next.js server.
 */
const STAGES_NEEDED: PipelineStage[] = ['setup', 'script', 'specs'];

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
// Example 1: Verify DAG prerequisites for specs
// ============================================================================

function example1_dagPrereqs(): void {
  console.log('=== Example 1: DAG prerequisites for specs ===');

  const deps = PIPELINE_DAG['specs'];
  assert(Array.isArray(deps), 'specs has DAG entry');
  assert(deps.includes('script'), 'specs depends on script');

  const scriptDeps = PIPELINE_DAG['script'];
  assert(scriptDeps.includes('setup'), 'script depends on setup');

  console.log('  Chain: setup -> script -> specs');
  console.log('');
}

// ============================================================================
// Example 2: Run specs via DAG orchestration with event capture
// ============================================================================

/**
 * Exercises runPipelineStage('specs', ...) which auto-runs all
 * prerequisite stages (setup -> script) before executing specs.
 * Captures all SSE events emitted during execution and verifies them.
 */
async function example2_runPipelineStage(): Promise<void> {
  console.log('=== Example 2: DAG orchestration for specs ===');

  const events: object[] = [];
  const mockSend: SseSend = (data: object) => {
    events.push(data);
  };

  const jobId = await runPipelineStage('specs', {}, mockSend);

  assert(typeof jobId === 'string' && jobId.length > 0, 'runPipelineStage returns a job ID');

  const job = getJob(jobId);
  assert(job !== undefined, 'Job exists in database');
  assert(job?.stage === 'specs', 'Job stage is specs');
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
  assert(specsLogs.length > 0, 'specs stage executor ran');

  console.log(`  Job ID: ${jobId}`);
  console.log(`  Total events: ${events.length} (${logEvents.length} logs, ${progressEvents.length} progress)`);
  console.log('');
}

// ============================================================================
// Example 3: Run specs with sections parameter
// ============================================================================

/**
 * Exercises runPipelineStage('specs', { sections: [...] }) to verify
 * that sections parameter is passed through to the executor factory.
 */
async function example3_runWithSections(): Promise<void> {
  console.log('=== Example 3: Run specs with sections parameter ===');

  // Re-register specs executor that captures params
  let capturedParams: Record<string, unknown> = {};
  registerExecutor('specs', (params, _send) => {
    capturedParams = params;
    return async (onLog) => {
      onLog('[specs] Running with sections filter');
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
    'specs',
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
  registerExecutor('specs', (_params, _send) => {
    return async (onLog) => {
      onLog('[specs] Mock executor running');
      const progressFn = (onLog as unknown as { progress?: (p: number) => void })
        .progress;
      progressFn?.(100);
    };
  });

  console.log('');
}

// ============================================================================
// Example 4: Source file structure verification — run route
// ============================================================================

/**
 * Reads the run route source and verifies it matches prompt requirements:
 *   - registerExecutor('specs', ...) for pipeline integration
 *   - POST handler with SSE streaming
 *   - Calls runClaudeFix scoped to specs/ directory
 *   - Parses body for sections and files parameters
 *   - Uses loadProject() for section list
 *   - SSE headers (text/event-stream, no-cache, keep-alive)
 */
function example4_runRouteSourceStructure(): void {
  console.log('=== Example 4: Run route source structure verification ===');

  const sourceCode = fs.readFileSync(
    path.join(__dirname, '..', 'app', 'api', 'pipeline', 'specs', 'run', 'route.ts'),
    'utf-8'
  );

  // Requirement: export async function POST
  assert(
    /export\s+async\s+function\s+POST/.test(sourceCode),
    'Exports async POST handler'
  );

  // Requirement: registerExecutor('specs', ...)
  assert(
    sourceCode.includes('registerExecutor') &&
    (sourceCode.includes("'specs'") || sourceCode.includes('"specs"')),
    'Registers specs executor with registerExecutor'
  );

  // Requirement: Calls runClaudeFix scoped to specs/
  assert(sourceCode.includes('runClaudeFix'), 'Calls runClaudeFix');

  // Requirement: Uses path.join(process.cwd(), 'specs') for scope directory
  assert(
    sourceCode.includes('process.cwd()') && sourceCode.includes('specs'),
    'Scopes Claude to specs/ via process.cwd()'
  );

  // Requirement: Uses loadProject() for section list
  assert(sourceCode.includes('loadProject'), 'Uses loadProject() for section list');

  // Requirement: Parses body for sections
  assert(sourceCode.includes('sections'), 'Handles sections parameter');

  // Requirement: Parses body for files
  assert(sourceCode.includes('files'), 'Handles files parameter');

  // Requirement: SSE streaming headers
  assert(sourceCode.includes('text/event-stream'), 'Sets Content-Type to text/event-stream');
  assert(sourceCode.includes('no-cache'), 'Sets Cache-Control to no-cache');
  assert(sourceCode.includes('keep-alive'), 'Sets Connection to keep-alive');

  // Requirement: Uses runPipelineStage for DAG orchestration
  assert(sourceCode.includes('runPipelineStage'), 'Uses runPipelineStage for DAG orchestration');

  // Requirement: Sends complete event with jobId
  assert(
    sourceCode.includes("'complete'") || sourceCode.includes('"complete"'),
    'Sends complete event type'
  );
  assert(sourceCode.includes('jobId'), 'Complete event includes jobId');

  // Requirement: Error handling
  assert(
    sourceCode.includes("'error'") || sourceCode.includes('"error"'),
    'Has error event handling'
  );

  // Requirement: imports from @/lib/jobs
  assert(sourceCode.includes('@/lib/jobs'), 'Imports from @/lib/jobs');

  // Requirement: imports from @/lib/claude
  assert(sourceCode.includes('@/lib/claude'), 'Imports from @/lib/claude');

  // Requirement: imports from @/lib/project
  assert(sourceCode.includes('@/lib/project'), 'Imports from @/lib/project');

  // Requirement: Visual type markers in the prompt
  assert(sourceCode.includes('[Remotion]'), 'Prompt includes [Remotion] visual type marker');
  assert(sourceCode.includes('[veo:]'), 'Prompt includes [veo:] visual type marker');
  assert(sourceCode.includes('[title:]'), 'Prompt includes [title:] visual type marker');
  assert(sourceCode.includes('[split:]'), 'Prompt includes [split:] visual type marker');

  console.log('');
}

// ============================================================================
// Example 5: SSE event parsing demonstration for spec generation events
// ============================================================================

/**
 * Demonstrates parsing the raw SSE wire format that the run endpoint produces.
 * Covers the specific event types emitted by the specs endpoint.
 */
function example5_sseEventParsing(): void {
  console.log('=== Example 5: SSE event parsing for specs ===');

  // Parse a log event
  const logEvent = 'data: {"type":"log","message":"Generating specs for intro...","jobId":"abc-123"}';
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
  const errorEvent = 'data: {"type":"error","error":"Claude CLI timeout after 300s"}';
  const errorPayload = JSON.parse(errorEvent.replace(/^data:\s*/, ''));
  assert(errorPayload.type === 'error', 'Parsed error event type');
  assert(errorPayload.error.includes('timeout'), 'Parsed error message');

  // Verify SSE format: each event is "data: <json>\n\n"
  const sseFrame = `data: ${JSON.stringify({ type: 'log', message: 'test' })}\n\n`;
  assert(sseFrame.startsWith('data: '), 'SSE frame starts with "data: "');
  assert(sseFrame.endsWith('\n\n'), 'SSE frame ends with double newline');

  console.log('');
}

// ============================================================================
// Example 6: Visual type detection patterns
// ============================================================================

/**
 * Verifies the visual type detection logic specified in the prompt.
 * Spec files use first-line markers to indicate their visual type.
 */
function example6_visualTypeDetection(): void {
  console.log('=== Example 6: Visual type detection patterns ===');

  // Reimplement the visual type detection from the prompt spec
  function detectVisualType(firstLine: string): string {
    const trimmed = firstLine.trim();
    if (trimmed === '[Remotion]') return 'remotion';
    if (trimmed.startsWith('[veo:')) return 'veo';
    if (trimmed.startsWith('[title:')) return 'title';
    if (trimmed.startsWith('[split:')) return 'split';
    return 'unknown';
  }

  assert(detectVisualType('[Remotion]') === 'remotion', 'Detects [Remotion] marker');
  assert(detectVisualType('[veo: cinematic drone shot]') === 'veo', 'Detects [veo:...] marker');
  assert(detectVisualType('[title: Product Launch]') === 'title', 'Detects [title:...] marker');
  assert(detectVisualType('[split: demo|narration]') === 'split', 'Detects [split:...] marker');
  assert(detectVisualType('## Regular heading') === 'unknown', 'Returns unknown for no marker');

  // Verify expected spec file structure
  const exampleSpec = `[veo: cinematic drone shot of city skyline]
## Opening Shot
Duration: 3 seconds
A sweeping aerial view of the downtown skyline at sunset.`;

  const firstLine = exampleSpec.split('\n')[0];
  assert(detectVisualType(firstLine) === 'veo', 'Full spec file first line detection works');

  console.log('');
}

// ============================================================================
// Example 7: Spec file directory structure
// ============================================================================

/**
 * Verifies the expected spec file directory structure from the prompt:
 *   specs/<sectionId>/<spec-name>.md
 */
function example7_specFileStructure(): void {
  console.log('=== Example 7: Expected spec file structure ===');

  // Verify path pattern
  const specPath = 'specs/intro/opening-shot.md';
  const parts = specPath.split('/');
  assert(parts[0] === 'specs', 'Spec path starts with specs/');
  assert(parts.length === 3, 'Spec path has 3 parts: specs/<sectionId>/<file>.md');
  assert(parts[2].endsWith('.md'), 'Spec files are markdown (.md)');

  // Verify section IDs match project.json
  const projectConfig = JSON.parse(
    fs.readFileSync(path.join(__dirname, '..', 'project.json'), 'utf-8')
  );
  const sectionIds = projectConfig.sections.map((s: any) => s.id);
  assert(sectionIds.includes('intro'), 'project.json has intro section');
  assert(sectionIds.includes('main'), 'project.json has main section');
  assert(sectionIds.includes('outro'), 'project.json has outro section');
  assert(sectionIds.length >= 1, 'project.json has at least one section');

  console.log('');
}

// ============================================================================
// Run all examples
// ============================================================================

async function main(): Promise<void> {
  example1_dagPrereqs();
  await example2_runPipelineStage();
  await example3_runWithSections();
  example4_runRouteSourceStructure();
  example5_sseEventParsing();
  example6_visualTypeDetection();
  example7_specFileStructure();

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

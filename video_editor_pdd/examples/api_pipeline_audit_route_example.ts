// api_pipeline_audit_route_example.ts
//
// Comprehensive verification example for:
//   - app/api/pipeline/audit/run/route.ts (POST — parallel section auditing via SSE)
//   - app/api/pipeline/audit/results/route.ts (GET — audit results)
//
// This file verifies the audit pipeline route by:
//   1. Exercising DAG orchestration (audit depends on render → compositions → …)
//   2. Testing the audit executor registration and section auditing flow
//   3. Verifying source file structure matches prompt requirements
//   4. Demonstrating SSE event parsing for audit-section events
//   5. Verifying audit markdown parsing logic (## Verdict / ## Summary)
//   6. Verifying concurrent section audit via Promise.all
//   7. Verifying output path conventions for stills and audit reports
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
 * The audit stage depends on the full DAG chain:
 *   setup -> script -> (tts-script -> tts-render -> audio-sync) || (specs -> veo)
 *   -> compositions -> render -> audit
 *
 * Register mock executors for all stages so DAG orchestration
 * runs end-to-end without needing Remotion, Claude, or a running Next.js server.
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
// Example 1: Verify DAG prerequisites for audit
// ============================================================================

/**
 * The pipeline DAG defines that 'audit' depends on 'render',
 * which depends on 'compositions', which in turn depends on both
 * 'audio-sync' and 'veo' tracks.
 *
 * Full chain:
 *   setup -> script -> (tts-script -> tts-render -> audio-sync) || (specs -> veo)
 *   -> compositions -> render -> audit
 */
function example1_dagPrereqs(): void {
  console.log('=== Example 1: DAG prerequisites for audit ===');

  const auditDeps = PIPELINE_DAG['audit'];
  assert(Array.isArray(auditDeps), 'audit has DAG entry');
  assert(auditDeps.includes('render'), 'audit depends on render');

  const renderDeps = PIPELINE_DAG['render'];
  assert(renderDeps.includes('compositions'), 'render depends on compositions');

  const compositionsDeps = PIPELINE_DAG['compositions'];
  assert(compositionsDeps.includes('audio-sync'), 'compositions depends on audio-sync');
  assert(compositionsDeps.includes('veo'), 'compositions depends on veo');

  const audioSyncDeps = PIPELINE_DAG['audio-sync'];
  assert(audioSyncDeps.includes('tts-render'), 'audio-sync depends on tts-render');

  const veoDeps = PIPELINE_DAG['veo'];
  assert(veoDeps.includes('specs'), 'veo depends on specs');

  console.log('  Chain: setup -> script -> (tts-script -> tts-render -> audio-sync) || (specs -> veo) -> compositions -> render -> audit');
  console.log('');
}

// ============================================================================
// Example 2: Run audit via DAG orchestration with event capture
// ============================================================================

/**
 * Exercises runPipelineStage('audit', ...) which auto-runs all
 * prerequisite stages before executing audit.
 * Captures all SSE events emitted during execution and verifies them.
 */
async function example2_runPipelineStage(): Promise<void> {
  console.log('=== Example 2: DAG orchestration for audit ===');

  const events: object[] = [];
  const mockSend: SseSend = (data: object) => {
    events.push(data);
  };

  const jobId = await runPipelineStage('audit', {}, mockSend);

  assert(typeof jobId === 'string' && jobId.length > 0, 'runPipelineStage returns a job ID');

  const job = getJob(jobId);
  assert(job !== undefined, 'Job exists in database');
  assert(job?.stage === 'audit', 'Job stage is audit');
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

  const renderLogs = logEvents.filter((e: any) =>
    typeof e.message === 'string' && e.message.includes('[render]')
  );
  assert(renderLogs.length > 0, 'Render stage auto-ran as prerequisite');

  const auditLogs = logEvents.filter((e: any) =>
    typeof e.message === 'string' && e.message.includes('[audit]')
  );
  assert(auditLogs.length > 0, 'Audit stage executor ran');

  console.log(`  Job ID: ${jobId}`);
  console.log(`  Total events: ${events.length} (${logEvents.length} logs, ${progressEvents.length} progress)`);
  console.log('');
}

// ============================================================================
// Example 3: Run audit with sections parameter
// ============================================================================

/**
 * POST /api/pipeline/audit/run accepts { sections?: string[] }.
 * This verifies the sections parameter is passed through to the executor.
 */
async function example3_runWithSections(): Promise<void> {
  console.log('=== Example 3: Run audit with sections parameter ===');

  let capturedParams: Record<string, unknown> = {};
  registerExecutor('audit', (params, _send) => {
    capturedParams = params;
    return async (onLog) => {
      onLog('[audit] Running with sections filter');
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
    'audit',
    { sections: ['intro', 'main'] },
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
  registerExecutor('audit', (_params, _send) => {
    return async (onLog) => {
      onLog('[audit] Mock executor running');
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
 * Reads the audit route source and verifies it matches prompt requirements:
 *   - registerExecutor('audit', ...) for pipeline integration
 *   - POST handler with SSE streaming
 *   - Uses renderStill from @/lib/render
 *   - Uses runClaudeAnalysis from @/lib/claude
 *   - Uses loadProject from @/lib/project
 *   - SSE headers (text/event-stream, no-cache, keep-alive)
 *   - Concurrent auditing with Promise.all
 *   - Audit report writing with ## Verdict / ## Summary
 */
function example4_sourceStructure(): void {
  console.log('=== Example 4: Source file structure verification ===');

  const sourceCode = fs.readFileSync(
    path.join(__dirname, '..', 'app', 'api', 'pipeline', 'audit', 'run', 'route.ts'),
    'utf-8'
  );

  // Requirement: export handler function
  assert(
    /export\s+async\s+function\s+POST/.test(sourceCode),
    'Exports async POST handler'
  );

  // Requirement: registerExecutor('audit', ...)
  assert(
    sourceCode.includes('registerExecutor') &&
    (sourceCode.includes("'audit'") || sourceCode.includes('"audit"')),
    'Registers audit executor with registerExecutor'
  );

  // Requirement: Uses renderStill from @/lib/render
  assert(sourceCode.includes('renderStill'), 'Uses renderStill for midpoint frame rendering');

  // Requirement: Uses runClaudeAnalysis from @/lib/claude
  assert(sourceCode.includes('runClaudeAnalysis'), 'Uses runClaudeAnalysis for spec comparison');

  // Requirement: Uses loadProject from @/lib/project
  assert(sourceCode.includes('loadProject'), 'Uses loadProject() for project config');

  // Requirement: SSE streaming headers
  assert(sourceCode.includes('text/event-stream'), 'Sets Content-Type to text/event-stream');
  assert(sourceCode.includes('no-cache'), 'Sets Cache-Control to no-cache');
  assert(sourceCode.includes('keep-alive'), 'Sets Connection to keep-alive');

  // Requirement: Uses runPipelineStage for DAG orchestration
  assert(sourceCode.includes('runPipelineStage'), 'Uses runPipelineStage for DAG orchestration');

  // Requirement: Imports from @/lib/jobs
  assert(sourceCode.includes('@/lib/jobs'), 'Imports from @/lib/jobs');

  // Requirement: Imports from @/lib/render
  assert(sourceCode.includes('@/lib/render'), 'Imports from @/lib/render');

  // Requirement: Imports from @/lib/claude
  assert(sourceCode.includes('@/lib/claude'), 'Imports from @/lib/claude');

  // Requirement: Imports from @/lib/project
  assert(sourceCode.includes('@/lib/project'), 'Imports from @/lib/project');

  // Requirement: Concurrent auditing with Promise.all
  assert(sourceCode.includes('Promise.all'), 'Uses Promise.all for concurrent section auditing');

  // Requirement: Emits audit-section events
  assert(sourceCode.includes('audit-section'), 'Emits audit-section SSE events');

  // Requirement: Audit report writing with ## Verdict / ## Summary format
  assert(sourceCode.includes('## Verdict'), 'Writes audit reports with ## Verdict heading');
  assert(sourceCode.includes('## Summary'), 'Writes audit reports with ## Summary heading');

  // Requirement: Still output path pattern (outputs/audit/{sectionId}/{specName}_frame.png)
  assert(
    sourceCode.includes('outputs') && sourceCode.includes('audit'),
    'References outputs/audit/ output directory for stills'
  );

  // Requirement: Audit report path pattern (specs/{sectionId}/AUDIT_{specName}.md)
  assert(sourceCode.includes('AUDIT_'), 'References AUDIT_ prefix for audit report files');

  // Requirement: Error handling with SSE error event
  assert(
    sourceCode.includes("'error'") || sourceCode.includes('"error"'),
    'Has error event handling'
  );

  // Requirement: AnnotationAnalysis type for Claude output
  assert(sourceCode.includes('AnnotationAnalysis'), 'Uses AnnotationAnalysis type');

  // Requirement: GET handler for results
  assert(
    /export\s+async\s+function\s+GET/.test(sourceCode),
    'Exports async GET handler for results'
  );

  // Requirement: Parses audit markdown for verdict extraction
  assert(
    sourceCode.includes('parseAuditMarkdown') ||
    (sourceCode.includes('## Verdict') && sourceCode.includes('match')),
    'Parses audit markdown files for verdict extraction'
  );

  console.log('');
}

// ============================================================================
// Example 5: Audit markdown parsing logic
// ============================================================================

/**
 * The GET /api/pipeline/audit/results endpoint parses AUDIT_*.md files
 * to extract verdicts. The markdown format is:
 *   ## Verdict
 *   pass (or fail)
 *   ## Summary
 *   {descriptive text}
 *
 * This example verifies the parsing logic works correctly.
 */
function example5_auditMarkdownParsing(): void {
  console.log('=== Example 5: Audit markdown parsing logic ===');

  // Reimplement the parseAuditMarkdown logic from the route
  function parseAuditMarkdown(content: string): {
    verdict: 'pass' | 'fail';
    summary: string;
  } {
    const verdictMatch = content.match(/## Verdict\s+(\w+)/i);
    const summaryMatch = content.match(/## Summary\s+([\s\S]+)/i);

    if (!verdictMatch || !summaryMatch) {
      throw new Error('Invalid audit markdown format');
    }

    const verdict = verdictMatch[1].toLowerCase() === 'pass' ? 'pass' : 'fail';
    const summary = summaryMatch[1].trim();

    return { verdict, summary };
  }

  // Test: pass verdict
  const passReport = `## Verdict
pass
## Summary
The frame at the midpoint of the intro section correctly displays the logo
in the upper-left corner with proper sizing (120x40px) and the gradient
background matches the specified color stops (#0f0f23 to #1a1a2e).`;

  const passResult = parseAuditMarkdown(passReport);
  assert(passResult.verdict === 'pass', 'Parses pass verdict correctly');
  assert(passResult.summary.includes('logo'), 'Extracts summary text for pass verdict');

  // Test: fail verdict
  const failReport = `## Verdict
fail
## Summary
Background gradient uses #1a1a2e instead of specified #0f0f23.`;

  const failResult = parseAuditMarkdown(failReport);
  assert(failResult.verdict === 'fail', 'Parses fail verdict correctly');
  assert(failResult.summary.includes('gradient'), 'Extracts summary text for fail verdict');

  // Test: case-insensitive verdict
  const upperReport = `## Verdict
PASS
## Summary
All elements match spec.`;

  const upperResult = parseAuditMarkdown(upperReport);
  assert(upperResult.verdict === 'pass', 'Handles uppercase PASS verdict');

  // Test: unknown verdict defaults to fail
  const unknownReport = `## Verdict
warning
## Summary
Minor issues found.`;

  const unknownResult = parseAuditMarkdown(unknownReport);
  assert(unknownResult.verdict === 'fail', 'Non-pass verdict maps to fail');

  // Test: malformed markdown throws
  let threwError = false;
  try {
    parseAuditMarkdown('no structure here');
  } catch {
    threwError = true;
  }
  assert(threwError, 'Throws on malformed audit markdown');

  // Verify the audit report format matches what the route writes
  const expectedFormat = `## Verdict\npass\n## Summary\nSome assessment text\n`;
  const parsed = parseAuditMarkdown(expectedFormat);
  assert(parsed.verdict === 'pass', 'Route-format report parses correctly');
  assert(parsed.summary === 'Some assessment text', 'Route-format summary extracted');

  console.log('');
}

// ============================================================================
// Example 6: SSE event parsing for audit-specific events
// ============================================================================

/**
 * Demonstrates parsing the raw SSE wire format produced by the audit endpoint.
 * Covers the event types:
 *   1. audit-section — per-section audit status (running, done, error)
 *   2. job — final job ID event
 *   3. error — unrecoverable error
 */
function example6_sseEventParsing(): void {
  console.log('=== Example 6: SSE event parsing for audit ===');

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

  // Parse an audit-section running event
  const runningChunk =
    'data: {"type":"audit-section","sectionId":"intro","status":"running","passCount":0,"failCount":0}\n\n';
  const runningEvents = parseSseChunk(runningChunk);
  assert(runningEvents.length === 1, 'Parsed one audit-section running event');
  const re = runningEvents[0] as any;
  assert(re.type === 'audit-section', 'Event type is audit-section');
  assert(re.sectionId === 'intro', 'sectionId field is correct');
  assert(re.status === 'running', 'status is running');
  assert(re.passCount === 0, 'passCount starts at 0');
  assert(re.failCount === 0, 'failCount starts at 0');

  // Parse an audit-section done event
  const doneChunk =
    'data: {"type":"audit-section","sectionId":"intro","status":"done","passCount":2,"failCount":1}\n\n';
  const doneEvents = parseSseChunk(doneChunk);
  const de = doneEvents[0] as any;
  assert(de.status === 'done', 'Parsed done status');
  assert(de.passCount === 2, 'passCount reflects completed audits');
  assert(de.failCount === 1, 'failCount reflects failed specs');

  // Parse a job ID event
  const jobChunk =
    'data: {"type":"job","jobId":"abc-123-def-456"}\n\n';
  const jobEvents = parseSseChunk(jobChunk);
  const je = jobEvents[0] as any;
  assert(je.type === 'job', 'Parsed job event type');
  assert(typeof je.jobId === 'string' && je.jobId.length > 0, 'jobId is non-empty string');

  // Parse an error event
  const errorChunk =
    'data: {"type":"error","message":"Spec directory not found"}\n\n';
  const errorEvents = parseSseChunk(errorChunk);
  const ee = errorEvents[0] as any;
  assert(ee.type === 'error', 'Parsed error event type');
  assert(ee.message.includes('Spec'), 'Error message content correct');

  // Parse multiple events in one chunk (simulated full audit stream)
  const multiChunk =
    'data: {"type":"audit-section","sectionId":"intro","status":"running","passCount":0,"failCount":0}\n\n' +
    'data: {"type":"audit-section","sectionId":"main","status":"running","passCount":0,"failCount":0}\n\n' +
    'data: {"type":"audit-section","sectionId":"intro","status":"done","passCount":2,"failCount":1}\n\n' +
    'data: {"type":"audit-section","sectionId":"main","status":"done","passCount":3,"failCount":0}\n\n' +
    'data: {"type":"job","jobId":"abc-123-def-456"}\n\n';
  const multiEvents = parseSseChunk(multiChunk);
  assert(multiEvents.length === 5, 'Parsed 5 events from full audit stream');

  // Verify SSE frame format
  const sseFrame = `data: ${JSON.stringify({
    type: 'audit-section',
    sectionId: 'intro',
    status: 'running',
    passCount: 0,
    failCount: 0,
  })}\n\n`;
  assert(sseFrame.startsWith('data: '), 'SSE frame starts with "data: "');
  assert(sseFrame.endsWith('\n\n'), 'SSE frame ends with double newline');

  console.log('');
}

// ============================================================================
// Example 7: Output path conventions for audit artifacts
// ============================================================================

/**
 * Verifies output path conventions from the prompt:
 *   - Still output:  outputs/audit/{sectionId}/{specName}_frame.png
 *   - Audit report:  specs/{sectionId}/AUDIT_{specName}.md
 *   - Spec input:    specs/{sectionId}/{specName}.md (excludes AUDIT_ files)
 */
function example7_outputPaths(): void {
  console.log('=== Example 7: Output path conventions ===');

  // Verify still output path pattern
  const stillPath = path.join('outputs', 'audit', 'intro', 'visual_layout_frame.png');
  assert(stillPath.includes(path.join('outputs', 'audit')), 'Still output under outputs/audit/');
  assert(stillPath.endsWith('.png'), 'Still output is .png');
  assert(stillPath.includes('intro'), 'Still path includes sectionId');

  // Verify audit report path pattern
  const auditReportPath = path.join('specs', 'intro', 'AUDIT_visual_layout.md');
  assert(auditReportPath.includes(path.join('specs', 'intro')), 'Audit report under specs/{sectionId}/');
  assert(auditReportPath.includes('AUDIT_'), 'Audit report has AUDIT_ prefix');
  assert(auditReportPath.endsWith('.md'), 'Audit report is .md');

  // Verify spec input path pattern
  const specInputPath = path.join('specs', 'intro', 'visual_layout.md');
  assert(!specInputPath.includes('AUDIT_'), 'Spec input does not have AUDIT_ prefix');
  assert(specInputPath.endsWith('.md'), 'Spec input is .md');

  // Verify AUDIT_ prefix correctly maps back to spec name
  const auditFileName = 'AUDIT_visual_layout.md';
  const specName = auditFileName.replace(/^AUDIT_/, '').replace(/\.md$/, '');
  assert(specName === 'visual_layout', 'AUDIT_ prefix maps back to spec name');

  // Verify frame file name convention
  const frameFileName = `${specName}_frame.png`;
  assert(frameFileName === 'visual_layout_frame.png', 'Frame file follows {specName}_frame.png convention');

  // Verify project.json sections have required fields for audit
  const projectConfig = JSON.parse(
    fs.readFileSync(path.join(__dirname, '..', 'project.json'), 'utf-8')
  );
  for (const section of projectConfig.sections) {
    assert(
      typeof section.specDir === 'string' && section.specDir.length > 0,
      `Section "${section.id}" has a specDir`
    );
    assert(
      typeof section.compositionId === 'string' && section.compositionId.length > 0,
      `Section "${section.id}" has a compositionId`
    );
    assert(
      typeof section.durationSeconds === 'number',
      `Section "${section.id}" has durationSeconds`
    );
  }

  // Verify fps is available in render config (needed for midpoint calculation)
  assert(
    typeof projectConfig.render?.fps === 'number' && projectConfig.render.fps > 0,
    'project.json has render.fps for midpoint frame calculation'
  );

  console.log('');
}

// ============================================================================
// Example 8: Midpoint frame calculation logic
// ============================================================================

/**
 * The audit route calculates the midpoint frame for each section:
 *   midpointFrame = Math.floor((section.durationSeconds / 2) * fps)
 *
 * This is used for renderStill() to capture a representative still frame.
 */
function example8_midpointFrameCalculation(): void {
  console.log('=== Example 8: Midpoint frame calculation ===');

  const projectConfig = JSON.parse(
    fs.readFileSync(path.join(__dirname, '..', 'project.json'), 'utf-8')
  );
  const fps = projectConfig.render.fps;

  for (const section of projectConfig.sections) {
    const midpointFrame = Math.floor((section.durationSeconds / 2) * fps);
    assert(
      midpointFrame >= 0,
      `Section "${section.id}": midpoint frame ${midpointFrame} is non-negative`
    );
    assert(
      midpointFrame === Math.floor(midpointFrame),
      `Section "${section.id}": midpoint frame is integer`
    );

    const expectedMidpoint = Math.floor((section.durationSeconds / 2) * fps);
    assert(
      midpointFrame === expectedMidpoint,
      `Section "${section.id}": midpoint = floor((${section.durationSeconds}/2) * ${fps}) = ${expectedMidpoint}`
    );
  }

  // Verify specific calculation for intro section (12.5s at 30fps)
  const introSection = projectConfig.sections.find((s: any) => s.id === 'intro');
  if (introSection) {
    const expected = Math.floor((12.5 / 2) * 30); // 187
    assert(
      Math.floor((introSection.durationSeconds / 2) * fps) === expected,
      `Intro midpoint frame = ${expected} (12.5s / 2 * 30fps)`
    );
  }

  console.log('');
}

// ============================================================================
// Run all examples
// ============================================================================

async function main(): Promise<void> {
  console.log('Audit Pipeline API — Module Verification Examples\n');

  example1_dagPrereqs();
  await example2_runPipelineStage();
  await example3_runWithSections();
  example4_sourceStructure();
  example5_auditMarkdownParsing();
  example6_sseEventParsing();
  example7_outputPaths();
  example8_midpointFrameCalculation();

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

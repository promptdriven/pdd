// example_usage.ts
// Comprehensive usage example for app/api/annotations/[id]/analyze/route.ts
//
// This file verifies the POST annotation analysis route by:
//   1. Importing and calling the actual POST handler from route.ts
//   2. Mocking runClaudeAnalysis to return a deterministic result
//   3. Testing success (200), not-found (404), and missing-composite (500)
//   4. Verifying exported constants match prompt requirements
//   5. Verifying source file structure matches prompt requirements
//
// For standalone execution, an in-memory SQLite database is used
// and the @/ module path alias is resolved at runtime.

// ---------------------------------------------------------------------------
// 0. Environment setup (must run before any module that calls getDb())
// ---------------------------------------------------------------------------
process.env.DB_PATH = ':memory:';

// Register @/ path alias so route.ts's `import { getDb } from "@/lib/db"`
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
// 1. Mock runClaudeAnalysis before loading the route module
// ---------------------------------------------------------------------------
const claudeModule = require('../lib/claude');

const mockAnalysis = {
  severity: 'major' as const,
  fixType: 'remotion' as const,
  technicalAssessment: 'Text overlay at 3.2s is clipped by the safe-zone boundary.',
  suggestedFixes: ['Reduce font size from 48px to 40px', 'Adjust text position inward by 20px'],
  confidence: 0.87,
};

claudeModule.runClaudeAnalysis = async function mockRunClaudeAnalysis(
  _prompt: string,
  onLog?: (line: string) => void
) {
  if (onLog) {
    onLog('[mock] Starting analysis...');
    onLog('[mock] Analysis complete');
  }
  return mockAnalysis;
};

// ---------------------------------------------------------------------------
// 2. Imports (safe now that alias is registered and mock is in place)
// ---------------------------------------------------------------------------
import fs from 'fs';
import path from 'path';
import { getDb } from '../lib/db';

// Dynamic require of route module (must be after alias registration and mock)
const routeModule = require('../app/api/annotations/[id]/analyze/route') as {
  POST: (request: Request, context: { params: { id: string } }) => Promise<Response>;
  dynamic: string;
};

// ---------------------------------------------------------------------------
// 3. Assertion helper
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
// Helper: seed an annotation directly in the DB
// ---------------------------------------------------------------------------
function seedAnnotation(opts: {
  id: string;
  sectionId: string;
  timestamp: number;
  text: string;
  videoFile?: string | null;
  drawingDataUrl?: string | null;
  compositeDataUrl?: string | null;
  analysis?: object | null;
  resolved?: boolean;
  resolveJobId?: string | null;
}): void {
  const db = getDb();
  const now = new Date().toISOString();

  db.prepare(
    `INSERT INTO annotations (id, sectionId, timestamp, text, videoFile, drawingDataUrl, compositeDataUrl, analysis, resolved, resolveJobId, createdAt)
     VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)`
  ).run(
    opts.id,
    opts.sectionId,
    opts.timestamp,
    opts.text,
    opts.videoFile ?? null,
    opts.drawingDataUrl ?? null,
    opts.compositeDataUrl ?? null,
    opts.analysis ? JSON.stringify(opts.analysis) : null,
    opts.resolved ? 1 : 0,
    opts.resolveJobId ?? null,
    now
  );
}

// ---------------------------------------------------------------------------
// Example 1: Successful analysis (200 OK)
// ---------------------------------------------------------------------------

async function example1_successfulAnalysis(): Promise<void> {
  console.log('=== Example 1: Successful analysis (200 OK) ===');

  const annId = 'ann-analyze-001';
  seedAnnotation({
    id: annId,
    sectionId: 'intro',
    timestamp: 3.2,
    text: 'Text is cut off on the right side',
    videoFile: 'output/sections/intro.mp4',
    compositeDataUrl: 'data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
  });

  // Suppress Claude log lines during test
  const origLog = console.log;
  const logLines: string[] = [];
  const origConsoleLog = console.log;

  const request = new Request('http://localhost/api/annotations/' + annId + '/analyze', {
    method: 'POST',
  });
  const response = await routeModule.POST(request, { params: { id: annId } });

  assert(response.status === 200, 'Response status is 200');

  const contentType = response.headers.get('Content-Type');
  assert(
    contentType !== null && contentType.includes('application/json'),
    `Content-Type is application/json (got: ${contentType})`
  );

  const body = await response.json();

  // Verify response shape: { annotation: Annotation }
  assert(body.annotation !== undefined, 'Response has annotation key');
  assert(body.annotation.id === annId, `annotation.id matches: ${body.annotation.id}`);
  assert(body.annotation.sectionId === 'intro', 'annotation.sectionId is "intro"');
  assert(body.annotation.text === 'Text is cut off on the right side', 'annotation.text matches');

  // Verify analysis was populated
  assert(body.annotation.analysis !== null, 'analysis is not null after analysis');
  assert(body.annotation.analysis.severity === 'major', 'analysis.severity is "major"');
  assert(body.annotation.analysis.fixType === 'remotion', 'analysis.fixType is "remotion"');
  assert(typeof body.annotation.analysis.technicalAssessment === 'string', 'analysis.technicalAssessment is a string');
  assert(Array.isArray(body.annotation.analysis.suggestedFixes), 'analysis.suggestedFixes is an array');
  assert(body.annotation.analysis.suggestedFixes.length === 2, 'analysis.suggestedFixes has 2 entries');
  assert(body.annotation.analysis.confidence === 0.87, 'analysis.confidence is 0.87');

  // Verify the DB was updated (re-read from DB directly)
  const db = getDb();
  const dbRow = db.prepare('SELECT analysis FROM annotations WHERE id = ?').get(annId) as { analysis: string };
  assert(dbRow.analysis !== null, 'DB analysis column is not null');
  const dbAnalysis = JSON.parse(dbRow.analysis);
  assert(dbAnalysis.severity === 'major', 'DB analysis.severity matches');

  console.log('\n  Response body:');
  console.log(`    id:          ${body.annotation.id}`);
  console.log(`    sectionId:   ${body.annotation.sectionId}`);
  console.log(`    severity:    ${body.annotation.analysis.severity}`);
  console.log(`    fixType:     ${body.annotation.analysis.fixType}`);
  console.log(`    confidence:  ${body.annotation.analysis.confidence}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 2: Annotation not found (404)
// ---------------------------------------------------------------------------

async function example2_notFound(): Promise<void> {
  console.log('=== Example 2: Annotation not found (404) ===');

  const fakeId = 'nonexistent-id-999';

  const request = new Request('http://localhost/api/annotations/' + fakeId + '/analyze', {
    method: 'POST',
  });
  const response = await routeModule.POST(request, { params: { id: fakeId } });

  assert(response.status === 404, 'Response status is 404');

  const body = await response.json();
  assert(body.error === 'Annotation not found', `error message is "Annotation not found" (got: "${body.error}")`);

  console.log(`  Response: ${JSON.stringify(body)}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 3: Annotation without compositeDataUrl (500)
// ---------------------------------------------------------------------------

async function example3_noComposite(): Promise<void> {
  console.log('=== Example 3: Missing compositeDataUrl (500) ===');

  const annId = 'ann-analyze-no-composite';
  seedAnnotation({
    id: annId,
    sectionId: 'main',
    timestamp: 10.0,
    text: 'Color grading looks off',
    compositeDataUrl: null,
  });

  // Suppress console.error during this test
  const origConsoleError = console.error;
  console.error = () => {};

  const request = new Request('http://localhost/api/annotations/' + annId + '/analyze', {
    method: 'POST',
  });
  const response = await routeModule.POST(request, { params: { id: annId } });

  // Restore console.error
  console.error = origConsoleError;

  assert(response.status === 500, 'Response status is 500');

  const body = await response.json();
  assert(body.error === 'Internal Server Error', `error message is "Internal Server Error" (got: "${body.error}")`);

  console.log(`  Response: ${JSON.stringify(body)}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 4: Verify analysis updates DB and re-reads (full round trip)
// ---------------------------------------------------------------------------

async function example4_dbRoundTrip(): Promise<void> {
  console.log('=== Example 4: DB round-trip verification ===');

  const annId = 'ann-analyze-roundtrip';
  seedAnnotation({
    id: annId,
    sectionId: 'outro',
    timestamp: 5.0,
    text: 'Fade-out is too abrupt',
    videoFile: 'output/sections/outro.mp4',
    compositeDataUrl: 'data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
    analysis: null,
  });

  // Verify analysis is null before
  const db = getDb();
  const before = db.prepare('SELECT analysis FROM annotations WHERE id = ?').get(annId) as { analysis: string | null };
  assert(before.analysis === null, 'analysis is null before POST');

  const request = new Request('http://localhost/api/annotations/' + annId + '/analyze', {
    method: 'POST',
  });
  const response = await routeModule.POST(request, { params: { id: annId } });

  assert(response.status === 200, 'Response status is 200');

  // Verify analysis is populated after
  const after = db.prepare('SELECT analysis FROM annotations WHERE id = ?').get(annId) as { analysis: string | null };
  assert(after.analysis !== null, 'analysis is not null after POST');

  const parsed = JSON.parse(after.analysis!);
  assert(parsed.severity === 'major', 'DB analysis.severity is "major"');
  assert(parsed.fixType === 'remotion', 'DB analysis.fixType is "remotion"');
  assert(parsed.confidence === 0.87, 'DB analysis.confidence is 0.87');

  // Verify returned annotation matches DB
  const body = await response.json();
  assert(body.annotation.analysis.severity === parsed.severity, 'Response analysis matches DB');

  console.log(`  Before: analysis=${before.analysis}`);
  console.log(`  After:  analysis.severity=${parsed.severity}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 5: Exported constants verification
// ---------------------------------------------------------------------------

function example5_exports(): void {
  console.log('=== Example 5: Exported constants ===');

  assert(routeModule.dynamic === 'force-dynamic', 'dynamic export is "force-dynamic"');
  assert(typeof routeModule.POST === 'function', 'POST is an exported function');

  console.log(`  dynamic: ${routeModule.dynamic}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 6: Source file structure verification
// ---------------------------------------------------------------------------

function example6_sourceStructure(): void {
  console.log('=== Example 6: Source file structure verification ===');

  const sourceCode = fs.readFileSync(
    path.join(__dirname, '..', 'app', 'api', 'annotations', '[id]', 'analyze', 'route.ts'),
    'utf-8'
  );

  // Requirement: POST handler
  assert(
    /export\s+async\s+function\s+POST/.test(sourceCode),
    'Exports async POST handler'
  );

  // Requirement: force-dynamic
  assert(
    sourceCode.includes('force-dynamic'),
    'Exports dynamic = "force-dynamic"'
  );

  // Requirement: Imports getDb from @/lib/db
  assert(
    sourceCode.includes('getDb') && sourceCode.includes('@/lib/db'),
    'Imports getDb from @/lib/db'
  );

  // Requirement: Imports runClaudeAnalysis from @/lib/claude
  assert(
    sourceCode.includes('runClaudeAnalysis') && sourceCode.includes('@/lib/claude'),
    'Imports runClaudeAnalysis from @/lib/claude'
  );

  // Requirement: NextResponse.json
  assert(
    sourceCode.includes('NextResponse.json'),
    'Uses NextResponse.json for responses'
  );

  // Requirement: 404 handling with "Annotation not found"
  assert(
    sourceCode.includes('Annotation not found'),
    'Handles annotation-not-found with error message'
  );

  // Requirement: params.id
  assert(
    sourceCode.includes('params') && sourceCode.includes('id'),
    'Uses params.id from route context'
  );

  // Requirement: next/server import
  assert(
    sourceCode.includes('next/server'),
    'Imports from next/server'
  );

  // Requirement: compositeDataUrl temp file logic
  assert(
    sourceCode.includes('compositeDataUrl') && sourceCode.includes('tmpdir'),
    'Writes compositeDataUrl to temp file'
  );

  // Requirement: Builds prompt with sectionId and text
  assert(
    sourceCode.includes('Analyze this annotation for section'),
    'Builds prompt with annotation context'
  );

  // Requirement: Updates analysis in DB
  assert(
    sourceCode.includes('UPDATE annotations SET') && sourceCode.includes('analysis'),
    'Updates analysis in DB after Claude analysis'
  );

  // Requirement: JSON.stringify for storing analysis
  assert(
    sourceCode.includes('JSON.stringify(analysis)'),
    'Stringifies analysis before storing in DB'
  );

  // Requirement: Re-reads annotation after update
  assert(
    /SELECT.*FROM annotations.*WHERE.*id/s.test(sourceCode),
    'Re-reads annotation from DB after update'
  );

  // Requirement: Temp file cleanup with try/finally
  assert(
    sourceCode.includes('finally') && sourceCode.includes('unlinkSync'),
    'Cleans up temp file in finally block'
  );

  // Requirement: 500 error handling
  assert(
    sourceCode.includes('500') && sourceCode.includes('Internal Server Error'),
    'Returns 500 on error'
  );

  console.log('');
}

// ---------------------------------------------------------------------------
// Example 7: Client usage pattern
// ---------------------------------------------------------------------------

function example7_clientPattern(): void {
  console.log('=== Example 7: Client usage pattern ===');

  console.log('  Browser usage:');
  console.log('    async function analyzeAnnotation(annotationId: string) {');
  console.log('      const res = await fetch(`/api/annotations/${annotationId}/analyze`, {');
  console.log('        method: "POST",');
  console.log('      });');
  console.log('      if (!res.ok) {');
  console.log('        const body = await res.json();');
  console.log('        throw new Error(body.error);');
  console.log('      }');
  console.log('      const { annotation } = await res.json();');
  console.log('      console.log("Analysis:", annotation.analysis);');
  console.log('    }');
  console.log('');
}

// ---------------------------------------------------------------------------
// Run all examples
// ---------------------------------------------------------------------------

async function main(): Promise<void> {
  console.log('========================================');
  console.log('POST /api/annotations/[id]/analyze Route - Module Verification');
  console.log('========================================\n');

  await example1_successfulAnalysis();
  await example2_notFound();
  await example3_noComposite();
  await example4_dbRoundTrip();
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

// example_usage.ts
// Comprehensive usage example for app/api/annotations/[id]/route.ts
//
// This file verifies the GET single annotation route by:
//   1. Importing and calling the actual GET handler from route.ts
//   2. Parsing JSON responses and verifying the Annotation shape
//   3. Testing success (200), not-found (404), and analysis parsing
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
// 1. Imports (safe now that alias is registered)
// ---------------------------------------------------------------------------
import fs from 'fs';
import path from 'path';
import { getDb } from '../lib/db';
import { randomUUID } from 'crypto';

// Dynamic require of route module (must be after alias registration above)
const routeModule = require('../app/api/annotations/[id]/route') as {
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
// Example 1: Successful annotation fetch (200 OK)
// ---------------------------------------------------------------------------

async function example1_successfulFetch(): Promise<void> {
  console.log('=== Example 1: Successful annotation fetch (200 OK) ===');

  const annId = 'ann-test-001';
  seedAnnotation({
    id: annId,
    sectionId: 'intro',
    timestamp: 3.2,
    text: 'Text is cut off on the right side',
    videoFile: 'output/sections/intro.mp4',
    analysis: {
      severity: 'major',
      fixType: 'remotion',
      technicalAssessment: 'Text overlay at 3.2s is clipped by the safe-zone boundary.',
      suggestedFixes: ['Reduce font size from 48px to 40px'],
      confidence: 0.87,
    },
  });

  const request = new Request('http://localhost/api/annotations/' + annId);
  const response = await routeModule.GET(request, { params: { id: annId } });

  assert(response.status === 200, 'Response status is 200');

  const contentType = response.headers.get('Content-Type');
  assert(
    contentType !== null && contentType.includes('application/json'),
    `Content-Type is application/json (got: ${contentType})`
  );

  const body = await response.json();

  // Verify full Annotation shape
  assert(body.id === annId, `id matches: ${body.id}`);
  assert(body.sectionId === 'intro', 'sectionId is "intro"');
  assert(body.timestamp === 3.2, 'timestamp is 3.2');
  assert(body.text === 'Text is cut off on the right side', 'text matches');
  assert(body.videoFile === 'output/sections/intro.mp4', 'videoFile matches');
  assert(body.resolved === false, 'resolved is false (boolean)');
  assert(body.resolveJobId === null, 'resolveJobId is null');
  assert(typeof body.createdAt === 'string', 'createdAt is a string');

  // Verify analysis was parsed from JSON
  assert(body.analysis !== null, 'analysis is not null');
  assert(body.analysis.severity === 'major', 'analysis.severity is "major"');
  assert(body.analysis.fixType === 'remotion', 'analysis.fixType is "remotion"');
  assert(typeof body.analysis.technicalAssessment === 'string', 'analysis.technicalAssessment is a string');
  assert(Array.isArray(body.analysis.suggestedFixes), 'analysis.suggestedFixes is an array');
  assert(body.analysis.confidence === 0.87, 'analysis.confidence is 0.87');

  // Verify raw analysis_json key is NOT in response
  assert(!('analysis_json' in body), 'analysis_json key is not in response');

  console.log('\n  Response body:');
  console.log(`    id:          ${body.id}`);
  console.log(`    sectionId:   ${body.sectionId}`);
  console.log(`    timestamp:   ${body.timestamp}s`);
  console.log(`    text:        ${body.text}`);
  console.log(`    videoFile:   ${body.videoFile}`);
  console.log(`    resolved:    ${body.resolved}`);
  console.log(`    analysis:    severity=${body.analysis.severity}, fixType=${body.analysis.fixType}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 2: Annotation not found (404)
// ---------------------------------------------------------------------------

async function example2_notFound(): Promise<void> {
  console.log('=== Example 2: Annotation not found (404) ===');

  const fakeId = 'nonexistent-id-999';

  const request = new Request('http://localhost/api/annotations/' + fakeId);
  const response = await routeModule.GET(request, { params: { id: fakeId } });

  assert(response.status === 404, 'Response status is 404');

  const body = await response.json();
  assert(body.error === 'Annotation not found', `error message is "Annotation not found" (got: "${body.error}")`);

  console.log(`  Response: ${JSON.stringify(body)}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 3: Annotation with null analysis (not yet analyzed)
// ---------------------------------------------------------------------------

async function example3_nullAnalysis(): Promise<void> {
  console.log('=== Example 3: Annotation with null analysis ===');

  const annId = 'ann-test-002';
  seedAnnotation({
    id: annId,
    sectionId: 'main',
    timestamp: 15.0,
    text: 'Color grading looks off in this scene',
    analysis: null,
  });

  const request = new Request('http://localhost/api/annotations/' + annId);
  const response = await routeModule.GET(request, { params: { id: annId } });

  assert(response.status === 200, 'Response status is 200');

  const body = await response.json();
  assert(body.id === annId, `id matches: ${body.id}`);
  assert(body.analysis === null, 'analysis is null (not yet analyzed)');
  assert(body.resolved === false, 'resolved is false');

  console.log(`  Annotation ${body.id}: analysis=${body.analysis}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 4: Resolved annotation
// ---------------------------------------------------------------------------

async function example4_resolved(): Promise<void> {
  console.log('=== Example 4: Resolved annotation ===');

  const annId = 'ann-test-003';
  const resolveJobId = 'job-fix-001';
  seedAnnotation({
    id: annId,
    sectionId: 'outro',
    timestamp: 5.0,
    text: 'Fade-out is too abrupt',
    resolved: true,
    resolveJobId,
    analysis: {
      severity: 'minor',
      fixType: 'remotion',
      technicalAssessment: 'Transition too fast.',
      suggestedFixes: ['Extend fade duration to 1.5s'],
      confidence: 0.9,
    },
  });

  const request = new Request('http://localhost/api/annotations/' + annId);
  const response = await routeModule.GET(request, { params: { id: annId } });

  assert(response.status === 200, 'Response status is 200');

  const body = await response.json();
  assert(body.resolved === true, 'resolved is true (boolean conversion from INTEGER 1)');
  assert(body.resolveJobId === resolveJobId, `resolveJobId matches: ${body.resolveJobId}`);

  console.log(`  Annotation ${body.id}: resolved=${body.resolved}, resolveJobId=${body.resolveJobId}`);
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
    path.join(__dirname, '..', 'app', 'api', 'annotations', '[id]', 'route.ts'),
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

  // Requirement: Imports getDb from @/lib/db
  assert(
    sourceCode.includes('getDb') && sourceCode.includes('@/lib/db'),
    'Imports getDb from @/lib/db'
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

  // Requirement: params.id destructuring
  assert(
    sourceCode.includes('params') && sourceCode.includes('id'),
    'Uses params.id from route context'
  );

  // Requirement: next/server import
  assert(
    sourceCode.includes('next/server'),
    'Imports from next/server'
  );

  // Requirement: analysis JSON parsing
  assert(
    sourceCode.includes('JSON.parse') && sourceCode.includes('analysis'),
    'Parses analysis JSON when reading from DB'
  );

  // Requirement: SELECT * FROM annotations WHERE id = ?
  assert(
    sourceCode.includes('SELECT') && sourceCode.includes('annotations') && sourceCode.includes('WHERE'),
    'Queries annotations table with WHERE clause'
  );

  console.log('');
}

// ---------------------------------------------------------------------------
// Run all examples
// ---------------------------------------------------------------------------

async function main(): Promise<void> {
  console.log('========================================');
  console.log('GET /api/annotations/[id] Route - Module Verification');
  console.log('========================================\n');

  await example1_successfulFetch();
  await example2_notFound();
  await example3_nullAnalysis();
  await example4_resolved();
  example5_exports();
  example6_sourceStructure();

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

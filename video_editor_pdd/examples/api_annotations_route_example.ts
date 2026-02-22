// example_usage.ts
// Comprehensive usage example for app/api/annotations/route.ts
//
// This file verifies the annotations CRUD route by:
//   1. Importing and calling the actual GET/POST handlers from route.ts
//   2. Parsing JSON responses and verifying the Annotation shape
//   3. Testing create (201), validation error (400), list all, and list filtered
//   4. Verifying source file structure matches prompt requirements
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

// Dynamic require of route module (must be after alias registration above)
const routeModule = require('../app/api/annotations/route') as {
  GET: (request: Request) => Promise<Response>;
  POST: (request: Request) => Promise<Response>;
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
// Example 1: Fetch all annotations (empty database)
// ---------------------------------------------------------------------------

async function example1_fetchAllEmpty(): Promise<void> {
  console.log('=== Example 1: Fetch all annotations (empty DB) ===');

  const request = new Request('http://localhost/api/annotations', { method: 'GET' });
  const response = await routeModule.GET(request);

  assert(response.status === 200, 'Response status is 200');

  const data = await response.json();
  assert(Array.isArray(data.annotations), 'Response has annotations array');
  assert(data.annotations.length === 0, `Empty DB returns 0 annotations (got ${data.annotations.length})`);

  console.log(`  Total annotations: ${data.annotations.length}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 2: Fetch annotations for section (empty)
// ---------------------------------------------------------------------------

async function example2_fetchBySectionEmpty(): Promise<void> {
  console.log('=== Example 2: Fetch annotations for section \'intro\' (empty) ===');

  const request = new Request('http://localhost/api/annotations?section=intro', { method: 'GET' });
  const response = await routeModule.GET(request);

  assert(response.status === 200, 'Response status is 200');

  const data = await response.json();
  assert(data.annotations.length === 0, `No annotations for section "intro" yet (got ${data.annotations.length})`);

  console.log(`  Annotations for section "intro": ${data.annotations.length}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 3: Create minimal annotation (required fields only)
// ---------------------------------------------------------------------------

async function example3_createMinimal(): Promise<string> {
  console.log('=== Example 3: Create minimal annotation ===');

  const request = new Request('http://localhost/api/annotations', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      sectionId: 'intro',
      text: 'Logo appears too late in the intro sequence',
    }),
  });

  const response = await routeModule.POST(request);

  assert(response.status === 201, 'Response status is 201');

  const annotation = await response.json();
  assert(typeof annotation.id === 'string' && annotation.id.length > 0, 'id is a non-empty string (UUID)');
  assert(annotation.sectionId === 'intro', 'sectionId is "intro"');
  assert(annotation.text === 'Logo appears too late in the intro sequence', 'text matches input');
  assert(annotation.timestamp === null, 'timestamp is null (not provided)');
  assert(annotation.videoFile === null, 'videoFile is null (not provided)');
  assert(annotation.drawingDataUrl === null, 'drawingDataUrl is null');
  assert(annotation.compositeDataUrl === null, 'compositeDataUrl is null');
  assert(annotation.analysis === null, 'analysis is null (not yet analyzed)');
  assert(annotation.resolved === false, 'resolved is false');
  assert(annotation.resolveJobId === null, 'resolveJobId is null');
  assert(typeof annotation.createdAt === 'string', 'createdAt is a string');

  console.log(`  Created annotation: ${annotation.id}`);
  console.log(`    sectionId: ${annotation.sectionId}`);
  console.log(`    text: ${annotation.text}`);
  console.log(`    timestamp: ${annotation.timestamp}`);
  console.log(`    analysis: ${annotation.analysis}`);
  console.log(`    resolved: ${annotation.resolved}`);
  console.log(`    createdAt: ${annotation.createdAt}`);
  console.log('');

  return annotation.id;
}

// ---------------------------------------------------------------------------
// Example 4: Create full annotation with all optional fields
// ---------------------------------------------------------------------------

async function example4_createFull(): Promise<string> {
  console.log('=== Example 4: Create full annotation ===');

  const request = new Request('http://localhost/api/annotations', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      sectionId: 'main',
      timestamp: 23.5,
      text: 'Text overlay is clipped on the right edge at this frame',
      videoFile: 'output/sections/main.mp4',
      drawingDataUrl: 'data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAUA...',
      compositeDataUrl: 'data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAUA...',
    }),
  });

  const response = await routeModule.POST(request);

  assert(response.status === 201, 'Response status is 201');

  const annotation = await response.json();
  assert(annotation.sectionId === 'main', 'sectionId is "main"');
  assert(annotation.timestamp === 23.5, 'timestamp is 23.5');
  assert(annotation.videoFile === 'output/sections/main.mp4', 'videoFile matches');
  assert(!!annotation.drawingDataUrl, 'has drawingDataUrl');
  assert(!!annotation.compositeDataUrl, 'has compositeDataUrl');
  assert(annotation.analysis === null, 'analysis is null');
  assert(annotation.resolved === false, 'resolved is false');

  console.log(`  Created full annotation: ${annotation.id}`);
  console.log(`    sectionId: ${annotation.sectionId}`);
  console.log(`    timestamp: ${annotation.timestamp}`);
  console.log(`    videoFile: ${annotation.videoFile}`);
  console.log(`    has drawing: ${!!annotation.drawingDataUrl}`);
  console.log(`    has composite: ${!!annotation.compositeDataUrl}`);
  console.log(`    analysis: ${annotation.analysis}`);
  console.log(`    resolved: ${annotation.resolved}`);
  console.log('');

  return annotation.id;
}

// ---------------------------------------------------------------------------
// Example 5: Validation error (missing required fields)
// ---------------------------------------------------------------------------

async function example5_validationError(): Promise<void> {
  console.log('=== Example 5: Validation error ===');

  // Missing 'text' field
  const request = new Request('http://localhost/api/annotations', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      sectionId: 'intro',
      // text is missing!
    }),
  });

  const response = await routeModule.POST(request);

  assert(response.status === 400, 'Response status is 400');

  const data = await response.json();
  assert(
    data.error === 'Missing required fields: sectionId and text are required.',
    `Error message matches (got: "${data.error}")`
  );

  console.log(`  Status: ${response.status}`);
  console.log(`  Error: ${data.error}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 6: Full workflow — create, then list by section
// ---------------------------------------------------------------------------

async function example6_workflow(): Promise<void> {
  console.log('=== Example 6: Full workflow ===');

  const sectionId = 'outro';

  // Step 1: Create an annotation
  const createReq = new Request('http://localhost/api/annotations', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      sectionId,
      timestamp: 5.0,
      text: 'Fade-out transition is too abrupt',
      videoFile: 'output/sections/outro.mp4',
    }),
  });
  const createRes = await routeModule.POST(createReq);
  const created = await createRes.json();
  assert(createRes.status === 201, 'Created annotation successfully');
  console.log(`  Step 1 — Created annotation: ${created.id}`);

  // Step 2: List annotations for this section
  const listReq = new Request(`http://localhost/api/annotations?section=${sectionId}`, { method: 'GET' });
  const listRes = await routeModule.GET(listReq);
  const listData = await listRes.json();

  assert(listData.annotations.length >= 1, `Section "${sectionId}" has at least 1 annotation`);

  // Verify our annotation is in the list
  const found = listData.annotations.find((a: { id: string }) => a.id === created.id);
  assert(!!found, 'Created annotation found in section list');

  console.log(`  Step 2 — Section "${sectionId}" has ${listData.annotations.length} annotation(s)`);
  console.log(`  Found our annotation: ${!!found}`);
  console.log(`  Step 3 — Next: POST /api/annotations/${created.id}/analyze (separate route)`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 7: Fetch all annotations (after creates)
// ---------------------------------------------------------------------------

async function example7_fetchAllAfterCreates(): Promise<void> {
  console.log('=== Example 7: Fetch all annotations (after creates) ===');

  const request = new Request('http://localhost/api/annotations', { method: 'GET' });
  const response = await routeModule.GET(request);

  assert(response.status === 200, 'Response status is 200');

  const data = await response.json();
  assert(data.annotations.length >= 3, `At least 3 annotations exist (got ${data.annotations.length})`);

  console.log(`  Total annotations: ${data.annotations.length}`);
  for (const ann of data.annotations) {
    console.log(
      `    [${ann.id}] section=${ann.sectionId} t=${ann.timestamp}s resolved=${ann.resolved} — "${ann.text}"`
    );
  }
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 8: Source file structure verification
// ---------------------------------------------------------------------------

function example8_sourceStructure(): void {
  console.log('=== Example 8: Source file structure verification ===');

  const sourceCode = fs.readFileSync(
    path.join(__dirname, '..', 'app', 'api', 'annotations', 'route.ts'),
    'utf-8'
  );

  // Requirement: GET handler
  assert(
    /export\s+async\s+function\s+GET/.test(sourceCode),
    'Exports async GET handler'
  );

  // Requirement: POST handler
  assert(
    /export\s+async\s+function\s+POST/.test(sourceCode),
    'Exports async POST handler'
  );

  // Requirement: Imports getDb from @/lib/db
  assert(
    sourceCode.includes('getDb') && sourceCode.includes('@/lib/db'),
    'Imports getDb from @/lib/db'
  );

  // Requirement: Imports types from @/lib/types
  assert(
    sourceCode.includes('Annotation') && sourceCode.includes('@/lib/types'),
    'Imports Annotation from @/lib/types'
  );

  // Requirement: crypto.randomUUID()
  assert(
    sourceCode.includes('randomUUID'),
    'Uses randomUUID for annotation ID generation'
  );

  // Requirement: NextResponse.json
  assert(
    sourceCode.includes('NextResponse.json'),
    'Uses NextResponse.json for responses'
  );

  // Requirement: section query param filter
  assert(
    sourceCode.includes('section') && sourceCode.includes('searchParams'),
    'Reads section query param for filtering'
  );

  // Requirement: 400 validation for missing fields
  assert(
    sourceCode.includes('400') && sourceCode.includes('sectionId') && sourceCode.includes('text'),
    'Validates required fields sectionId and text with 400 response'
  );

  // Requirement: ORDER BY timestamp ASC
  assert(
    sourceCode.includes('ORDER BY timestamp ASC'),
    'Orders annotations by timestamp ASC'
  );

  // Requirement: analysis JSON parsing on read
  assert(
    sourceCode.includes('JSON.parse') && sourceCode.includes('analysis'),
    'Parses analysis JSON when reading from DB'
  );

  // Requirement: next/server import
  assert(
    sourceCode.includes('next/server'),
    'Imports from next/server'
  );

  console.log('');
}

// ---------------------------------------------------------------------------
// Run all examples
// ---------------------------------------------------------------------------

async function main(): Promise<void> {
  console.log('========================================');
  console.log('Annotations Route - Module Verification');
  console.log('========================================\n');

  await example1_fetchAllEmpty();
  await example2_fetchBySectionEmpty();
  await example3_createMinimal();
  await example4_createFull();
  await example5_validationError();
  await example6_workflow();
  await example7_fetchAllAfterCreates();
  example8_sourceStructure();

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

// example_usage.ts
// Comprehensive usage example for app/api/jobs/[id]/route.ts
//
// This file verifies the GET job polling route by:
//   1. Importing and calling the actual GET handler from route.ts
//   2. Parsing JSON responses and verifying the Job shape
//   3. Testing success (200), not-found (404), and error job scenarios
//   4. Verifying exported constants match prompt requirements
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
const routeModule = require('../app/api/jobs/[id]/route') as {
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
// Example 1: Successful job fetch — GET returns full Job shape
// ---------------------------------------------------------------------------

async function example1_successfulFetch(): Promise<void> {
  console.log('=== Example 1: Successful job fetch (200 OK) ===');

  const jobId = createJob('tts-render', { sectionId: 'intro' });

  // Run the job to completion
  await runJob(jobId, async (onLog) => {
    onLog('[tts-render] Starting render');
    onLog('[tts-render] Progress: 50%');
    onLog('[tts-render] Completed successfully');
  });

  // Call the actual route handler
  const request = new Request('http://localhost/api/jobs/' + jobId);
  const response = await routeModule.GET(request, { params: { id: jobId } });

  // Verify status code
  assert(response.status === 200, 'Response status is 200');

  // Verify Content-Type is JSON
  const contentType = response.headers.get('Content-Type');
  assert(
    contentType !== null && contentType.includes('application/json'),
    `Content-Type is application/json (got: ${contentType})`
  );

  // Parse the response body
  const body = await response.json();

  // Verify full Job shape
  assert(body.id === jobId, `id matches: ${body.id}`);
  assert(body.stage === 'tts-render', `stage is tts-render`);
  assert(body.status === 'done', `status is done`);
  assert(body.progress === 100, `progress is 100`);
  assert(body.error === null, `error is null`);
  assert(typeof body.params === 'object', `params is an object`);
  assert(body.params.sectionId === 'intro', `params.sectionId is "intro"`);
  assert(typeof body.createdAt === 'string', `createdAt is a string`);
  assert(typeof body.updatedAt === 'string', `updatedAt is a string`);

  console.log('\n  Response body:');
  console.log(`    id:        ${body.id}`);
  console.log(`    stage:     ${body.stage}`);
  console.log(`    status:    ${body.status}`);
  console.log(`    progress:  ${body.progress}`);
  console.log(`    error:     ${body.error}`);
  console.log(`    params:    ${JSON.stringify(body.params)}`);
  console.log(`    createdAt: ${body.createdAt}`);
  console.log(`    updatedAt: ${body.updatedAt}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 2: Job not found — 404 response
// ---------------------------------------------------------------------------

async function example2_jobNotFound(): Promise<void> {
  console.log('=== Example 2: Job not found (404) ===');

  const fakeId = 'non-existent-job-id';

  const request = new Request('http://localhost/api/jobs/' + fakeId);
  const response = await routeModule.GET(request, { params: { id: fakeId } });

  // Verify 404 status
  assert(response.status === 404, 'Response status is 404');

  // Verify error body
  const body = await response.json();
  assert(body.error === 'Job not found', `error message is "Job not found" (got: "${body.error}")`);

  console.log(`  Response: ${JSON.stringify(body)}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 3: Pending job — returns current state before completion
// ---------------------------------------------------------------------------

async function example3_pendingJob(): Promise<void> {
  console.log('=== Example 3: Pending job (not yet started) ===');

  const jobId = createJob('veo', { sectionId: 'main', model: 'veo-2.0' });

  // Don't run the job — it stays in 'pending' status
  const request = new Request('http://localhost/api/jobs/' + jobId);
  const response = await routeModule.GET(request, { params: { id: jobId } });

  assert(response.status === 200, 'Response status is 200');

  const body = await response.json();
  assert(body.status === 'pending', `status is pending`);
  assert(body.progress === 0, `progress is 0`);
  assert(body.error === null, `error is null`);
  assert(body.stage === 'veo', `stage is veo`);

  console.log(`  Job ${body.id}: status=${body.status}, progress=${body.progress}%`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 4: Error job — returns error details
// ---------------------------------------------------------------------------

async function example4_errorJob(): Promise<void> {
  console.log('=== Example 4: Failed job with error ===');

  const jobId = createJob('specs', { sectionId: 'intro' });

  // Run a failing executor
  await runJob(jobId, async (onLog) => {
    onLog('[specs] Starting spec generation...');
    throw new Error('API rate limit exceeded');
  });

  const request = new Request('http://localhost/api/jobs/' + jobId);
  const response = await routeModule.GET(request, { params: { id: jobId } });

  assert(response.status === 200, 'Response status is 200 (error is in the body, not HTTP status)');

  const body = await response.json();
  assert(body.status === 'error', `status is error`);
  assert(body.error === 'API rate limit exceeded', `error message matches`);

  console.log(`  Job ${body.id}: status=${body.status}, error="${body.error}"`);
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
    path.join(__dirname, '..', 'app', 'api', 'jobs', '[id]', 'route.ts'),
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

  // Requirement: NextResponse.json
  assert(
    sourceCode.includes('NextResponse.json'),
    'Uses NextResponse.json for responses'
  );

  // Requirement: 404 handling with "Job not found"
  assert(
    sourceCode.includes('Job not found'),
    'Handles job-not-found with error message'
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

  console.log('');
}

// ---------------------------------------------------------------------------
// Example 7: Client polling pattern (SseLogPanel fallback)
// ---------------------------------------------------------------------------

function example7_clientPattern(): void {
  console.log('=== Example 7: Client polling pattern (SseLogPanel fallback) ===');

  console.log('  Browser usage:');
  console.log('    // SSE failed — fall back to polling GET /api/jobs/[id]');
  console.log('    async function pollJob(jobId: string) {');
  console.log('      const res = await fetch(`/api/jobs/${jobId}`);');
  console.log('      if (res.status === 404) throw new Error("Job not found");');
  console.log('      const job = await res.json();');
  console.log('      setStatus(job.status);');
  console.log('      setProgress(job.progress);');
  console.log('      if (job.error) setErrorMessage(job.error);');
  console.log('      if (job.status !== "done" && job.status !== "error") {');
  console.log('        setTimeout(() => pollJob(jobId), 2000);');
  console.log('      }');
  console.log('    }');
  console.log('');
}

// ---------------------------------------------------------------------------
// Run all examples
// ---------------------------------------------------------------------------

async function main(): Promise<void> {
  console.log('========================================');
  console.log('GET /api/jobs/[id] Route - Module Verification');
  console.log('========================================\n');

  await example1_successfulFetch();
  await example2_jobNotFound();
  await example3_pendingJob();
  await example4_errorJob();
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

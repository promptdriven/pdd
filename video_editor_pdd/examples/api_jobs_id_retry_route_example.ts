// example_usage.ts
// Comprehensive usage example for app/api/jobs/[id]/retry/route.ts
//
// This file verifies the POST retry route by:
//   1. Importing and calling the actual POST handler from route.ts
//   2. Parsing JSON responses and verifying status codes / body shapes
//   3. Testing all four scenarios: success (200), not-found (404),
//      not-in-error-state (400), and retryJob failure (500)
//   4. Verifying exported constants match prompt requirements
//   5. Verifying source file structure matches prompt requirements
//
// For standalone execution, an in-memory SQLite database is used
// and the @/ module path alias is resolved at runtime.

// ---------------------------------------------------------------------------
// 0. Environment setup (must run before any module that calls getDb())
// ---------------------------------------------------------------------------
process.env.DB_PATH = ':memory:';

// Register @/ path alias so route.ts's `import { ... } from "@/lib/jobs"`
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
import { createJob, getJob, runJob, registerExecutor } from '../lib/jobs';

// Dynamic require of route module (must be after alias registration above)
const routeModule = require('../app/api/jobs/[id]/retry/route') as {
  POST: (request: Request, context: { params: { id: string } }) => Promise<Response>;
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
// 3. Register a dummy executor for the 'setup' stage so retryJob succeeds
// ---------------------------------------------------------------------------
registerExecutor('setup', (_params, _send) => {
  return async (onLog) => {
    onLog('[setup] Retrying...');
    onLog('[setup] Done');
  };
});

// ---------------------------------------------------------------------------
// Example 1: Successful retry — job in error state with registered executor
// ---------------------------------------------------------------------------

async function example1_successfulRetry(): Promise<void> {
  console.log('=== Example 1: Successful retry (200 OK) ===');

  const jobId = createJob('setup', {});

  // Run the job and make it fail
  await runJob(jobId, async (onLog) => {
    onLog('[setup] Starting...');
    throw new Error('Something went wrong');
  });

  // Verify job is in error state
  const jobBefore = getJob(jobId);
  assert(jobBefore?.status === 'error', 'Job is in error state before retry');

  // Call the actual route handler
  const request = new Request('http://localhost/api/jobs/' + jobId + '/retry', {
    method: 'POST',
  });
  const response = await routeModule.POST(request, { params: { id: jobId } });

  // Verify 200 status
  assert(response.status === 200, 'Response status is 200');

  // Verify response body
  const body = await response.json();
  assert(body.jobId === jobId, `Response contains jobId: ${body.jobId}`);

  // Verify job was retried (executor ran, status should be done now)
  const jobAfter = getJob(jobId);
  assert(jobAfter?.status === 'done', `Job status is done after retry (got: ${jobAfter?.status})`);

  console.log(`  Response: ${JSON.stringify(body)}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 2: Job not found — 404 response
// ---------------------------------------------------------------------------

async function example2_jobNotFound(): Promise<void> {
  console.log('=== Example 2: Job not found (404) ===');

  const fakeId = 'non-existent-job-id';

  const request = new Request('http://localhost/api/jobs/' + fakeId + '/retry', {
    method: 'POST',
  });
  const response = await routeModule.POST(request, { params: { id: fakeId } });

  // Verify 404 status
  assert(response.status === 404, 'Response status is 404');

  // Verify error body
  const body = await response.json();
  assert(body.error === 'Job not found', `error message is "Job not found" (got: "${body.error}")`);

  console.log(`  Response: ${JSON.stringify(body)}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 3: Job is not in error state — 400 response
// ---------------------------------------------------------------------------

async function example3_notInErrorState(): Promise<void> {
  console.log('=== Example 3: Job not in error state (400) ===');

  const jobId = createJob('setup', {});

  // Run the job to completion (status = done)
  await runJob(jobId, async (onLog) => {
    onLog('[setup] Done');
  });

  const jobBefore = getJob(jobId);
  assert(jobBefore?.status === 'done', 'Job is in done state (not error)');

  // Attempt to retry a non-error job
  const request = new Request('http://localhost/api/jobs/' + jobId + '/retry', {
    method: 'POST',
  });
  const response = await routeModule.POST(request, { params: { id: jobId } });

  // Verify 400 status
  assert(response.status === 400, 'Response status is 400');

  // Verify error body
  const body = await response.json();
  assert(
    body.error === 'Job is not in error state',
    `error message is "Job is not in error state" (got: "${body.error}")`
  );

  console.log(`  Response: ${JSON.stringify(body)}`);
  console.log('');
}

// ---------------------------------------------------------------------------
// Example 4: retryJob throws — 500 response
// ---------------------------------------------------------------------------

async function example4_retryThrows(): Promise<void> {
  console.log('=== Example 4: retryJob throws (500) ===');

  // Create a job for a stage with no registered executor (e.g., 'veo')
  const jobId = createJob('veo', { sectionId: 'intro' });

  // Make it fail
  await runJob(jobId, async (onLog) => {
    onLog('[veo] Starting...');
    throw new Error('Veo API error');
  });

  const jobBefore = getJob(jobId);
  assert(jobBefore?.status === 'error', 'Job is in error state');

  // Suppress console.error during this test since the route handler
  // logs the expected error — we don't want it on stderr.
  const origConsoleError = console.error;
  console.error = () => {};

  // Retry — retryJob will throw because no executor for 'veo'
  const request = new Request('http://localhost/api/jobs/' + jobId + '/retry', {
    method: 'POST',
  });
  const response = await routeModule.POST(request, { params: { id: jobId } });

  // Restore console.error
  console.error = origConsoleError;

  // Verify 500 status
  assert(response.status === 500, 'Response status is 500');

  // Verify error body
  const body = await response.json();
  assert(body.error === 'Internal Server Error', `error message is "Internal Server Error" (got: "${body.error}")`);

  console.log(`  Response: ${JSON.stringify(body)}`);
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
    path.join(__dirname, '..', 'app', 'api', 'jobs', '[id]', 'retry', 'route.ts'),
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

  // Requirement: Imports getJob and retryJob from @/lib/jobs
  assert(
    sourceCode.includes('getJob') && sourceCode.includes('@/lib/jobs'),
    'Imports getJob from @/lib/jobs'
  );
  assert(
    sourceCode.includes('retryJob') && sourceCode.includes('@/lib/jobs'),
    'Imports retryJob from @/lib/jobs'
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

  // Requirement: 400 handling with "Job is not in error state"
  assert(
    sourceCode.includes('Job is not in error state'),
    'Handles non-error job with 400'
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

  console.log('');
}

// ---------------------------------------------------------------------------
// Example 7: Client usage pattern
// ---------------------------------------------------------------------------

function example7_clientPattern(): void {
  console.log('=== Example 7: Client usage pattern ===');

  console.log('  Browser usage:');
  console.log('    async function retryJob(jobId: string) {');
  console.log('      const res = await fetch(`/api/jobs/${jobId}/retry`, { method: "POST" });');
  console.log('      if (res.status === 404) throw new Error("Job not found");');
  console.log('      if (res.status === 400) {');
  console.log('        const body = await res.json();');
  console.log('        throw new Error(body.error);');
  console.log('      }');
  console.log('      const { jobId: id } = await res.json();');
  console.log('      // Subscribe to SSE at /api/jobs/${id}/stream for progress');
  console.log('    }');
  console.log('');
}

// ---------------------------------------------------------------------------
// Run all examples
// ---------------------------------------------------------------------------

async function main(): Promise<void> {
  console.log('========================================');
  console.log('POST /api/jobs/[id]/retry Route - Module Verification');
  console.log('========================================\n');

  await example1_successfulRetry();
  await example2_jobNotFound();
  await example3_notInErrorState();
  await example4_retryThrows();
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

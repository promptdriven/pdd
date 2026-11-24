import './helpers/test-home.mjs';
import './helpers/test-net-guard.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, existsSync, mkdirSync, readFileSync, realpathSync, rmSync, statSync, symlinkSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { delimiter, dirname, join, resolve } from 'node:path';
import { Readable } from 'node:stream';
import { fileURLToPath } from 'node:url';
import * as seam from '../src/runtime-seam.mjs';
import { CommandInputError, parseArgv } from '../src/argument-parser.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { formatBatchReconciliation, formatCheckReconciliation, formatStaleReconciliation } from '../src/core/reconcile-format.mjs';
import { checkRuntimeClientParity } from '../scripts/publish-release.mjs';
import { PLACE, TOKEN, fakeRuntime, harbor, portsFor } from './helpers/runtime-fake.mjs';

const repoRoot = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const RUNTIME_CLIENT_PKG = seam.version().package;
const VALID_REQUEST_ID = '11111111-1111-4111-8111-111111111111';

function fakeGhBin(sandbox) {
  const binDir = join(sandbox, 'fake-gh-bin');
  mkdirSync(binDir, { recursive: true });
  const ghPath = join(binDir, 'gh');
  writeFileSync(
    ghPath,
    `#!/bin/sh\nif [ "$1" = "auth" ]; then printf '%s\\n' ${JSON.stringify(TOKEN)}; exit 0; fi\nprintf 'octo 4242\\n'\n`,
  );
  chmodSync(ghPath, 0o755);
  return `${binDir}${delimiter}${process.env.PATH ?? ''}`;
}

function captureStream() {
  return {
    text: '',
    write(chunk) {
      this.text += String(chunk);
      return true;
    },
  };
}

function makeCliStory(repo) {
  rmSync(join(repo, 'tests/unknown-item.json'), { force: true });
  const input = {
    type: 'object',
    properties: { argv: { type: 'array', items: { type: 'string' } } },
    required: ['argv'],
    additionalProperties: false,
  };
  const result = {
    type: 'object',
    properties: {
      stdout: { type: 'string' },
      stderr: { type: 'string' },
      exit_code: { type: 'integer' },
    },
    required: ['stdout', 'stderr', 'exit_code'],
    additionalProperties: false,
  };
  const iface = {
    status: 'draft',
    prose_sha256: '',
    entries: [{ operation: 'main', input_schema: input, result_schema: result, errors: [] }],
    calls: [],
    resources: [],
    limits: { max_steps: 1, max_model_calls: 1 },
    conventions: ['input_schema', 'result_schema'].map(key => ({
      path: `/entries/0/${key}`,
      convention: 'cli',
    })),
  };
  const renderPrompt = () =>
    `# paperclip\n\nPrint each argument.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface)}\n\`\`\`\n</details>\n`;
  iface.prose_sha256 = seam.proseSha256(renderPrompt());
  writeFileSync(join(repo, PLACE), renderPrompt());
  writeFileSync(
    join(repo, 'user_stories/place-order.md'),
    '# Arguments\n\nI can pass words.\n\n## Acceptance criteria\n\n1. Each argument prints.\n',
  );
  const doc = {
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/place-order.md',
    criteria: [{ id: 'AC1', text: 'Each argument prints.' }],
    initial_world: {},
    simulation: {},
    context: [],
    steps: [
      {
        step_id: 'one',
        entry_path: PLACE,
        operation: 'main',
        input: { argv: ['hi'] },
        checks: [{ criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: 'hi\n' }],
      },
    ],
  };
  writeFileSync(join(repo, 'tests/place-order.json'), `${JSON.stringify(doc, null, 2)}\n`);
}

function compareExactSemver(a, b) {
  const pa = a.split('.').map(Number);
  const pb = b.split('.').map(Number);
  for (let i = 0; i < 3; i++) {
    if (pa[i] !== pb[i]) return pa[i] - pb[i];
  }
  return 0;
}

function makeReconciliationBody(requestId, overrides = {}) {
  return {
    schema_version: 'pdd-runtime.check-reconciliation.v1',
    read_only: true,
    request_id: requestId,
    job_id: requestId,
    command: 'check',
    disposition: {
      state: 'refused',
      verdict: 'refused',
      terminal: true,
      refusal_code: 'capacity-full',
      created_at: '2026-11-21T00:00:00Z',
      finished_at: '2026-11-21T00:00:01Z',
      expired: false,
      purged: false,
    },
    dispatch: { status: 'not_started', proven: true },
    accounting: {
      status: 'complete_zero',
      accounting_complete: true,
      calls: 0,
      known_calls: 0,
      unknown_calls: 0,
      cap: 40,
    },
    retry: {
      blocked: false,
      safe_next_action: 'Safe to submit a replacement check with a new request ID.',
    },
    evidence: {
      proof_basis: ['server_receipt_not_dispatched'],
      contradictions: [],
      ledger_row_present: false,
      report_status: 'missing',
      report_dispatch: 'not_started',
      report_accounting_complete: true,
      prepared_receipt_status: 'valid',
      provision_phase: 'never_provisioned',
      accounting_custody: 'protected',
      call_records_count: 0,
      call_ledger_status: 'absent',
      call_ledger_started: false,
      call_ledger_counts: null,
    },
    provenance: {
      source_sha256: 'a'.repeat(64),
      engine_sha: 'b'.repeat(40),
      server_commit: 'c'.repeat(40),
      sources_consulted: ['receipt_store'],
    },
    ...overrides,
  };
}

test('#3431 / #3594: runtime-client >= 1.1.1 pins exact semver, accepts pdd-bindings.json without stories, and supports bounded pdd-workspace.json', async t => {
  const pkg = JSON.parse(readFileSync(join(repoRoot, 'package.json'), 'utf8'));
  const lockfile = JSON.parse(readFileSync(join(repoRoot, 'package-lock.json'), 'utf8'));
  const pinned = pkg.dependencies[RUNTIME_CLIENT_PKG];
  const locked = lockfile.packages[`node_modules/${RUNTIME_CLIENT_PKG}`];
  assert.equal(typeof pinned, 'string');
  assert.match(pinned, /^\d+\.\d+\.\d+$/, `expected exact semver pin, got ${JSON.stringify(pinned)}`);
  assert.ok(compareExactSemver(pinned, '1.1.1') >= 0, `expected pinned version >= 1.1.1, got ${pinned}`);
  assert.equal(lockfile.packages[''].dependencies[RUNTIME_CLIENT_PKG], pinned);
  assert.equal(locked.version, pinned);
  assert.equal(locked.resolved, `https://registry.npmjs.org/${RUNTIME_CLIENT_PKG}/-/runtime-client-${pinned}.tgz`);

  // 1. pdd-bindings.json { module, prompt } without stories works on pdd test --files.
  const setup = harbor(t, repo => {
    mkdirSync(join(repo, 'src'), { recursive: true });
    writeFileSync(join(repo, 'src/place-order.mjs'), 'export function placeOrder() { return true; }\n');
    writeFileSync(
      join(repo, 'pdd-bindings.json'),
      `${JSON.stringify({ schema_version: 'pdd.bindings.v1', modules: [{ module: 'src/place-order.mjs', prompt: PLACE }] }, null, 2)}\n`,
    );
  });

  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state });
  const seamCode = await seam.local(
    { what: 'files', words: ['place-order'], options: { '--json': true }, cwd: setup.repo },
    ports,
  );
  assert.equal(seamCode, 0, ports.stderr.text);
  const seamJson = JSON.parse(ports.stdout.text);
  assert.ok(Array.isArray(seamJson.files), 'expected --files JSON to include files array');
  assert.ok(seamJson.files.some(f => f.path === PLACE), `expected ${PLACE} in files list`);

  const stdout = captureStream();
  const stderr = captureStream();
  const cliCode = await runPdd(['test', '--files', 'place-order', '--json'], {
    cwd: setup.repo,
    env: { ...process.env, HOME: setup.home, PDD_STATE_DIR: setup.state },
    stdout,
    stderr,
  });
  assert.equal(cliCode, 0, stderr.text);
  const cliJson = JSON.parse(stdout.text);
  assert.ok(cliJson.files.some(f => f.path === PLACE));

  // 2. Bounded pdd-workspace.json excluding src/ still allows pdd-bindings.json to reference Git-visible src/ modules (1.1.1 fix).
  const boundedSetup = harbor(t, repo => {
    mkdirSync(join(repo, 'src'), { recursive: true });
    writeFileSync(join(repo, 'src/place-order.mjs'), 'export function placeOrder() { return true; }\n');
    writeFileSync(
      join(repo, 'pdd-workspace.json'),
      `${JSON.stringify({ allowed_paths: ['prompts/', 'user_stories/', 'tests/'] }, null, 2)}\n`,
    );
    writeFileSync(
      join(repo, 'pdd-bindings.json'),
      `${JSON.stringify({
        schema_version: 'pdd.bindings.v1',
        modules: [{ module: 'src/place-order.mjs', stories: ['user_stories/place-order.md'], prompt: PLACE }],
      }, null, 2)}\n`,
    );
  });

  const boundedFiles = portsFor({ HOME: boundedSetup.home, PDD_STATE_DIR: boundedSetup.state });
  assert.equal(
    await seam.local({ what: 'files', words: ['place-order'], options: { '--json': true }, cwd: boundedSetup.repo }, boundedFiles.ports),
    0,
    boundedFiles.ports.stderr.text,
  );
  assert.ok(JSON.parse(boundedFiles.ports.stdout.text).files.some(f => f.path === PLACE));

  const boundedBindings = portsFor({ HOME: boundedSetup.home, PDD_STATE_DIR: boundedSetup.state });
  assert.equal(
    await seam.local({ what: 'explain-bindings', words: ['place-order'], options: { '--json': true }, cwd: boundedSetup.repo }, boundedBindings.ports),
    0,
    boundedBindings.ports.stderr.text,
  );

  // Also verify real 1.1.1 check run computes binding coverage cleanly under bounded pdd-workspace.json.
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const boundedCheck = portsFor({ HOME: boundedSetup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: boundedSetup.state });
  assert.equal(
    await seam.check({ words: ['place-order'], options: { '--json': true }, cwd: boundedSetup.repo }, boundedCheck.ports),
    0,
    boundedCheck.ports.stderr.text,
  );
  const checkJson = JSON.parse(boundedCheck.ports.stdout.text);
  assert.equal(checkJson.coverage?.available, true);
  assert.equal(checkJson.coverage?.bound, 1);
  assert.equal(checkJson.coverage?.total, 1);
});

test('#3594: pdd test --fresh parses cleanly, bypasses local cache reuse, sends fresh: true, and rejects invalid mixes', async t => {
  assert.deepEqual(parseArgv(['test', 'place-order', '--fresh']).options, { '--fresh': true });
  assert.deepEqual(parseArgv(['test', '--affected', '--fresh']).options, { '--affected': true, '--fresh': true });
  assert.throws(() => parseArgv(['test', '--fresh=true']), CommandInputError);

  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));

  // 1. Initial run populates local cache and does NOT send fresh: true.
  const first = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(
    await seam.check({ words: ['place-order'], options: { '--json': true }, cwd: setup.repo }, first.ports),
    0,
    first.ports.stderr.text,
  );
  assert.equal(fake.posts.filter(p => p.command === 'check').length, 1);
  assert.notEqual(fake.posts.filter(p => p.command === 'check')[0].request.fresh, true);

  // 2. Second ordinary run reuses local passing cache (0 new POSTs).
  const cached = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(
    await seam.check({ words: ['place-order'], options: { '--json': true }, cwd: setup.repo }, cached.ports),
    0,
    cached.ports.stderr.text,
  );
  assert.equal(fake.posts.filter(p => p.command === 'check').length, 1, 'second run without --fresh should hit cache');

  // 3. --fresh run bypasses local cache reuse AND sends fresh: true in POST /v1/check.
  const freshRun = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(
    await seam.check({ words: ['place-order'], fresh: true, options: { '--json': true }, cwd: setup.repo }, freshRun.ports),
    0,
    freshRun.ports.stderr.text,
  );
  const checkPosts = fake.posts.filter(p => p.command === 'check');
  assert.equal(checkPosts.length, 2, '--fresh must bypass saved passing cache and dispatch a fresh check');
  assert.equal(checkPosts[1].request.fresh, true, 'POST /v1/check payload must carry fresh: true');

  // 4. --affected --fresh succeeds cleanly and sends fresh: true when a prompt changes (with refreshed prose_sha256).
  const editedPrompt = readFileSync(join(setup.repo, PLACE), 'utf8').replace('## Dependencies', 'Extra note.\n\n## Dependencies');
  const syncedPrompt = seam.format.setInterfaceStatus(editedPrompt, {
    status: 'approved',
    prose_sha256: seam.proseSha256(editedPrompt),
  });
  writeFileSync(join(setup.repo, PLACE), syncedPrompt);
  const affectedRun = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  const affectedCode = await seam.check(
    { options: { '--affected': true, '--fresh': true, '--json': true }, cwd: setup.repo },
    affectedRun.ports,
  );
  assert.equal(affectedCode, 0, affectedRun.ports.stderr.text);
  const affectedPosts = fake.posts.filter(p => p.command === 'check');
  assert.ok(affectedPosts.length >= 3, `expected --affected --fresh to dispatch fresh checks, got ${affectedPosts.length}`);
  assert.equal(affectedPosts.at(-1).request.fresh, true);

  // 5. Invalid --fresh mixes fail closed with exit 2.
  for (const badOpts of [
    { '--fresh': true, '--read': true },
    { '--fresh': true, '--lint': true },
    { '--fresh': true, '--files': true },
    { '--fresh': true, '--reconcile': VALID_REQUEST_ID },
    { '--fresh': 'yes' },
  ]) {
    const p = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
    assert.equal(await seam.runCheck({ words: [], options: badOpts, cwd: setup.repo }, p.ports), 2, JSON.stringify(badOpts));
  }
});

test('#3594: direct pdd --fresh forwards fresh: true to POST /v1/try, CLI door descriptors, and runDoorCall', async t => {
  assert.deepEqual(parseArgv(['--fresh', 'place-order']).options, { '--fresh': true });
  assert.deepEqual(parseArgv(['--cli', '--fresh', 'place-order']).options, { '--cli': true, '--fresh': true });
  assert.deepEqual(parseArgv(['prompts/app.prompt.md', '--fresh']).options, { '--fresh': true });
  assert.throws(() => parseArgv(['--fresh=1']), CommandInputError);

  const webSetup = harbor(t);
  const setup = harbor(t, makeCliStory);
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.url.endsWith('/model')) return { status: 200, json: { calls: { cap: 40, remaining: 40 } } };
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.method === 'POST' && entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
    if (entry.method === 'POST' && /^\/v1\/try\/([^/]+)\/call$/.test(entry.url)) {
      const sessionId = entry.url.match(/^\/v1\/try\/([^/]+)\/call$/)[1];
      const callId = entry.json?.requestId ?? VALID_REQUEST_ID;
      const callAnswer = {
        id: callId,
        requestId: callId,
        command: 'call',
        session_id: sessionId,
        state: 'passed',
        result: {
          program_result: { stdout: 'hi\n', stderr: '', exit_code: 0 },
          world: {},
          input_world: {},
          session: { id: sessionId },
        },
        usage: { calls: 1, cap: 40, remaining: 39 },
      };
      f.jobs.set(callId, callAnswer);
      return { status: 200, json: callAnswer };
    }
    if (entry.method === 'GET' && f.jobs.has(entry.url.split('/').at(-1))) {
      return { status: 200, json: f.jobs.get(entry.url.split('/').at(-1)) };
    }
    return { status: 200, json: f.tryJob(entry.url.split('/').at(-1)) };
  });

  // 1. Standard browser simulate with --fresh sends fresh: true on POST /v1/try.
  const webPorts = portsFor(
    { HOME: webSetup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: webSetup.state },
    { openUrl: async () => true },
  );
  assert.equal(
    await seam.simulate({ words: ['place-order'], fresh: true, options: { '--no-wait': true }, cwd: webSetup.repo }, webPorts.ports),
    0,
    webPorts.ports.stderr.text,
  );
  const tryPosts = fake.posts.filter(p => p.command === 'try');
  assert.equal(tryPosts.length, 1);
  assert.equal(tryPosts[0].request.fresh, true, 'POST /v1/try must include fresh: true');

  // 2. CLI simulate with --cli --fresh marks the saved door descriptor fresh: true and forwards fresh: true on door calls.
  const cliPorts = portsFor(
    { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state },
    { stdin: Readable.from([]), openUrl: async () => false },
  );
  assert.equal(
    await seam.simulate({ words: ['place-order'], mode: 'cli', fresh: true, options: { '--new': true }, cwd: setup.repo }, cliPorts.ports),
    0,
    cliPorts.ports.stderr.text,
  );
  const launcherText = readFileSync(join(setup.repo, '.pdd/try/bin/paperclip'), 'utf8');
  const descriptorMatch = launcherText.match(/([^\s'"]+\.door\.json)/);
  assert.ok(descriptorMatch, `expected .door.json path in launcher:\n${launcherText}`);
  const descriptorPath = descriptorMatch[1];
  assert.equal(existsSync(descriptorPath), true);
  const descriptor = JSON.parse(readFileSync(descriptorPath, 'utf8'));
  assert.equal(descriptor.fresh, true, 'CLI door descriptor must persist fresh: true');

  const callPorts = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  await seam.runDoorCall(descriptor, { argv: ['hi'] }, callPorts.ports);
  const callPosts = fake.jsonPosts.filter(p => /^\/v1\/try\/[^/]+\/call$/.test(p.url));
  assert.equal(callPosts.length, 1);
  assert.equal(callPosts[0].json.fresh, true, 'POST /v1/try/:id/call must include fresh: true');

  // 3. Invalid --stop --fresh mix fails closed with exit 2.
  const badPorts = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(
    await seam.simulate({ words: ['place-order'], mode: 'stop', fresh: true, cwd: setup.repo }, badPorts.ports),
    2,
  );
});

test('#3594: pdd test --read --details passes through cleanly without rejecting the flag and still rejects invalid mixes', async t => {
  assert.deepEqual(parseArgv(['test', '--read', '--details']).options, { '--read': true, '--details': true });

  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.method === 'POST') {
      return {
        status: 200,
        json: f.check(entry.request.requestId, 'failed', [
          {
            step_id: 'add-coffee',
            criterion_id: 'AC1',
            passed: false,
            target: 'result',
            path: '/total',
            op: 'equals',
            expected: 350,
            actual: 400,
            detail: 'Expected total 350 but got 400.',
          },
        ]),
      };
    }
    return f.normal(entry);
  });

  const runPorts = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  const runCode = await seam.check({ words: ['place-order'], options: { '--json': true }, cwd: setup.repo }, runPorts.ports);
  assert.equal(runCode, 1, runPorts.ports.stderr.text);
  const batchId = JSON.parse(runPorts.ports.stdout.text).batch;
  assert.ok(batchId, 'expected saved batch ID from check output');

  // Compare --read WITHOUT --details vs --read WITH --details: detailed checks output appears only with --details.
  const plainReadPorts = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  const plainReadCode = await seam.read({ batch: batchId, cwd: setup.repo }, plainReadPorts.ports);
  assert.equal(plainReadCode, 1, plainReadPorts.ports.stderr.text);
  assert.doesNotMatch(plainReadPorts.ports.stdout.text, /Checks for Place a coffee order \(tests\/place-order\.json\):/);

  const readPorts = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  const readCode = await seam.read({ batch: batchId, details: true, cwd: setup.repo }, readPorts.ports);
  assert.equal(readCode, 1, `expected saved failure exit 1 (not option refusal 2), stderr:\n${readPorts.ports.stderr.text}`);
  assert.doesNotMatch(readPorts.ports.stderr.text, /This mix of options does not work together/);
  assert.match(readPorts.ports.stdout.text, /Checks for Place a coffee order \(tests\/place-order\.json\):/);
  assert.match(readPorts.ports.stdout.text, /\/total/);

  // Also test through runPdd CLI path.
  const cliOut = captureStream();
  const cliErr = captureStream();
  const cliReadCode = await runPdd(['test', '--read', batchId, '--details'], {
    cwd: setup.repo,
    env: { ...process.env, HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state, PATH: fakeGhBin(setup.sandbox) },
    stdout: cliOut,
    stderr: cliErr,
  });
  assert.equal(cliReadCode, 1, cliErr.text);
  assert.doesNotMatch(cliErr.text, /This mix of options does not work together/);
  assert.match(cliOut.text, /Checks for Place a coffee order \(tests\/place-order\.json\):/);

  // Invalid extra flag alongside --read --details still fails closed with exit 2.
  const badPorts = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(
    await seam.runCheck({ words: [batchId], options: { '--read': true, '--details': true, '--lf': true }, cwd: setup.repo }, badPorts.ports),
    2,
  );
});

test('#3594: pdd test --reconcile exercises real >= 1.1.1 read-only HTTP reconciliation, validates inputs, preserves mocked older-client fail-closed path, and reads saved targets', async t => {
  assert.deepEqual(parseArgv(['test', '--reconcile', VALID_REQUEST_ID, '--json']).options, {
    '--reconcile': VALID_REQUEST_ID,
    '--json': true,
  });
  assert.throws(() => parseArgv(['test', '--reconcile', 'not-a-uuid']), CommandInputError);

  const setup = harbor(t);
  const completeZeroBody = makeReconciliationBody(VALID_REQUEST_ID);
  let reconcileReply = () => ({ status: 200, json: completeZeroBody });
  const fake = await fakeRuntime(t, entry => {
    if (entry.method === 'GET' && entry.url === `/v1/runs/${VALID_REQUEST_ID}/reconciliation`) {
      return reconcileReply(entry);
    }
    throw new Error(`unexpected runtime call during --reconcile: ${entry.method} ${entry.url}`);
  });

  // 1. Real >= 1.1.1 projectCheckReconciliation projects valid HTTP 200, 410, 404, and contradictory payloads fail-closed.
  const projectedOk = seam.projectCheckReconciliation({
    request_id: VALID_REQUEST_ID,
    status: 200,
    body: completeZeroBody,
  });
  assert.equal(projectedOk.available, true);
  assert.equal(projectedOk.http_status, 200);
  assert.equal(projectedOk.dispatch.status, 'not_started');
  assert.equal(projectedOk.dispatch.proven, true);
  assert.equal(projectedOk.accounting.status, 'complete_zero');
  assert.equal(projectedOk.retry.blocked, false);

  const projectedExpired = seam.projectCheckReconciliation({
    request_id: VALID_REQUEST_ID,
    status: 410,
    body: null,
  });
  assert.equal(projectedExpired.available, false);
  assert.equal(projectedExpired.http_status, 410);
  assert.equal(projectedExpired.error_code, 'result-expired');
  assert.equal(projectedExpired.disposition.expired, true);
  assert.equal(projectedExpired.retry.blocked, true);

  const projectedMissing = seam.projectCheckReconciliation({
    request_id: VALID_REQUEST_ID,
    status: 404,
    body: null,
  });
  assert.equal(projectedMissing.available, false);
  assert.equal(projectedMissing.error_code, 'run-not-found');
  assert.equal(projectedMissing.retry.blocked, true);

  const projectedContradictory = seam.projectCheckReconciliation({
    request_id: VALID_REQUEST_ID,
    status: 200,
    body: makeReconciliationBody(VALID_REQUEST_ID, {
      accounting: {
        status: 'complete_zero',
        accounting_complete: true,
        calls: 1,
        known_calls: 1,
        unknown_calls: 0,
        cap: 40,
      },
    }),
  });
  assert.equal(projectedContradictory.available, false);
  assert.equal(projectedContradictory.error_code, 'contradictory-reconciliation');
  assert.equal(projectedContradictory.retry.blocked, true);

  assert.throws(
    () => seam.projectCheckReconciliation({ request_id: '', status: 200, body: null }),
    err => err?.code === 'invalid-request-id',
  );
  await assert.rejects(
    () => seam.reconcileCheckReceipt({ cwd: setup.repo, requestId: 'bad-id' }),
    err => err?.code === 'invalid-request-id' && err?.exitCode === 2,
  );

  // 2. Real >= 1.1.1 seam.reconcileCheckReceipt & CLI runPdd end-to-end against loopback fakeRuntime (read-only GET, 0 POSTs).
  const batchName = '20261121-000100-ab12';
  const batchDir = join(setup.state, 'batches', batchName);
  mkdirSync(batchDir, { recursive: true });
  const batchPath = join(batchDir, 'batch.json');
  const savedBatch = {
    batch: batchName,
    intent: 'check',
    root: setup.repo,
    rows: [
      { test: 'tests/place-order.json', story: 'user_stories/place-order.md', state: 'unknown', request_ids: [VALID_REQUEST_ID, 'not-a-uuid', VALID_REQUEST_ID] },
      { test: 'tests/unknown-item.json', story: 'user_stories/unknown-item.md', state: 'passed', request_ids: ['22222222-2222-4222-8222-222222222222'] },
    ],
  };
  const rawSaved = `${JSON.stringify(savedBatch, null, 2)}\n`;
  writeFileSync(batchPath, rawSaved);

  const livePorts = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }).ports;
  const directLive = await seam.reconcileCheckReceipt({ cwd: setup.repo, requestId: VALID_REQUEST_ID }, livePorts);
  assert.equal(directLive.available, true);
  assert.equal(directLive.request_id, VALID_REQUEST_ID);
  assert.equal(directLive.accounting.status, 'complete_zero');

  const liveEnv = {
    ...process.env,
    HOME: setup.home,
    PDD_RUNTIME_URL: fake.origin,
    PDD_STATE_DIR: setup.state,
    PATH: fakeGhBin(setup.sandbox),
  };

  const jsonOut = captureStream();
  const jsonErr = captureStream();
  const jsonCode = await runPdd(['test', '--reconcile', VALID_REQUEST_ID, '--json'], {
    cwd: setup.repo,
    env: liveEnv,
    stdout: jsonOut,
    stderr: jsonErr,
  });
  assert.equal(jsonCode, 0, jsonErr.text);
  const parsedLive = JSON.parse(jsonOut.text);
  assert.equal(parsedLive.available, true);
  assert.equal(parsedLive.request_id, VALID_REQUEST_ID);
  assert.equal(parsedLive.accounting.status, 'complete_zero');

  const textOut = captureStream();
  const textErr = captureStream();
  const textCode = await runPdd(['test', '--reconcile', VALID_REQUEST_ID], {
    cwd: setup.repo,
    env: liveEnv,
    stdout: textOut,
    stderr: textErr,
  });
  assert.equal(textCode, 0, textErr.text);
  assert.match(textOut.text, /CHECK reconciliation 11111111-1111-4111-8111-111111111111 \(read-only; HTTP 200\)/);
  assert.match(textOut.text, /Dispatch: not_started \(proven\)/);
  assert.match(textOut.text, /Accounting: complete_zero \(complete=yes, calls=0, known=0, unknown=0, cap=40\)/);
  assert.match(textOut.text, /Retry blocked: no/);

  // Real >= 1.1.1 HTTP 410 expired response fails closed with exit 3 and keeps retry blocked.
  reconcileReply = () => ({ status: 410, json: { error: { code: 'result-expired' } } });
  const expOut = captureStream();
  const expErr = captureStream();
  const expCode = await runPdd(['test', '--reconcile', VALID_REQUEST_ID], {
    cwd: setup.repo,
    env: liveEnv,
    stdout: expOut,
    stderr: expErr,
  });
  assert.equal(expCode, 3, expErr.text);
  assert.match(expOut.text, /expired=yes/);
  assert.match(expOut.text, /Retry blocked: yes/);
  assert.match(expOut.text, /Error: result-expired/);
  assert.equal(fake.posts.length, 0, '--reconcile must never dispatch POST requests');
  assert.equal(fake.jsonPosts.length, 0, '--reconcile must never dispatch JSON POST requests');
  assert.equal(fake.gets.filter(g => g.url === `/v1/runs/${VALID_REQUEST_ID}/reconciliation`).length, 4);
  assert.equal(formatCheckReconciliation(null), 'CHECK reconciliation: unavailable (malformed response).');

  // 3. Mocked older-client fail-closed coverage (code: reconciliation-unsupported, exit 5) via seam/CLI ports.
  const makeUnsupportedError = () =>
    Object.assign(new Error(`CHECK receipt reconciliation requires ${RUNTIME_CLIENT_PKG} >= 1.1.1.`), {
      code: 'reconciliation-unsupported',
      exitCode: 5,
    });
  await assert.rejects(
    () => seam.reconcileCheckReceipt(
      { cwd: setup.repo, requestId: VALID_REQUEST_ID },
      { reconcileCheckReceipt: async () => { throw makeUnsupportedError(); } },
    ),
    err => err?.code === 'reconciliation-unsupported' && err?.exitCode === 5 && err.message.includes(RUNTIME_CLIENT_PKG),
  );
  assert.throws(
    () => seam.projectCheckReconciliation(
      { request_id: VALID_REQUEST_ID, status: 200, body: completeZeroBody },
      { projectCheckReconciliation: () => { throw makeUnsupportedError(); } },
    ),
    err => err?.code === 'reconciliation-unsupported' && err?.exitCode === 5,
  );
  const fallbackOut = captureStream();
  const fallbackErr = captureStream();
  const fallbackCode = await runPdd(['test', '--reconcile', VALID_REQUEST_ID], {
    cwd: setup.repo,
    env: { ...process.env, HOME: setup.home, PDD_STATE_DIR: setup.state },
    stdout: fallbackOut,
    stderr: fallbackErr,
    runtimeCheckReconcile: async () => { throw makeUnsupportedError(); },
  });
  assert.equal(fallbackCode, 5);
  assert.ok(fallbackErr.text.includes(RUNTIME_CLIENT_PKG));

  // 4. CLI rejects invalid option/operand mixes with exit 2.
  for (const argv of [
    ['test', '--reconcile', 'not-a-uuid'],
    ['test', '--reconcile', VALID_REQUEST_ID, '--fresh'],
    ['test', '--reconcile', VALID_REQUEST_ID, 'place-order'],
  ]) {
    const out = captureStream();
    const err = captureStream();
    assert.equal(
      await runPdd(argv, {
        cwd: setup.repo,
        env: { ...process.env, HOME: setup.home, PDD_STATE_DIR: setup.state },
        stdout: out,
        stderr: err,
      }),
      2,
      argv.join(' '),
    );
  }

  // 5. Seam DI forwarding for reconcileCheckReceipt & projectCheckReconciliation.
  const forwarded = await seam.reconcileCheckReceipt(
    { cwd: setup.repo, requestId: VALID_REQUEST_ID },
    { reconcileCheckReceipt: async (inp, p) => ({ ok: true, id: inp.requestId, hasRedaction: Boolean(p.redaction) }) },
  );
  assert.deepEqual(forwarded, { ok: true, id: VALID_REQUEST_ID, hasRedaction: true });
  assert.deepEqual(
    seam.projectCheckReconciliation(
      { requestId: VALID_REQUEST_ID },
      { projectCheckReconciliation: inp => ({ projected: inp.requestId }) },
    ),
    { projected: VALID_REQUEST_ID },
  );

  // 6. --reconcile leaves saved batch JSON strictly untouched on disk.
  assert.equal(readFileSync(batchPath, 'utf8'), rawSaved, '--reconcile must remain strictly read-only');
});

test('#3594: checkRuntimeClientParity validates real repo package.json pinned at exact semver >= 1.1.1 cleanly offline', () => {
  const pkg = JSON.parse(readFileSync(join(repoRoot, 'package.json'), 'utf8'));
  const pinned = pkg.dependencies[RUNTIME_CLIENT_PKG];
  assert.match(pinned, /^\d+\.\d+\.\d+$/);
  assert.ok(compareExactSemver(pinned, '1.1.1') >= 0);
  const [major, minor] = pinned.split('.').map(Number);
  const newer = `${major}.${minor + 1}.0`;

  const matched = checkRuntimeClientParity({
    root: repoRoot,
    dryRun: false,
    runCommand: () => ({ status: 0, stdout: `${pinned}\n`, stderr: '' }),
    log: () => {},
  });
  assert.equal(matched.ok, true);
  assert.equal(matched.skipped, false);
  assert.equal(matched.stale, false);
  assert.equal(matched.pinned, pinned);
  assert.equal(matched.latest, pinned);

  assert.throws(
    () => checkRuntimeClientParity({
      root: repoRoot,
      dryRun: false,
      runCommand: () => ({ status: 0, stdout: `${newer}\n`, stderr: '' }),
      log: () => {},
    }),
    err => err instanceof Error && err.message.includes(`pinned to ${pinned}, behind latest published ${newer}`),
  );
});

test('#3617: .github/dependabot.yml schedules daily npm updates scoped strictly to the runtime client package', () => {
  const dependabotPath = join(repoRoot, '.github/dependabot.yml');
  assert.equal(existsSync(dependabotPath), true, 'expected .github/dependabot.yml to exist');
  const raw = readFileSync(dependabotPath, 'utf8');
  const lines = raw
    .split(/\r?\n/)
    .map(line => line.replace(/#.*$/, '').trimEnd())
    .filter(line => line.trim().length > 0);
  const unquote = val => val.trim().replace(/^(['"])(.*)\1$/, '$2');

  assert.ok(lines.some(line => /^version:\s*2\s*$/.test(line)), 'expected Dependabot config version: 2');

  const updatesIdx = lines.findIndex(line => /^updates:\s*$/.test(line));
  assert.ok(updatesIdx >= 0, 'expected top-level updates: section');
  const updateIndent = lines.slice(updatesIdx + 1).find(line => /^\s*-\s+/.test(line))?.match(/^(\s*)-/)?.[1].length;
  assert.equal(typeof updateIndent, 'number', 'expected at least one updates entry');

  const entries = [];
  for (let i = updatesIdx + 1; i < lines.length; i++) {
    const line = lines[i];
    const indent = line.match(/^(\s*)/)[1].length;
    if (indent === 0) break;
    if (indent === updateIndent && line.slice(indent).startsWith('-')) {
      entries.push([line.slice(indent + 1).trim()]);
    } else if (entries.length > 0) {
      entries.at(-1).push(line);
    }
  }
  assert.equal(entries.length, 1, `expected exactly one Dependabot update rule, got ${entries.length}`);

  const ruleLines = entries[0];
  const ruleText = ruleLines.join('\n');
  const scalar = key => {
    const prefix = `${key}:`;
    const hit = ruleLines.find(line => line.trimStart().startsWith(prefix));
    return hit ? unquote(hit.trimStart().slice(prefix.length)) : null;
  };
  assert.equal(scalar('package-ecosystem'), 'npm');
  assert.equal(scalar('directory'), '/');
  assert.equal(scalar('interval'), 'daily');
  assert.equal(scalar('versioning-strategy'), 'increase');
  assert.equal(scalar('open-pull-requests-limit'), '1');

  const allowIdx = ruleLines.findIndex(line => /^\s*allow:\s*$/.test(line));
  assert.ok(allowIdx >= 0, 'expected allow: section inside Dependabot update rule');
  const allowIndent = ruleLines[allowIdx].match(/^(\s*)/)[1].length;
  const allowItems = [];
  for (let i = allowIdx + 1; i < ruleLines.length; i++) {
    const line = ruleLines[i];
    const indent = line.match(/^(\s*)/)[1].length;
    if (indent <= allowIndent) break;
    allowItems.push(line.trim());
  }
  const allowDeps = allowItems
    .map(item => item.match(/^-\s*dependency-name:\s*(.+)$/)?.[1])
    .filter(Boolean)
    .map(unquote);
  assert.equal(allowItems.length, 1, `expected allow: block to contain exactly one entry, got ${JSON.stringify(allowItems)}`);
  assert.deepEqual(allowDeps, [RUNTIME_CLIENT_PKG], 'Dependabot allow: section must contain only the runtime client package');

  const allDepNames = [...ruleText.matchAll(/dependency-name:\s*(.+)/g)].map(m => unquote(m[1]));
  assert.deepEqual(allDepNames, [RUNTIME_CLIENT_PKG], 'no dependency-name entry may exist outside allow:');
  assert.doesNotMatch(ruleText, /\bignore:/, 'must not define ignore: alongside or instead of allow:');
  assert.doesNotMatch(ruleText, /dependency-type:/, 'must not broaden allow rule by dependency-type');
  assert.match(ruleText, /\blabels:\s*\n\s*-\s*['"]?dependencies['"]?\b/);
});

test('#3594 R1 regressions: runCheck --reconcile, non-string requestId, Stop(2)/Stop(5) exit codes, and formatCheckReconciliation sanitization', async t => {
  const setup = harbor(t);
  let networkHit = 0;
  const noNetPorts = extra => portsFor(
    { HOME: setup.home, PDD_RUNTIME_URL: 'http://127.0.0.1:9', PDD_STATE_DIR: setup.state },
    { fetch: async () => { networkHit += 1; throw new Error('must not dispatch network check'); }, ...extra },
  ).ports;

  // Finding #1 (P0): direct seam.runCheck({ options: { '--reconcile': uuid } }) never dispatches POST /v1/lint or /v1/check.
  const pUnsupported = noNetPorts({
    reconcileCheckReceipt: async () => {
      throw Object.assign(new Error(`CHECK receipt reconciliation requires ${RUNTIME_CLIENT_PKG} >= 1.1.1.`), {
        code: 'reconciliation-unsupported',
        exitCode: 5,
      });
    },
  });
  assert.equal(await seam.runCheck({ cwd: setup.repo, words: [], options: { '--reconcile': VALID_REQUEST_ID } }, pUnsupported), 5);
  assert.equal(networkHit, 0, 'runCheck --reconcile must never dispatch POST /v1/lint or /v1/check');
  assert.ok(pUnsupported.stderr.text.includes(RUNTIME_CLIENT_PKG));

  // Real >= 1.1.1 direct seam.runCheck --reconcile dispatches ONLY read-only GET /v1/runs/<uuid>/reconciliation (0 POSTs).
  const fake = await fakeRuntime(t, entry => {
    if (entry.method === 'GET' && entry.url === `/v1/runs/${VALID_REQUEST_ID}/reconciliation`) {
      return { status: 200, json: makeReconciliationBody(VALID_REQUEST_ID) };
    }
    throw new Error(`unexpected runtime call: ${entry.method} ${entry.url}`);
  });
  const pLive = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }).ports;
  assert.equal(
    await seam.runCheck({ cwd: setup.repo, words: [], options: { '--reconcile': VALID_REQUEST_ID, '--json': true } }, pLive),
    0,
    pLive.stderr.text,
  );
  assert.equal(JSON.parse(pLive.stdout.text).request_id, VALID_REQUEST_ID);
  assert.equal(fake.posts.length, 0, 'real runCheck --reconcile must never POST /v1/lint or /v1/check');
  assert.equal(fake.gets.length, 1);

  const pExtra = noNetPorts();
  assert.equal(await seam.runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--reconcile': VALID_REQUEST_ID } }, pExtra), 2);
  assert.equal(networkHit, 0);

  const pMock = noNetPorts({
    reconcileCheckReceipt: async ({ requestId }) => ({
      schema_version: 'pdd-runtime.check-reconciliation.v1',
      request_id: requestId,
      available: true,
      http_status: 200,
      disposition: { state: 'passed' },
      dispatch: { status: 'dispatched', proven: true },
      accounting: { status: 'complete_dispatched', accounting_complete: true, calls: 1, known_calls: 1, unknown_calls: 0 },
      retry: { blocked: true, safe_next_action: 'Read saved verdict.' },
    }),
  });
  assert.equal(await seam.runCheck({ cwd: setup.repo, words: [], options: { '--reconcile': VALID_REQUEST_ID, '--json': true } }, pMock), 0);
  assert.equal(JSON.parse(pMock.stdout.text).request_id, VALID_REQUEST_ID);
  assert.equal(networkHit, 0);

  // Finding #8 (P2) + R2 nit: non-string requestId (including null-prototype objects and Symbols) must reject with invalid-request-id, never TypeError.
  for (const badId of [{ toString: () => VALID_REQUEST_ID }, [VALID_REQUEST_ID], 123, null, Object.create(null), Symbol('req')]) {
    await assert.rejects(
      () => seam.reconcileCheckReceipt({ cwd: setup.repo, requestId: badId }),
      err => err?.code === 'invalid-request-id' && err?.exitCode === 2,
    );
    const pBad = noNetPorts();
    assert.equal(await seam.runCheck({ cwd: setup.repo, words: [], options: { '--reconcile': badId } }, pBad), 2);
  }

  // Finding #10 (P2): Stop(2) / Stop(5) explicit exitCode preserved (never collapsed to 3).
  for (const expectedExit of [2, 5]) {
    const out = captureStream();
    const err = captureStream();
    const code = await runPdd(['test', '--reconcile', VALID_REQUEST_ID], {
      cwd: setup.repo,
      env: { ...process.env, HOME: setup.home, PDD_STATE_DIR: setup.state },
      stdout: out,
      stderr: err,
      runtimeCheckReconcile: async () => {
        throw Object.assign(new Error(`explicit exit ${expectedExit}`), { exitCode: expectedExit });
      },
    });
    assert.equal(code, expectedExit, `expected explicit exitCode ${expectedExit} to survive`);
    assert.match(err.text, new RegExp(`explicit exit ${expectedExit}`));
  }

  // Finding #7 (P2): formatCheckReconciliation sanitizes control characters in accounting.calls / known_calls / unknown_calls.
  const formatted = formatCheckReconciliation({
    request_id: VALID_REQUEST_ID,
    http_status: 200,
    disposition: { state: 'unknown' },
    dispatch: { status: 'unproved', proven: false },
    accounting: {
      status: 'unknown',
      accounting_complete: false,
      calls: '1\npdd-workflow:fake',
      known_calls: '2\r\ninjected',
      unknown_calls: '3\u0007bell',
    },
    retry: { blocked: true },
  });
  assert.doesNotMatch(formatted, /[\r\u0007]/);
  assert.match(formatted, /Accounting: unknown \(complete=no, calls=1 pdd-workflow:fake, known=2 injected, unknown=3 bell\)/);
});

test('#3594 R1 regressions: --lf --fresh bypasses cache reuse while keeping unselected cached passes intact', async t => {
  const setup = harbor(t);
  let nowMs = Date.parse('2026-10-27T16:27:47Z');
  const stepPorts = () => {
    nowMs += 60_000;
    const base = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
    base.clock.now = nowMs;
    return base;
  };
  let failUnknown = true;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.method === 'POST' && entry.command === 'check') {
      const state = failUnknown && JSON.stringify(entry.request).includes('unknown-item') ? 'failed' : 'passed';
      f.jobs.set(entry.request.requestId, state);
      return { status: 202, json: f.check(entry.request.requestId, 'queued') };
    }
    const id = entry.url.split('/').at(-1);
    const state = f.jobs.get(id) ?? 'passed';
    return {
      status: 200,
      json: state === 'failed'
        ? f.check(id, 'failed', [{ criterion_id: 'AC1', passed: false }])
        : f.check(id, 'passed'),
    };
  });

  // 1. Run all stories: place-order passes (cached), unknown-item fails (recorded in last-failed).
  const first = stepPorts();
  assert.equal(await seam.check({ words: [], options: { '--json': true }, cwd: setup.repo }, first.ports), 1, first.ports.stderr.text);
  const initialCheckPosts = fake.posts.filter(p => p.command === 'check').length;
  assert.equal(initialCheckPosts, 2);

  // 2. Now unknown-item passes on rerun; run --lf --fresh and verify it dispatches fresh: true (not cached) and writes back pass.
  failUnknown = false;
  const lfFresh = stepPorts();
  assert.equal(
    await seam.check({ words: [], options: { '--lf': true, '--fresh': true, '--json': true }, cwd: setup.repo }, lfFresh.ports),
    0,
    lfFresh.ports.stderr.text,
  );
  const afterLfPosts = fake.posts.filter(p => p.command === 'check');
  assert.equal(afterLfPosts.length, initialCheckPosts + 1, '--lf --fresh must execute the failed story freshly');
  assert.equal(afterLfPosts.at(-1).request.fresh, true);

  // 3. Subsequent ordinary run of place-order STILL hits local cache (0 new POSTs) because --lf --fresh preserved unselected passes!
  const cachedSibling = stepPorts();
  assert.equal(
    await seam.check({ words: ['place-order'], options: { '--json': true }, cwd: setup.repo }, cachedSibling.ports),
    0,
    cachedSibling.ports.stderr.text,
  );
  assert.equal(fake.posts.filter(p => p.command === 'check').length, afterLfPosts.length, 'unselected Story cache pass must survive --lf --fresh');

  // 4. With all stories passing and cached (0 failed), plain --lf reuses cache (0 new POSTs),
  //    while --lf --fresh bypasses local cache reuse and dispatches fresh: true for every selected Story!
  const lfCached = stepPorts();
  assert.equal(
    await seam.check({ words: [], options: { '--lf': true, '--json': true }, cwd: setup.repo }, lfCached.ports),
    0,
    lfCached.ports.stderr.text,
  );
  assert.equal(fake.posts.filter(p => p.command === 'check').length, afterLfPosts.length, 'plain --lf with cached passes reuses cache');

  const lfBypass = stepPorts();
  assert.equal(
    await seam.check({ words: [], options: { '--lf': true, '--fresh': true, '--json': true }, cwd: setup.repo }, lfBypass.ports),
    0,
    lfBypass.ports.stderr.text,
  );
  const finalPosts = fake.posts.filter(p => p.command === 'check');
  assert.equal(finalPosts.length, afterLfPosts.length + 2, '--lf --fresh must bypass cached pass reuse for all selected stories');
  assert.equal(finalPosts.at(-1).request.fresh, true);
  assert.equal(finalPosts.at(-2).request.fresh, true);
});

test('#3594 R1 regressions: simulate --fresh --shell 0o600 single-session patch, existing-Try refusal, runDoorCall/runShim/openServe guards', async t => {
  const setup = harbor(t, makeCliStory);
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.url.endsWith('/model')) {
      return {
        status: 200,
        json: {
          calls: { cap: 40, remaining: 40 },
          app_map: true,
          entries: [],
        },
      };
    }
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.method === 'POST' && entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
    if (entry.method === 'DELETE') {
      const tryId = entry.url.split('/').at(-1);
      const stopId = entry.headers['x-request-id'] || VALID_REQUEST_ID;
      const stopAnswer = f.stopJob(stopId, tryId);
      f.jobs.set(stopId, stopAnswer);
      return { status: 200, json: stopAnswer };
    }
    if (entry.method === 'POST' && /^\/v1\/try\/([^/]+)\/call$/.test(entry.url)) {
      const sessionId = entry.url.match(/^\/v1\/try\/([^/]+)\/call$/)[1];
      const callId = entry.json?.requestId ?? VALID_REQUEST_ID;
      const callAnswer = {
        id: callId,
        requestId: callId,
        command: 'call',
        session_id: sessionId,
        state: 'passed',
        result: {
          program_result: { stdout: 'hi\n', stderr: '', exit_code: 0 },
          world: {},
          input_world: {},
          session: { id: sessionId },
        },
        usage: { calls: 1, cap: 40, remaining: 39 },
      };
      f.jobs.set(callId, callAnswer);
      return { status: 200, json: callAnswer };
    }
    if (entry.method === 'POST' && /^\/v1\/try\/([^/]+)\/screen\/api\/act$/.test(entry.url)) {
      return { status: 200, json: { ok: true } };
    }
    if (entry.method === 'GET' && f.jobs.has(entry.url.split('/').at(-1))) {
      return { status: 200, json: f.jobs.get(entry.url.split('/').at(-1)) };
    }
    return { status: 200, json: f.tryJob(entry.url.split('/').at(-1)) };
  });

  // Seed an UNRELATED existing CLI door descriptor (must NOT be touched by --fresh for this session).
  const unrelatedId = '99999999-9999-4999-8999-999999999999';
  const triesDir = join(setup.state, 'tries');
  mkdirSync(triesDir, { recursive: true });
  const unrelatedDoorPath = join(triesDir, `${unrelatedId}.door.json`);
  writeFileSync(unrelatedDoorPath, `${JSON.stringify({ version: 1, sessionId: unrelatedId }, null, 2)}\n`, { mode: 0o600 });

  // Finding #3 (P1): --cli --shell --fresh patches THIS session's .door.json BEFORE shell launches, with mode 0o600,
  // and leaves unrelated open CLI sessions untouched!
  let freshInsideShell = null;
  let modeInsideShell = null;
  let doorPathInsideShell = null;
  const shellPorts = portsFor(
    { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state },
    {
      stdin: Readable.from([]),
      openUrl: async () => false,
      shell: async () => {
        const launcher = readFileSync(join(setup.repo, '.pdd/try/bin/paperclip'), 'utf8');
        doorPathInsideShell = launcher.match(/([^\s'"]+\.door\.json)/)?.[1] ?? null;
        if (doorPathInsideShell) {
          freshInsideShell = JSON.parse(readFileSync(doorPathInsideShell, 'utf8')).fresh === true;
          modeInsideShell = statSync(doorPathInsideShell).mode & 0o777;
        }
        return 0;
      },
    },
  );
  assert.equal(
    await seam.simulate({ words: ['place-order'], mode: 'cli', fresh: true, options: { '--shell': true }, cwd: setup.repo }, shellPorts.ports),
    0,
    shellPorts.ports.stderr.text,
  );
  assert.equal(freshInsideShell, true, '.door.json must be patched fresh: true BEFORE --shell launches');
  assert.equal(modeInsideShell, 0o600, '.door.json must keep 0o600 permissions');
  assert.equal(JSON.parse(readFileSync(unrelatedDoorPath, 'utf8')).fresh, undefined, 'unrelated session door must remain untouched');

  // Finding #4 (P1): simulate [STORY] --fresh without --new fails closed (exit 2) when a Try is already open!
  const postsBeforeReuse = fake.posts.length;
  const reusePorts = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }, { openUrl: async () => true });
  assert.equal(
    await seam.simulate({ words: ['place-order'], fresh: true, options: { '--no-wait': true }, cwd: setup.repo }, reusePorts.ports),
    2,
    'simulate --fresh without --new must fail closed when a Try is already open',
  );
  assert.match(reusePorts.ports.stderr.text, /--new/);
  assert.equal(fake.posts.length, postsBeforeReuse, 'refused --fresh without --new must not silently reuse or post');

  // Passing --new alongside --fresh replaces the open Try cleanly.
  const replacePorts = portsFor(
    { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state },
    { stdin: Readable.from([]), openUrl: async () => false },
  );
  assert.equal(
    await seam.simulate({ words: ['place-order'], mode: 'cli', fresh: true, options: { '--new': true }, cwd: setup.repo }, replacePorts.ports),
    0,
    replacePorts.ports.stderr.text,
  );

  // Finding #5 (P2): runDoorCall inspects ONLY descriptor.fresh (never domain payload input.fresh).
  const nonFreshDescriptor = {
    ...JSON.parse(readFileSync(doorPathInsideShell, 'utf8')),
    fresh: undefined,
  };
  delete nonFreshDescriptor.fresh;
  const doorPorts = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  await seam.runDoorCall(nonFreshDescriptor, { argv: ['hi'], fresh: true }, doorPorts.ports);
  const lastCallPost = fake.jsonPosts.filter(p => /^\/v1\/try\/[^/]+\/call$/.test(p.url)).at(-1);
  assert.equal(lastCallPost.json.fresh, undefined, 'runDoorCall must not lift domain input.fresh onto transport body');

  // Finding #9 (P2): runShim ignores symlinked descriptorPath when checking fresh flag.
  const symlinkDoorPath = join(setup.sandbox, 'symlink.door.json');
  symlinkSync(doorPathInsideShell, symlinkDoorPath);
  const shimPorts = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }, { stdin: Readable.from([]) });
  const shimCode = await seam.runShim(symlinkDoorPath, ['hi'], shimPorts.ports);
  assert.equal(shimCode, 125, 'symlinked descriptor must be refused');

  // Finding #6 (P2): direct seam.openServe(..., { '--fresh': true }) injects fresh: true on Screen POSTs via context.runtime.send.
  const serveSessionId = nonFreshDescriptor.sessionId;
  const baseFetch = globalThis.fetch;
  const servePorts = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }, { fetch: baseFetch }).ports;
  const runtimeProto = {
    async send(path, init) {
      const response = await this.ports.fetch(new URL(path, this.origin), init);
      const text = await response.text();
      let json = null;
      try { json = JSON.parse(text); } catch {}
      return { status: response.status, headers: response.headers, text, json };
    },
  };
  const fakeRuntimeClient = Object.assign(Object.create(runtimeProto), { origin: fake.origin, ports: servePorts });
  let screenStatus = 0;
  servePorts.serve = async server => {
    const port = server.address().port;
    const res = await baseFetch(`http://127.0.0.1:${port}/__pdd/screen/api/act`, {
      method: 'POST',
      headers: { 'content-type': 'application/json', host: `127.0.0.1:${port}` },
      body: JSON.stringify({ action: 'tap' }),
    });
    screenStatus = res.status;
  };
  const serveCode = await seam.openServe(
    {
      root: setup.repo,
      origin: fake.origin,
      identity: { login: 'octo', token: TOKEN },
      ports: servePorts,
      runtime: fakeRuntimeClient,
      signal: new AbortController().signal,
    },
    { path: 'tests/place-order.json', story: 'place-order' },
    serveSessionId,
    { '--serve': 0, '--fresh': true },
  );
  assert.equal(serveCode, 0);
  assert.equal(screenStatus, 200);
  const screenPosts = fake.jsonPosts.filter(p => /^\/v1\/try\/[^/]+\/screen\/api\/act$/.test(p.url));
  assert.equal(screenPosts.length, 1);
  assert.equal(screenPosts[0].json.fresh, true, 'openServe --fresh must inject fresh: true on Screen POSTs');
});

test('#3594 R2/R3 regression: pdd --product --fresh handles open, sibling, journey, and absent product Tries accurately', async t => {
  // 0. When NO product Try is open, --product --fresh proceeds cleanly without false refusal.
  const cleanSetup = harbor(t);
  let cleanInvoked = false;
  const cleanPorts = portsFor(
    { HOME: cleanSetup.home, PDD_STATE_DIR: cleanSetup.state },
    { runTry: async () => { cleanInvoked = true; return 0; } },
  );
  assert.equal(
    await seam.simulate({ words: [], fresh: true, options: { '--product': true, '--no-wait': true }, cwd: cleanSetup.repo }, cleanPorts.ports),
    0,
    cleanPorts.ports.stderr.text,
  );
  assert.equal(cleanInvoked, true, '--product --fresh must proceed when no product Try is open');

  const setup = harbor(t, repo => {
    mkdirSync(join(repo, 'user_stories/journeys'), { recursive: true });
    writeFileSync(
      join(repo, 'user_stories/journeys/checkout.md'),
      '# Checkout Journey\n\nI can place a coffee order.\n\n## Acceptance criteria\n\n1. Order succeeds.\n',
    );
    const baseTest = JSON.parse(readFileSync(join(repo, 'tests/place-order.json'), 'utf8'));
    writeFileSync(
      join(repo, 'tests/checkout.json'),
      `${JSON.stringify({ ...baseTest, story_path: 'user_stories/journeys/checkout.md' }, null, 2)}\n`,
    );
  });
  const realRoot = realpathSync(setup.repo);
  const repoKey = createHash('sha256').update(realRoot).digest('hex').slice(0, 16);
  const reposDir = join(setup.state, 'repos');
  mkdirSync(reposDir, { recursive: true });
  const repoStatePath = join(reposDir, `${repoKey}.json`);
  writeFileSync(
    repoStatePath,
    `${JSON.stringify({
      root: realRoot,
      last_batch: null,
      tries: {
        'tests/place-order.json': {
          id: VALID_REQUEST_ID,
          story: 'place-order',
          storyPath: 'user_stories/place-order.md',
          product_setup: { parts: null, journey: null },
        },
      },
    }, null, 2)}\n`,
  );

  // 1. Explicit Story target `--product place-order --fresh` fails closed via resolved target branch and names the Story.
  let invokedTry = false;
  const targetPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state },
    { runTry: async () => { invokedTry = true; return 0; } },
  );
  assert.equal(
    await seam.simulate({ words: ['place-order'], fresh: true, options: { '--product': true, '--no-wait': true }, cwd: setup.repo }, targetPorts.ports),
    2,
    '--product place-order --fresh without --new must fail closed when place-order has an open Try',
  );
  assert.match(targetPorts.ports.stderr.text, /pdd --product place-order --fresh --new/);
  assert.equal(invokedTry, false);

  // 2. Sibling Story target `--product unknown-item --fresh` (while place-order has an open product Try) MUST proceed cleanly!
  let siblingInvoked = false;
  const siblingPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state },
    { runTry: async () => { siblingInvoked = true; return 0; } },
  );
  assert.equal(
    await seam.simulate({ words: ['unknown-item'], fresh: true, options: { '--product': true, '--no-wait': true }, cwd: setup.repo }, siblingPorts.ports),
    0,
    siblingPorts.ports.stderr.text,
  );
  assert.equal(siblingInvoked, true, '--product unknown-item --fresh must NOT be falsely refused by place-order open Try');

  // 3. Explicit `--product --journey checkout --fresh` fails closed when checkout journey Try is open (and names --journey).
  writeFileSync(
    repoStatePath,
    `${JSON.stringify({
      root: realRoot,
      last_batch: null,
      tries: {
        'tests/checkout.json': {
          id: VALID_REQUEST_ID,
          story: 'checkout',
          storyPath: 'user_stories/journeys/checkout.md',
          product_setup: { parts: null, journey: 'checkout' },
        },
      },
    }, null, 2)}\n`,
  );
  let journeyInvoked = false;
  const journeyPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state },
    { runTry: async () => { journeyInvoked = true; return 0; } },
  );
  assert.equal(
    await seam.simulate({ words: [], fresh: true, options: { '--product': true, '--journey': 'checkout', '--no-wait': true }, cwd: setup.repo }, journeyPorts.ports),
    2,
    '--product --journey checkout --fresh without --new must fail closed when checkout journey Try is open',
  );
  assert.match(journeyPorts.ports.stderr.text, /pdd --product --journey checkout --fresh --new/);
  assert.equal(journeyInvoked, false);

  // 4. Bare `--product --fresh` without --new fails closed when the unique open product Try matches, and `--new` proceeds.
  let bareInvoked = false;
  const prodPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state },
    { runTry: async () => { bareInvoked = true; return 0; } },
  );
  assert.equal(
    await seam.simulate({ words: [], fresh: true, options: { '--product': true, '--no-wait': true }, cwd: setup.repo }, prodPorts.ports),
    2,
  );
  assert.match(prodPorts.ports.stderr.text, /pdd --product --fresh --new/);
  assert.equal(bareInvoked, false);

  let newInvoked = false;
  const newProdPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state },
    { runTry: async () => { newInvoked = true; return 0; } },
  );
  assert.equal(
    await seam.simulate({ words: [], fresh: true, options: { '--product': true, '--new': true, '--no-wait': true }, cwd: setup.repo }, newProdPorts.ports),
    0,
    newProdPorts.ports.stderr.text,
  );
  assert.equal(newInvoked, true, '--product --fresh --new must proceed to runtimeRunTry');
});

test('runtime-client 1.1.2: reconcileCheckBatch, reconcileStaleReservations, --reconcile BATCH, --reconcile-stale, and --batch-timeout work end-to-end', async t => {
  const BATCH_ID = '20261121-000100-ab12';
  assert.deepEqual(parseArgv(['test', '--reconcile', BATCH_ID, '--json']).options, {
    '--reconcile': BATCH_ID,
    '--json': true,
  });
  assert.deepEqual(parseArgv(['test', '--reconcile-stale', '--json']).options, {
    '--reconcile-stale': true,
    '--json': true,
  });
  assert.deepEqual(parseArgv(['test', '--batch-timeout', '45']).options, {
    '--batch-timeout': '45',
  });
  assert.deepEqual(parseArgv(['test', '--read', BATCH_ID, '--batch-timeout', '15']).options, {
    '--read': true,
    '--batch-timeout': '15',
  });
  for (const invalid of [
    ['test', '--reconcile', 'not-a-batch-or-uuid'],
    ['test', '--reconcile-stale=true'],
    ['test', '--batch-timeout', '0'],
    ['test', '--batch-timeout', '1441'],
    ['lint', '--batch-timeout', '5'],
    ['lint', '--reconcile-stale'],
  ]) {
    assert.throws(() => parseArgv(invalid), CommandInputError, invalid.join(' '));
  }

  // Seam runtimeClientSlice overlays seam-bound reconciliation helpers.
  const slice = seam.runtimeClientSlice();
  assert.equal(slice.reconcileCheckReceipt, seam.reconcileCheckReceipt);
  assert.equal(slice.reconcileCheckBatch, seam.reconcileCheckBatch);
  assert.equal(slice.reconcileStaleReservations, seam.reconcileStaleReservations);

  const setup = harbor(t);
  for (const badBatch of [{ toString: () => BATCH_ID }, [BATCH_ID], 123, null, Object.create(null), Symbol('batch')]) {
    await assert.rejects(
      () => seam.reconcileCheckBatch({ cwd: setup.repo, batchId: badBatch }),
      err => err?.code === 'invalid-batch-id' && err?.exitCode === 2,
    );
  }

  // Real 1.1.2 batch reconciliation on an already-resolved saved batch (0 network POSTs).
  const batchDir = join(setup.state, 'batches', BATCH_ID);
  mkdirSync(batchDir, { recursive: true });
  writeFileSync(
    join(batchDir, 'batch.json'),
    `${JSON.stringify({
      version: 1,
      batch: BATCH_ID,
      intent: 'check',
      root: setup.repo,
      rows: [
        { test: 'tests/place-order.json', story: 'place-order', state: 'passed', calls: 1, accounting_complete: true, request_ids: [VALID_REQUEST_ID] },
      ],
    }, null, 2)}\n`,
  );

  const noNetEnv = {
    ...process.env,
    HOME: setup.home,
    PDD_STATE_DIR: setup.state,
    PDD_RUNTIME_URL: 'http://127.0.0.1:9',
  };
  const batchRes = await seam.reconcileCheckBatch(
    { cwd: setup.repo, batchId: BATCH_ID },
    portsFor(noNetEnv, { fetch: async () => { throw new Error('must not call network for already-resolved batch'); } }).ports,
  );
  assert.equal(batchRes.schema_version, 'pdd-runtime.batch-reconciliation.v1');
  assert.equal(batchRes.batch, BATCH_ID);
  assert.equal(batchRes.status, 'already-resolved');
  assert.equal(batchRes.remaining_unresolved_count, 0);

  const batchJsonOut = captureStream();
  const batchJsonErr = captureStream();
  assert.equal(
    await runPdd(['test', '--reconcile', BATCH_ID, '--json'], { cwd: setup.repo, env: noNetEnv, stdout: batchJsonOut, stderr: batchJsonErr }),
    0,
    batchJsonErr.text,
  );
  assert.equal(JSON.parse(batchJsonOut.text).status, 'already-resolved');

  const batchTextOut = captureStream();
  const batchTextErr = captureStream();
  assert.equal(
    await runPdd(['test', '--reconcile', BATCH_ID], { cwd: setup.repo, env: noNetEnv, stdout: batchTextOut, stderr: batchTextErr }),
    0,
    batchTextErr.text,
  );
  assert.match(batchTextOut.text, new RegExp(`Batch ${BATCH_ID}: no unresolved prior reservations remain\\.`));

  // Real 1.1.2 stale reservation reconciliation when no unresolved reservations exist.
  const staleRes = await seam.reconcileStaleReservations(
    { cwd: setup.repo },
    portsFor(noNetEnv, { fetch: async () => { throw new Error('must not call network when no stale reservations exist'); } }).ports,
  );
  assert.equal(staleRes.schema_version, 'pdd-runtime.stale-reconciliation.v1');
  assert.equal(staleRes.batches_inspected, 0);
  assert.equal(staleRes.remaining_unresolved_count, 0);

  const staleOut = captureStream();
  const staleErr = captureStream();
  assert.equal(
    await runPdd(['test', '--reconcile-stale'], { cwd: setup.repo, env: noNetEnv, stdout: staleOut, stderr: staleErr }),
    0,
    staleErr.text,
  );
  assert.match(staleOut.text, /No unresolved prior reservations found for this repository\./);

  const staleJsonOut = captureStream();
  const staleJsonErr = captureStream();
  assert.equal(
    await runPdd(['test', '--reconcile-stale', '--json'], { cwd: setup.repo, env: noNetEnv, stdout: staleJsonOut, stderr: staleJsonErr }),
    0,
    staleJsonErr.text,
  );
  assert.equal(JSON.parse(staleJsonOut.text).batches_inspected, 0);

  // Invalid mixes with --reconcile-stale fail closed with exit 2.
  for (const argv of [
    ['test', '--reconcile-stale', '--fresh'],
    ['test', '--reconcile-stale', 'place-order'],
    ['test', '--reconcile', BATCH_ID, '--reconcile-stale'],
  ]) {
    const out = captureStream();
    const err = captureStream();
    assert.equal(await runPdd(argv, { cwd: setup.repo, env: noNetEnv, stdout: out, stderr: err }), 2, argv.join(' '));
  }

  // Formatters sanitize control characters cleanly.
  const batchFmt = formatBatchReconciliation({
    batch: `${BATCH_ID}\nfake`,
    cleared_count: 1,
    settled_count: 1,
    remaining_unresolved_count: 0,
    rows: [{ test: 'tests/a.json\r\nbad', status: 'settled', calls: 2, cleared: true, reason: 'ok\u0007' }],
  });
  assert.doesNotMatch(batchFmt, /[\r\u0007]/);
  assert.match(batchFmt, /Reconciled batch 20261121-000100-ab12 fake: 1 cleared \(1 settled\), 0 remaining unresolved\./);
  const staleFmt = formatStaleReconciliation({
    batches_inspected: 1,
    cleared_count: 1,
    remaining_unresolved_count: 0,
    batches: [{ batch: BATCH_ID, status: 'reconciled', cleared_count: 1, remaining_unresolved_count: 0 }],
  });
  assert.match(staleFmt, /Reconciled 1 prior batch: 1 reservation cleared, 0 remaining unresolved\./);
});

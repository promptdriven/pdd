import './helpers/test-home.mjs';
import './helpers/test-net-guard.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { chmodSync, existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { delimiter, dirname, join, resolve } from 'node:path';
import { Readable } from 'node:stream';
import { fileURLToPath } from 'node:url';
import * as seam from '../src/runtime-seam.mjs';
import { CommandInputError, parseArgv } from '../src/argument-parser.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { formatCheckReconciliation, savedCheckReconciliationTargets } from '../src/workflow-results.mjs';
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

test('#3431 / #3594: runtime-client 1.1.0 accepts pdd-bindings.json { module, prompt } without stories on pdd test --files', async t => {
  const pkg = JSON.parse(readFileSync(join(repoRoot, 'package.json'), 'utf8'));
  assert.equal(pkg.dependencies[RUNTIME_CLIENT_PKG], '1.1.0');
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

test('#3594: pdd simulate --fresh forwards fresh: true to POST /v1/try, CLI door descriptors, and runDoorCall', async t => {
  assert.deepEqual(parseArgv(['simulate', 'place-order', '--fresh']).options, { '--fresh': true });
  assert.deepEqual(parseArgv(['simulate', 'place-order', '--cli', '--fresh']).options, { '--cli': true, '--fresh': true });
  assert.throws(() => parseArgv(['simulate', '--fresh=1']), CommandInputError);

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

  const readPorts = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  const readCode = await seam.read({ batch: batchId, details: true, cwd: setup.repo }, readPorts.ports);
  assert.equal(readCode, 1, `expected saved failure exit 1 (not option refusal 2), stderr:\n${readPorts.ports.stderr.text}`);
  assert.doesNotMatch(readPorts.ports.stderr.text, /This mix of options does not work together/);
  assert.match(readPorts.ports.stdout.text, /place-order/);

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

  // Invalid extra flag alongside --read --details still fails closed with exit 2.
  const badPorts = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(
    await seam.runCheck({ words: [batchId], options: { '--read': true, '--details': true, '--lf': true }, cwd: setup.repo }, badPorts.ports),
    2,
  );
});

test('#3594: pdd test --reconcile fails closed on 1.1.0, validates inputs, supports mocked read-only JSON & text paths, and reads saved targets', async t => {
  assert.deepEqual(parseArgv(['test', '--reconcile', VALID_REQUEST_ID, '--json']).options, {
    '--reconcile': VALID_REQUEST_ID,
    '--json': true,
  });
  assert.throws(() => parseArgv(['test', '--reconcile', 'not-a-uuid']), CommandInputError);

  const setup = harbor(t);

  // 1. Direct seam helpers fail closed cleanly on 1.1.0 (never TypeError).
  await assert.rejects(
    () => seam.reconcileCheckReceipt({ cwd: setup.repo, requestId: VALID_REQUEST_ID }),
    err => err?.code === 'reconciliation-unsupported' && err?.exitCode === 5 && err.message.includes('>= 1.2.0') && err.message.includes(RUNTIME_CLIENT_PKG),
  );
  assert.throws(
    () => seam.projectCheckReconciliation({ requestId: VALID_REQUEST_ID }),
    err => err?.code === 'reconciliation-unsupported' && err?.exitCode === 5 && err.message.includes('>= 1.2.0'),
  );
  await assert.rejects(
    () => seam.reconcileCheckReceipt({ cwd: setup.repo, requestId: 'bad-id' }),
    err => err?.code === 'invalid-request-id' && err?.exitCode === 2,
  );

  // 2. CLI fallback on 1.1.0 fails closed with exit 5 and actionable upgrade message.
  const fallbackOut = captureStream();
  const fallbackErr = captureStream();
  const fallbackCode = await runPdd(['test', '--reconcile', VALID_REQUEST_ID], {
    cwd: setup.repo,
    env: { ...process.env, HOME: setup.home, PDD_STATE_DIR: setup.state },
    stdout: fallbackOut,
    stderr: fallbackErr,
  });
  assert.equal(fallbackCode, 5);
  assert.match(fallbackErr.text, />= 1\.2\.0/);
  assert.ok(fallbackErr.text.includes(RUNTIME_CLIENT_PKG));

  // 3. CLI rejects invalid option/operand mixes with exit 2.
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

  // 4. Mocked happy path (available: true, complete_zero) in both JSON and human-text modes.
  const completeZeroRecord = {
    schema_version: 'pdd-runtime.check-reconciliation.v1',
    request_id: VALID_REQUEST_ID,
    available: true,
    http_status: 200,
    error_code: null,
    disposition: { state: 'not_dispatched', verdict: null, refusal_code: 'capacity-full', expired: false, purged: false },
    dispatch: { status: 'not_dispatched', proven: true },
    accounting: { status: 'complete_zero', accounting_complete: true, calls: 0, known_calls: 0, unknown_calls: 0, cap: 40 },
    retry: { blocked: false, safe_next_action: 'Safe to submit a replacement check with a new request ID.' },
    evidence: { proof_basis: ['server_receipt_not_dispatched'], contradictions: [] },
    provenance: { source_sha256: 'a'.repeat(64), engine_sha: 'b'.repeat(40), server_commit: 'c'.repeat(40), sources_consulted: ['receipt_store'] },
  };
  const reconcileCalls = [];
  const mockReconcile = async (input, ports) => {
    reconcileCalls.push({ input, ports });
    return completeZeroRecord;
  };

  const jsonOut = captureStream();
  const jsonErr = captureStream();
  const jsonCode = await runPdd(['test', '--reconcile', VALID_REQUEST_ID, '--json'], {
    cwd: setup.repo,
    env: { ...process.env, HOME: setup.home, PDD_STATE_DIR: setup.state },
    stdout: jsonOut,
    stderr: jsonErr,
    runtimeCheckReconcile: mockReconcile,
  });
  assert.equal(jsonCode, 0, jsonErr.text);
  assert.deepEqual(JSON.parse(jsonOut.text), completeZeroRecord);
  assert.equal(reconcileCalls.length, 1);
  assert.equal(reconcileCalls[0].input.requestId, VALID_REQUEST_ID);

  const textOut = captureStream();
  const textErr = captureStream();
  const textCode = await runPdd(['test', '--reconcile', VALID_REQUEST_ID], {
    cwd: setup.repo,
    env: { ...process.env, HOME: setup.home, PDD_STATE_DIR: setup.state },
    stdout: textOut,
    stderr: textErr,
    runtimeCheckReconcile: mockReconcile,
  });
  assert.equal(textCode, 0, textErr.text);
  assert.match(textOut.text, /CHECK reconciliation 11111111-1111-4111-8111-111111111111 \(read-only; HTTP 200\)/);
  assert.match(textOut.text, /Dispatch: not_dispatched \(proven\)/);
  assert.match(textOut.text, /Accounting: complete_zero \(complete=yes, calls=0, known=0, unknown=0, cap=40\)/);
  assert.match(textOut.text, /Retry blocked: no/);

  // 5. Mocked fail-closed unavailable record (HTTP 410 expired) returns exit 3 and keeps retry blocked.
  const expiredRecord = {
    schema_version: 'pdd-runtime.check-reconciliation.v1',
    request_id: VALID_REQUEST_ID,
    available: false,
    http_status: 410,
    error_code: 'receipt-expired',
    disposition: { state: 'unknown', verdict: null, refusal_code: null, expired: true, purged: false },
    dispatch: { status: 'unproved', proven: false },
    accounting: { status: 'unknown', accounting_complete: false, calls: 'unknown', known_calls: 0, unknown_calls: null, cap: null },
    retry: { blocked: true, safe_next_action: 'Do not automatically retry; receipt expired.' },
    evidence: { proof_basis: [], contradictions: ['expired-before-reconcile'] },
    provenance: { sources_consulted: ['receipt_store'] },
  };
  const expOut = captureStream();
  const expErr = captureStream();
  const expCode = await runPdd(['test', '--reconcile', VALID_REQUEST_ID], {
    cwd: setup.repo,
    env: { ...process.env, HOME: setup.home, PDD_STATE_DIR: setup.state },
    stdout: expOut,
    stderr: expErr,
    runtimeCheckReconcile: async () => expiredRecord,
  });
  assert.equal(expCode, 3, expErr.text);
  assert.match(expOut.text, /expired=yes/);
  assert.match(expOut.text, /Retry blocked: yes/);
  assert.match(expOut.text, /Error: receipt-expired/);
  assert.equal(formatCheckReconciliation(null), 'CHECK reconciliation: unavailable (malformed response).');

  // 6. Seam DI forwarding for reconcileCheckReceipt & projectCheckReconciliation.
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

  // 7. Read-only savedCheckReconciliationTargets extracts canonical UUIDs without modifying saved batch JSON.
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

  const lostOnly = savedCheckReconciliationTargets(batchName, {
    env: { PDD_STATE_DIR: setup.state },
    root: setup.repo,
  });
  assert.deepEqual(lostOnly.requestIds, [VALID_REQUEST_ID]);
  assert.equal(lostOnly.requests.length, 1);

  const allTargets = savedCheckReconciliationTargets(batchName, {
    env: { PDD_STATE_DIR: setup.state },
    root: setup.repo,
    includeAll: true,
  });
  assert.deepEqual(allTargets.requestIds, [VALID_REQUEST_ID, '22222222-2222-4222-8222-222222222222']);
  assert.equal(readFileSync(batchPath, 'utf8'), rawSaved, 'savedCheckReconciliationTargets must remain strictly read-only');
});

test('#3594: checkRuntimeClientParity validates real repo package.json pinned at 1.1.0 cleanly offline', () => {
  const matched = checkRuntimeClientParity({
    root: repoRoot,
    dryRun: false,
    runCommand: () => ({ status: 0, stdout: '1.1.0\n', stderr: '' }),
    log: () => {},
  });
  assert.equal(matched.ok, true);
  assert.equal(matched.skipped, false);
  assert.equal(matched.stale, false);
  assert.equal(matched.pinned, '1.1.0');
  assert.equal(matched.latest, '1.1.0');

  assert.throws(
    () => checkRuntimeClientParity({
      root: repoRoot,
      dryRun: false,
      runCommand: () => ({ status: 0, stdout: '1.2.0\n', stderr: '' }),
      log: () => {},
    }),
    /pinned to 1\.1\.0, behind latest published 1\.2\.0/,
  );
});

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

test('#3594 R1 regressions: runCheck --reconcile, non-string requestId, Stop(2)/Stop(5) exit codes, and formatCheckReconciliation sanitization', async t => {
  const setup = harbor(t);
  let networkHit = 0;
  const noNetPorts = extra => portsFor(
    { HOME: setup.home, PDD_RUNTIME_URL: 'http://127.0.0.1:9', PDD_STATE_DIR: setup.state },
    { fetch: async () => { networkHit += 1; throw new Error('must not dispatch network check'); }, ...extra },
  ).ports;

  // Finding #1 (P0): direct seam.runCheck({ options: { '--reconcile': uuid } }) never dispatches POST /v1/check.
  const pUnsupported = noNetPorts();
  assert.equal(await seam.runCheck({ cwd: setup.repo, words: [], options: { '--reconcile': VALID_REQUEST_ID } }, pUnsupported), 5);
  assert.equal(networkHit, 0, 'runCheck --reconcile must never dispatch POST /v1/lint or /v1/check');
  assert.match(pUnsupported.stderr.text, />= 1\.2\.0/);

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

  // Finding #7 (P2): formatCheckReconciliation sanitizes accounting.calls / known_calls / unknown_calls.
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
  assert.doesNotMatch(formatted, /pdd-workflow:fake/);
  assert.match(formatted, /pdd-workflow\\u003afake/);
  assert.match(formatted, /Accounting: unknown \(complete=no, calls=1 pdd-workflow\\u003afake, known=2 injected, unknown=3 bell\)/);
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

test('#3594 R2 regression: pdd simulate --product --fresh without --new fails closed when a product Try is already open', async t => {
  const setup = harbor(t);
  const realRoot = realpathSync(setup.repo);
  const repoKey = createHash('sha256').update(realRoot).digest('hex').slice(0, 16);
  const reposDir = join(setup.state, 'repos');
  mkdirSync(reposDir, { recursive: true });
  writeFileSync(
    join(reposDir, `${repoKey}.json`),
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

  let invokedTry = false;
  const prodPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state },
    {
      runTry: async () => {
        invokedTry = true;
        return 0;
      },
    },
  );
  const code = await seam.simulate(
    { words: [], fresh: true, options: { '--product': true, '--no-wait': true }, cwd: setup.repo },
    prodPorts.ports,
  );
  assert.equal(code, 2, 'simulate --product --fresh without --new must fail closed when a product Try is already open');
  assert.match(prodPorts.ports.stderr.text, /pdd simulate --product --fresh --new/);
  assert.equal(invokedTry, false, 'refused --product --fresh without --new must not invoke runtimeRunTry');

  // With --new, --product --fresh passes the pre-check and reaches runtimeRunTry cleanly.
  const newProdPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state },
    {
      runTry: async () => {
        invokedTry = true;
        return 0;
      },
    },
  );
  const newCode = await seam.simulate(
    { words: [], fresh: true, options: { '--product': true, '--new': true, '--no-wait': true }, cwd: setup.repo },
    newProdPorts.ports,
  );
  assert.equal(newCode, 0, newProdPorts.ports.stderr.text);
  assert.equal(invokedTry, true, '--product --fresh --new must proceed to runtimeRunTry');
});

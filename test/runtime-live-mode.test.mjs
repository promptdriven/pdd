import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { captureSource, tarFiles } from '../src/runtime-preflight.mjs';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

const git = (cwd, ...args) => {
  const r = spawnSync('git', args, { cwd, encoding: 'utf8' });
  assert.equal(r.status, 0, r.stderr);
};
const readJson = path => JSON.parse(readFileSync(path, 'utf8'));
const writeJson = (path, value) => writeFileSync(path, `${JSON.stringify(value, null, 2)}\n`);

const BINDINGS_DOC = {
  schema_version: 'prompt-runtime.live-resource-bindings.v1',
  operations: [
    {
      resource: 'git',
      operation: 'log',
      kind: 'command',
      access: 'read',
      template: {
        executable: 'pdd-git',
        subcommand: ['log'],
        argv: [{ literal: '--project' }, { target: 'project' }],
      },
    },
  ],
};

const RUN_CONFIG_DOC = {
  schema_version: 'prompt-runtime.live-resource-run-config.v1',
  mode: 'live',
  max_live_calls: 4,
  allow_live_writes: false,
  command: {
    allowed_executables: ['pdd-git'],
    allowed_subcommands: [['log']],
    sandbox_projects: ['pdd-live-example'],
    targets: { project: 'pdd-live-example' },
  },
  http: null,
  model: null,
};

function addLiveFiles(repo, { bindings = BINDINGS_DOC, runConfig = RUN_CONFIG_DOC, live = {
  resource_bindings: 'runtime/live-resources.json',
  resource_run_config: 'run-config.json',
} } = {}) {
  mkdirSync(join(repo, 'runtime'), { recursive: true });
  writeJson(join(repo, 'runtime/live-resources.json'), bindings);
  writeJson(join(repo, 'run-config.json'), runConfig);
  const testFile = join(repo, 'tests/place-order.json');
  const doc = readJson(testFile);
  if (live !== null) doc.live = live;
  writeJson(testFile, doc);
}

// Simulated mode remains the default: POST /v1/check sends only {requestId, source_sha256, scenario, max_calls}.
test('LIVE-MODE1: simulated mode stays default and unchanged on check, lint and try', async t => {
  const { repo, home, state } = harbor(t);
  const fake = await fakeRuntime(t, entry => {
    if (entry.method === 'POST' && entry.command === 'try') return { status: 200, json: fake.tryJob(entry.request.requestId) };
    return fake.normal(entry);
  });
  const env = { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: fake.origin };

  const { ports } = portsFor(env);
  assert.equal(await runCheck({ words: ['place-order'], options: { '--json': true }, cwd: repo }, ports), 0, ports.stderr.text);
  const checkPost = fake.posts.find(p => p.command === 'check');
  assert.deepEqual(Object.keys(checkPost.request).sort(), ['max_calls', 'requestId', 'scenario', 'source_sha256']);
  assert.equal(checkPost.request.resource_mode, undefined);
  assert.equal(checkPost.request.resource_bindings, undefined);
  assert.equal(checkPost.request.resource_run_config, undefined);

  const out = JSON.parse(ports.stdout.text);
  assert.equal(out.rows[0].resource_mode, undefined);
  assert.equal(out.rows[0].max_live_calls, undefined);
  assert.equal(out.rows[0].cost, undefined);
});

// Live mode sends resource_mode, resource_bindings and resource_run_config on check only, keeps max_calls and records max_live_calls.
test('LIVE-MODE2: live test config sends the three fields on check only, strips live from scenario tar, and never sends them on lint or try', async t => {
  const { repo, home, state } = harbor(t, r => addLiveFiles(r));
  const fake = await fakeRuntime(t, entry => {
    if (entry.method === 'POST' && entry.command === 'try') return { status: 200, json: fake.tryJob(entry.request.requestId) };
    return fake.normal(entry);
  });
  const env = { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: fake.origin };

  // 1. Standalone lint never sends the three live fields.
  const lintRun = portsFor(env);
  assert.equal(await runCheck({ words: ['place-order'], options: { '--lint': true, '--json': true }, cwd: repo }, lintRun.ports), 0, lintRun.ports.stderr.text);
  const lintPost = fake.posts.find(p => p.command === 'lint');
  assert.equal(lintPost.request.resource_mode, undefined);
  assert.equal(lintPost.request.resource_bindings, undefined);
  assert.equal(lintPost.request.resource_run_config, undefined);

  // 2. Try (pdd simulate) never sends the three live fields.
  const tryRun = portsFor(env);
  assert.equal(await runTry({ words: ['place-order'], options: { '--no-open': true, '--no-wait': true }, cwd: repo }, tryRun.ports), 0, tryRun.ports.stderr.text);
  const tryPost = fake.posts.find(p => p.command === 'try');
  assert.equal(tryPost.request.resource_mode, undefined);
  assert.equal(tryPost.request.resource_bindings, undefined);
  assert.equal(tryPost.request.resource_run_config, undefined);

  // 3. Check sends the three fields, includes both files in the upload tar, strips `live` from uploaded scenario bytes, and records max_live_calls.
  const checkRun = portsFor(env);
  assert.equal(await runCheck({ words: ['place-order'], options: { '--json': true, '--max-calls': '30' }, cwd: repo, cache: true }, checkRun.ports), 0, checkRun.ports.stderr.text);
  const checkPosts = fake.posts.filter(p => p.command === 'check');
  assert.equal(checkPosts.length, 1);
  const checkReq = checkPosts[0].request;
  assert.equal(checkReq.scenario, 'tests/place-order.json');
  assert.equal(checkReq.max_calls, 30);
  assert.equal(checkReq.resource_mode, 'live');
  assert.equal(checkReq.resource_bindings, 'runtime/live-resources.json');
  assert.equal(checkReq.resource_run_config, 'run-config.json');

  // Preliminary lint before check also did not send the live fields.
  for (const post of fake.posts.filter(p => p.command === 'lint')) {
    assert.equal(post.request.resource_mode, undefined);
    assert.equal(post.request.resource_bindings, undefined);
    assert.equal(post.request.resource_run_config, undefined);
  }

  // Uploaded tar contains both live files and the uploaded scenario has `live` stripped.
  const uploadedPaths = spawnSync('tar', ['-tf', '-'], { input: checkPosts[0].tar, encoding: 'utf8' }).stdout.split('\n').filter(Boolean);
  assert.ok(uploadedPaths.includes('runtime/live-resources.json'));
  assert.ok(uploadedPaths.includes('run-config.json'));
  const uploadedScenario = JSON.parse(spawnSync('tar', ['-xOf', '-', 'tests/place-order.json'], { input: checkPosts[0].tar, encoding: 'utf8' }).stdout);
  assert.equal(uploadedScenario.live, undefined);

  // Cost record on JSON output, summary.json, batch.json, and check_plan includes max_calls and max_live_calls.
  const json = JSON.parse(checkRun.ports.stdout.text);
  const row = json.rows[0];
  assert.equal(row.resource_mode, 'live');
  assert.equal(row.resource_bindings, 'runtime/live-resources.json');
  assert.equal(row.resource_run_config, 'run-config.json');
  assert.deepEqual(row.cost, { max_calls: 30, max_live_calls: 4 });
  assert.equal(row.max_live_calls, 4);
  assert.equal(json.max_live_calls, 4);
  assert.deepEqual(json.cost, { max_calls: 30, max_live_calls: 4 });
  assert.equal(json.check_plan.max_live_calls, 4);

  const summary = readJson(join(state, 'batches', json.batch, 'summary.json'));
  assert.equal(summary.rows[0].max_live_calls, 4);
  assert.deepEqual(summary.rows[0].cost, { max_calls: 30, max_live_calls: 4 });
  const batch = readJson(join(state, 'batches', json.batch, 'batch.json'));
  assert.equal(batch.rows[0].max_live_calls, 4);
  assert.deepEqual(batch.rows[0].cost, { max_calls: 30, max_live_calls: 4 });

  // Running a second time does not skip via local pass cache ("runs every time: uses live resources").
  const secondRun = portsFor(env);
  assert.equal(await runCheck({ words: ['place-order'], options: { '--json': true, '--max-calls': '30' }, cwd: repo, cache: true }, secondRun.ports), 0, secondRun.ports.stderr.text);
  assert.equal(fake.posts.filter(p => p.command === 'check').length, 2);
  const secondJson = JSON.parse(secondRun.ports.stdout.text);
  assert.equal(secondJson.rows[0].cache_reason, 'runs every time: uses live resources');
});

// A live request with an unknown service-restarted receipt keeps its original identity for every recovery read.
test('LIVE-MODE5: live service-restarted stays unknown and never creates a replacement request', async t => {
  const { repo, home, state } = harbor(t, r => addLiveFiles(r));
  let originalId = null;
  const fake = await fakeRuntime(t, (entry, runtime) => {
    if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: runtime.lint(entry.request.requestId) };
    if (entry.method === 'POST' && entry.command === 'check') {
      originalId ??= entry.request.requestId;
      return { status: 202, json: runtime.check(entry.request.requestId, 'queued') };
    }
    const id = entry.url.split('/').at(-1);
    if (id === originalId) return { status: 200, json: runtime.job(id, 'check', 'unknown', {
      exitCode: 1, refusals: [{ code: 'service-restarted' }],
    }, 2) };
    return { status: 200, json: runtime.check(id) };
  });
  const env = { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: fake.origin };
  const first = portsFor(env);
  const firstCode = await runCheck({ words: ['place-order'], options: { '--json': true }, cwd: repo }, first.ports);
  const firstJson = JSON.parse(first.ports.stdout.text);
  assert.deepEqual(fake.posts.filter(post => post.command === 'check').map(post => post.request.requestId), [originalId]);
  assert.equal(firstCode, 3);
  const batch = firstJson.batch;
  assert.equal(firstJson.rows[0].state, 'partial');
  assert.equal(firstJson.rows[0].request_id, originalId);
  assert.equal(firstJson.rows[0].resource_mode, 'live');
  assert.equal(firstJson.rows[0].calls, 2);
  assert.match(first.ports.stderr.text, /fresh pdd test/i);
  assert.deepEqual(fake.posts.filter(post => post.command === 'check').map(post => post.request.requestId), [originalId]);

  for (const run of [
    { words: [batch], options: { '--read': true } },
    { words: [], options: { '--retry': batch } },
  ]) {
    const recovery = portsFor(env);
    const code = await runCheck({ ...run, options: { '--json': true, ...run.options }, cwd: repo }, recovery.ports);
    assert.equal(code, 3);
    const json = JSON.parse(recovery.ports.stdout.text);
    assert.equal(json.rows[0].state, 'partial');
    assert.equal(json.rows[0].request_id, originalId);
    assert.equal(json.rows[0].calls, 2);
    assert.match(recovery.ports.stderr.text, /fresh pdd test/i);
    assert.deepEqual(fake.posts.filter(post => post.command === 'check').map(post => post.request.requestId), [originalId]);
  }
});

test('LIVE-MODE6: malformed live JSON does not echo source bytes in a local refusal', async t => {
  const sentinel = 'SENTINEL';
  const { repo, home, state } = harbor(t, r => {
    addLiveFiles(r);
    writeFileSync(join(r, 'runtime/live-resources.json'), `{"schema_version":"prompt-runtime.live-resource-bindings.v1","operations":[{"resource":${sentinel},"operation":"log","kind":"command"}]}`);
  });
  let networkCalls = 0;
  const { ports } = portsFor(
    { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'http://127.0.0.1:9' },
    { fetch: async () => { networkCalls += 1; throw Error('unexpected network call'); } },
  );
  const code = await runCheck({ words: ['place-order'], options: { '--json': true }, cwd: repo }, ports);
  assert.equal(code, 4);
  assert.equal(networkCalls, 0);
  const out = JSON.parse(ports.stdout.text);
  assert.equal(out.rows[0].refusals[0].code, 'live-resource-policy');
  assert.match(out.rows[0].refusals[0].message, /valid UTF-8 JSON/i);
  assert.doesNotMatch(out.rows[0].refusals[0].message, /Unexpected token|position \d+|line \d+ column \d+/i);
  assert.equal(ports.stdout.text.includes(sentinel), false);
  assert.equal(ports.stderr.text.includes(sentinel), false);
});

// The Try endpoint refuses live replay without suggesting an unavailable retry.
test('LIVE-MODE7: live-replay-unavailable advice depends on Try and does not suggest --new', async t => {
  const { repo, home, state } = harbor(t, r => addLiveFiles(r));
  const fake = await fakeRuntime(t, (entry, runtime) => {
    if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: runtime.lint(entry.request.requestId) };
    const id = entry.method === 'POST' ? entry.request.requestId : entry.url.split('/').at(-1);
    return { status: 200, json: runtime.job(id, 'try', 'refused', {
      exitCode: 4, refusals: [{ code: 'live-replay-unavailable' }],
    }, 0) };
  });
  const { ports } = portsFor({ HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: fake.origin });
  const code = await runTry({ words: ['place-order'], options: { '--no-open': true, '--no-wait': true }, cwd: repo }, ports);
  assert.equal(code, 4);
  assert.doesNotMatch(ports.stdout.text, /--new|pdd simulate/i);
  assert.match(ports.stdout.text, /live-replay-unavailable/i);
  assert.match(ports.stdout.text, /live resource.*replay|replay.*live resource/i);
  assert.match(ports.stdout.text, /test without .*live resource operations/i);
  const tryPost = fake.posts.find(post => post.command === 'try');
  assert.ok(tryPost);
  assert.equal(tryPost.request.resource_mode, undefined);
  assert.equal(tryPost.request.resource_bindings, undefined);
  assert.equal(tryPost.request.resource_run_config, undefined);
});

// Path safety, Git visibility, upload membership, symlink and size/schema policy refusals.
test('LIVE-MODE3: path safety, untracked files, symlinks, upload omission, size limits and schema errors refuse locally with live-resource-policy', async t => {
  const cases = [
    ['traversal .. in bindings', r => addLiveFiles(r, { live: { resource_bindings: '../live-resources.json', resource_run_config: 'run-config.json' } }), /repository-relative/],
    ['traversal segment in run config', r => addLiveFiles(r, { live: { resource_bindings: 'runtime/live-resources.json', resource_run_config: 'runtime/../../run-config.json' } }), /repository-relative/],
    ['absolute path', r => addLiveFiles(r, { live: { resource_bindings: '/etc/passwd', resource_run_config: 'run-config.json' } }), /repository-relative/],
    ['backslash path', r => addLiveFiles(r, { live: { resource_bindings: 'runtime\\live-resources.json', resource_run_config: 'run-config.json' } }), /forward slashes/],
    ['.git segment', r => addLiveFiles(r, { live: { resource_bindings: '.git/config', resource_run_config: 'run-config.json' } }), /repository-relative/],
    ['simulated mode inside live', r => addLiveFiles(r, { live: { resource_mode: 'simulated', resource_bindings: 'runtime/live-resources.json', resource_run_config: 'run-config.json' } }), /resource_mode/],
    ['extra key inside live', r => addLiveFiles(r, { live: { resource_bindings: 'runtime/live-resources.json', resource_run_config: 'run-config.json', extra: true } }), /unknown keys/],
    ['wrong bindings schema', r => addLiveFiles(r, { bindings: { schema_version: 'wrong.v1', operations: [] } }), /prompt-runtime\.live-resource-bindings\.v1/],
    ['invalid UTF-8 in bindings', r => {
      addLiveFiles(r);
      const path = join(r, 'runtime/live-resources.json');
      const bytes = readFileSync(path);
      const marker = Buffer.from('\"resource\": \"git\"');
      const at = bytes.indexOf(marker);
      assert.notEqual(at, -1);
      writeFileSync(path, Buffer.concat([bytes.subarray(0, at), Buffer.from('\"resource\": \"'), Buffer.from([0xff]), Buffer.from('\"'), bytes.subarray(at + marker.length)]));
    }, /valid UTF-8/],
    ['wrong run config schema', r => addLiveFiles(r, { runConfig: { schema_version: 'wrong.v1', mode: 'live', max_live_calls: 2, allow_live_writes: false } }), /prompt-runtime\.live-resource-run-config\.v1/],
    ['zero max_live_calls', r => addLiveFiles(r, { runConfig: { ...RUN_CONFIG_DOC, max_live_calls: 0 } }), /max_live_calls/],
    ['oversized bindings (> 65536 bytes)', r => {
      addLiveFiles(r);
      writeFileSync(join(r, 'runtime/live-resources.json'), JSON.stringify({
        ...BINDINGS_DOC,
        pad: 'x'.repeat(70_000),
      }));
    }, /65536/],
    ['oversized run config (> 65536 bytes)', r => {
      addLiveFiles(r);
      writeFileSync(join(r, 'run-config.json'), JSON.stringify({
        ...RUN_CONFIG_DOC,
        pad: 'y'.repeat(70_000),
      }));
    }, /65536/],
    ['symlinked bindings file', r => {
      addLiveFiles(r);
      writeJson(join(r, 'runtime/real-bindings.json'), BINDINGS_DOC);
      symlinkSync('real-bindings.json', join(r, 'runtime/symlink-bindings.json'));
      const doc = readJson(join(r, 'tests/place-order.json'));
      doc.live.resource_bindings = 'runtime/symlink-bindings.json';
      writeJson(join(r, 'tests/place-order.json'), doc);
    }, /symlink/],
    ['symlinked ancestor directory', r => {
      addLiveFiles(r);
      symlinkSync('runtime', join(r, 'linked-runtime'));
      const doc = readJson(join(r, 'tests/place-order.json'));
      doc.live.resource_bindings = 'linked-runtime/live-resources.json';
      writeJson(join(r, 'tests/place-order.json'), doc);
    }, /symlink/],
  ];

  for (const [name, edit, pattern] of cases) {
    const { repo, home, state } = harbor(t, edit);
    let networkCalls = 0;
    const { ports } = portsFor(
      { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'http://127.0.0.1:9' },
      { fetch: async () => { networkCalls += 1; throw Error('unexpected network call'); } },
    );
    const code = await runCheck({ words: ['place-order'], options: { '--json': true }, cwd: repo }, ports);
    assert.equal(code, 4, `${name}: expected exit 4, got ${code} (${ports.stderr.text})`);
    assert.equal(networkCalls, 0, `${name}: expected 0 network calls`);
    const out = JSON.parse(ports.stdout.text);
    assert.equal(out.rows[0].state, 'not run', name);
    assert.equal(out.rows[0].refusals[0].code, 'live-resource-policy', name);
    assert.match(out.rows[0].refusals[0].message, pattern, name);
  }

  // Non-Git-visible (gitignored) file is refused before network calls.
  {
    const { repo, home, state } = harbor(t, r => {
      addLiveFiles(r);
      writeFileSync(join(r, '.gitignore'), 'run-config.json\n');
    });
    let networkCalls = 0;
    const { ports } = portsFor(
      { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'http://127.0.0.1:9' },
      { fetch: async () => { networkCalls += 1; throw Error('unexpected network call'); } },
    );
    const code = await runCheck({ words: ['place-order'], options: { '--json': true }, cwd: repo }, ports);
    assert.equal(code, 4);
    assert.equal(networkCalls, 0);
    const out = JSON.parse(ports.stdout.text);
    assert.equal(out.rows[0].refusals[0].code, 'live-resource-policy');
    assert.match(out.rows[0].refusals[0].message, /Git-visible/);
  }

  // File omitted from upload closure is refused locally before POST /v1/check.
  {
    const { repo, home, state } = harbor(t, r => addLiveFiles(r));
    const fake = await fakeRuntime(t, entry => fake.normal(entry));
    const { ports } = portsFor(
      { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: fake.origin },
      {
        captureSource: (rootDir, opts) => {
          const cap = captureSource(rootDir, opts);
          cap.files = cap.files.filter(f => f.path !== 'run-config.json');
          return cap;
        },
      },
    );
    const code = await runCheck({ words: ['place-order'], options: { '--json': true }, cwd: repo }, ports);
    assert.equal(code, 4);
    assert.equal(fake.posts.filter(p => p.command === 'check').length, 0);
    const out = JSON.parse(ports.stdout.text);
    assert.equal(out.rows[0].state, 'not run');
    assert.equal(out.rows[0].refusals[0].code, 'live-resource-policy');
    assert.match(out.rows[0].refusals[0].message, /not inside the uploaded source archive/);
  }
});

// Clear messages and fix hints for server refusals: live-resource-policy, live-resource-binding-missing, live-replay-unavailable.
test('LIVE-MODE4: server refusals live-resource-policy, live-resource-binding-missing and live-replay-unavailable print clear messages and hints', async t => {
  const serverRefusals = [
    ['live-resource-policy', null, /The live resource bindings or run config failed the live resource policy/i, /prompt-runtime\.live-resource-bindings\.v1/],
    ['live-resource-binding-missing', 'git_origin', /A live check reached a resource operation that has no live binding/i, /add a live binding/i],
    ['live-replay-unavailable', null, /Check endpoint.*live resource/i, /simulated/i],
  ];

  for (const [code, detail, msgPattern, hintPattern] of serverRefusals) {
    // 1. Job-level refusal answer on POST /v1/check
    const { repo, home, state } = harbor(t, r => addLiveFiles(r));
    const fake = await fakeRuntime(t, entry => {
      if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: fake.lint(entry.request.requestId) };
      const id = entry.method === 'POST' ? entry.request.requestId : entry.url.split('/').at(-1);
      return {
        status: 200,
        json: fake.check(id, 'refused', [], [{ code, ...(detail ? { detail } : {}) }]),
      };
    });
    const { ports } = portsFor({ HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: fake.origin });
    const exitCode = await runCheck({ words: ['place-order'], options: {}, cwd: repo }, ports);
    assert.equal(exitCode, 4, `${code}: expected exit 4`);
    assert.match(ports.stdout.text, new RegExp(code), `${code}: expected code in stdout`);
    assert.match(ports.stdout.text, msgPattern, `${code}: expected clear message in stdout`);
    assert.match(ports.stdout.text, hintPattern, `${code}: expected repair hint in stdout`);
    if (code === 'live-replay-unavailable') assert.doesNotMatch(ports.stdout.text, /Try does not replay|pdd simulate|--new/i);

    // 2. HTTP 422 direct server refusal on POST /v1/check
    const fake422 = await fakeRuntime(t, entry => {
      if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: fake422.lint(entry.request.requestId) };
      return { status: 422, json: { error: { code, ...(detail ? { detail } : {}) } } };
    });
    const run422 = portsFor({ HOME: home, PDD_STATE_DIR: join(state, 'http422'), PDD_RUNTIME_URL: fake422.origin });
    const exit422 = await runCheck({ words: ['place-order'], options: {}, cwd: repo }, run422.ports);
    assert.equal(exit422, 4, `${code} 422: expected exit 4`);
    assert.match(run422.ports.stdout.text, new RegExp(code), `${code} 422: expected code in stdout`);
    assert.match(run422.ports.stdout.text, msgPattern, `${code} 422: expected clear message in stdout`);
    assert.match(run422.ports.stdout.text, hintPattern, `${code} 422: expected repair hint in stdout`);
    if (code === 'live-replay-unavailable') assert.doesNotMatch(run422.ports.stdout.text, /Try does not replay|pdd simulate|--new/i);
  }
});

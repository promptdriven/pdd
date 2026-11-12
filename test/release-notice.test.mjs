import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { releaseNotice } from '../src/release-notice.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, writeFileSync, rmSync, readFileSync, mkdirSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { harbor } from './runtime-fake.mjs';

const line = 'pdd 0.1.28: update available (0.2.0). Run: npm install -g github:promptdriven/pdd\n';
test('newer stable release gives the exact notice', async () => {
  assert.deepEqual(await releaseNotice({ version: '0.1.28', ci: false }, { latest: async () => ({ tag: 'alpha-v0.2.0' }) }), { notice: line });
  assert.match((await releaseNotice({ version: '1.99999999999999999999.0', ci: false }, { latest: async () => ({ tag: 'v1.100000000000000000000.0' }) })).notice, /update available/);
});
test('equal, old, malformed, and failed lookups are silent', async () => {
  for (const latest of ['v0.1.28', 'v0.1.27', 'v0.2.0-rc.1', 'bad']) {
    assert.equal((await releaseNotice({ version: '0.1.28', ci: false }, { latest: async () => ({ tag: latest }) })).notice, '');
  }
  assert.equal((await releaseNotice({ version: '0.1.28', ci: false }, { latest: async () => { throw Error('offline'); } })).notice, '');
});
test('CI skips the lookup', async () => {
  let calls = 0;
  assert.equal((await releaseNotice({ version: '0.1.28', ci: true }, { latest: () => { calls++; return { tag: 'v1.0.0' }; } })).notice, '');
  assert.equal(calls, 0);
});
test('the actual entry prints one notice without changing command stdout or exit', () => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-notice-'));
  try {
    const preload = join(dir, 'fetch.mjs');
    const marker = join(dir, 'effects');
    writeFileSync(preload, `import * as fs from 'node:fs'; import cp from 'node:child_process'; import { syncBuiltinESMExports } from 'node:module';\nfor (const name of ['spawn', 'spawnSync', 'exec', 'execSync', 'execFile', 'execFileSync']) { const original = cp[name]; cp[name] = function(...args) { if (String(args[0]).includes('npm')) fs.appendFileSync(${JSON.stringify(marker)}, 'install\\n'); return original.apply(this, args); }; } syncBuiltinESMExports();\nglobalThis.fetch = async () => { fs.appendFileSync(${JSON.stringify(marker)}, 'fetch\\n'); return { ok: true, json: async () => ({ tag_name: 'alpha-v999.0.0' }) }; };\n`);
    const env = { ...process.env, CI: '', NODE_OPTIONS: `--import=${preload}` };
    const version = JSON.parse(readFileSync('package.json', 'utf8')).version;
    const result = spawnSync(process.execPath, [resolve('bin/pdd.mjs'), '--version'], { encoding: 'utf8', env, timeout: 5000 });
    assert.equal(result.status, 0);
    assert.equal(result.stdout, version + '\n');
    assert.equal(result.stderr.split('\n')[0], `pdd ${version}: update available (999.0.0). Run: npm install -g github:promptdriven/pdd`);
    assert.equal(result.stderr.match(/update available/g).length, 1);
    const normalWorkflow = spawnSync(process.execPath, [resolve('bin/pdd.mjs'), 'workflow', '--help'], { encoding: 'utf8', env, timeout: 5000 });
    assert.equal(normalWorkflow.status, 0);
    const workflow = spawnSync(process.execPath, [resolve('bin/pdd.mjs'), 'workflow', '--help'], { encoding: 'utf8', env: { ...env, CI: 'true' }, timeout: 5000 });
    assert.equal(workflow.status, 0);
    assert.doesNotMatch(workflow.stderr, /update available/);
    const ciVersion = spawnSync(process.execPath, [resolve('bin/pdd.mjs'), '--version'], { encoding: 'utf8', env: { ...env, CI: 'true' }, timeout: 5000 });
    assert.equal(ciVersion.status, 0);
    assert.equal(ciVersion.stdout, version + '\n');
    assert.doesNotMatch(ciVersion.stderr, /update available/);
    const invalid = spawnSync(process.execPath, [resolve('bin/pdd.mjs'), 'check', '--fill-hash'], { encoding: 'utf8', env, timeout: 5000 });
    assert.equal(invalid.status, 2);
    assert.equal(readFileSync(marker, 'utf8'), 'fetch\n');
  } finally { rmSync(dir, { recursive: true, force: true }); }
});

test('dispatcher selects notice after parsing and ignores notice failures', async () => {
  let calls = 0;
  const stream = () => ({ text: '', write(chunk) { this.text += chunk; } });
  const run = argv => runPdd(argv, { stdout: stream(), stderr: stream(), pathDiagnostic: () => [],
    releaseNotice: async () => { calls++; throw new Error('offline'); } });
  assert.equal(await run(['--help']), 0);
  assert.equal(await run(['check', '--fill-hash']), 2);
  assert.equal(calls, 0);
  assert.equal(await run(['--version']), 0);
  assert.equal(calls, 1);
});

function testCommand(t) {
  const { sandbox, repo, home } = harbor(t);
  const tools = join(sandbox, 'tools'), preload = join(sandbox, 'fetch.mjs'), audit = join(sandbox, 'requests');
  mkdirSync(tools);
  writeFileSync(join(tools, 'gh'), '#!/bin/sh\nif [ "$1" = auth ]; then echo fixture-token; else echo "fixture-user 123"; fi\n', { mode: 0o755 });
  writeFileSync(preload, `
import { appendFileSync } from 'node:fs';
globalThis.fetch = async (url, options = {}) => {
  const release = String(url).startsWith('https://api.github.com/');
  appendFileSync(process.env.PDD_TEST_AUDIT, JSON.stringify({
    kind: release ? 'release' : 'interpreter',
    authorization: new Headers(options.headers).has('authorization')
  }) + '\\n');
  if (release) {
    if (process.env.PDD_TEST_RELEASE_OFFLINE) throw Error('offline');
    return Response.json({ tag_name: 'alpha-v999.0.0' });
  }
  return new URL(url).pathname === '/v1/capacity'
    ? Response.json({ error: { code: 'not-found' } }, { status: 404 })
    : Response.json({ error: { code: 'not-invited', message: 'Fixture access refused.' } }, { status: 403 });
};
`);
  let invocation = 0;
  return (argv, extraEnv = {}) => {
    writeFileSync(audit, '');
    const result = spawnSync(process.execPath, ['--import', preload, resolve('bin/pdd.mjs'), 'test', ...argv], {
      cwd: repo, encoding: 'utf8', timeout: 10000,
      env: { ...process.env, HOME: home, PATH: tools + ':' + process.env.PATH, CI: '',
        PDD_STATE_DIR: join(sandbox, `state-${invocation++}`), PDD_RUNTIME_URL: 'http://127.0.0.1:9',
        PDD_TEST_AUDIT: audit, PDD_TEST_RELEASE_OFFLINE: '', ...extraEnv }
    });
    assert.equal(result.error, undefined, result.stderr);
    assert.equal(result.signal, null, result.stderr);
    return { ...result, requests: readFileSync(audit, 'utf8').split('\n').filter(Boolean).map(row => JSON.parse(row)) };
  };
}

test('ordinary public test command prints one unauthenticated notice before interpreter requests', t => {
  const run = testCommand(t);
  const ci = run(['place-order'], { CI: 'true' });
  assert.equal(ci.status, 5, ci.stderr);
  assert.ok(ci.requests.length >= 2, 'fixture reaches several interpreter requests');
  assert.ok(ci.requests.every(row => row.kind === 'interpreter' && row.authorization));
  assert.doesNotMatch(ci.stderr, /update available/);

  const normal = run(['place-order']);
  const version = JSON.parse(readFileSync('package.json', 'utf8')).version;
  const notice = `pdd ${version}: update available (999.0.0). Run: npm install -g github:promptdriven/pdd\n`;
  assert.equal(normal.stderr.split(notice).length - 1, 1, normal.stderr);
  assert.deepEqual(normal.requests, [{ kind: 'release', authorization: false }, ...ci.requests]);
  assert.equal(normal.status, ci.status);
  assert.equal(normal.stdout, ci.stdout);
  assert.equal(normal.stderr.replace(notice, ''), ci.stderr);

  const offline = run(['place-order'], { PDD_TEST_RELEASE_OFFLINE: '1' });
  assert.deepEqual(offline.requests, normal.requests);
  assert.equal(offline.status, ci.status);
  assert.equal(offline.stdout, ci.stdout);
  assert.equal(offline.stderr, ci.stderr);
});

test('public test local modes and early refusals still make no release or interpreter lookup', t => {
  const run = testCommand(t);
  for (const [argv, status] of [
    [['--files', 'place-order'], 0],
    [['--explain-bindings', 'place-order'], 0],
    [['--fill-hash'], 0],
    [['--lint', '--local', 'place-order'], 0],
    [['missing-story'], 2],
    [['place-order', '--max-calls', '0'], 2],
    [['--fill-hash', '--compact', 'place-order'], 2]
  ]) {
    const result = run(argv);
    assert.equal(result.status, status, `${argv}: ${result.stderr}`);
    assert.deepEqual(result.requests, [], argv.join(' '));
    assert.doesNotMatch(result.stderr, /update available/);
  }
});

test('native lookup stays silent when offline or aborted', async () => {
  const previous = globalThis.fetch;
  try {
    globalThis.fetch = async () => { throw new Error('offline'); };
    assert.deepEqual(await releaseNotice({ version: '0.1.28', ci: false }), { notice: '' });
    let aborted = false;
    globalThis.fetch = (_url, { signal }) => new Promise((_resolve, reject) => {
      signal.addEventListener('abort', () => { aborted = true; reject(new Error('aborted')); }, { once: true });
    });
    assert.deepEqual(await releaseNotice({ version: '0.1.28', ci: false }), { notice: '' });
    assert.equal(aborted, true);
  } finally { globalThis.fetch = previous; }
});

test('Story scenario replays the release decisions', async () => {
  const scenario = JSON.parse(readFileSync('test/runtime/release-notice.json', 'utf8'));
  let calls = 0;
  for (const step of scenario.steps) {
    const before = calls;
    const result = await releaseNotice(step.input, { latest: async () => { calls++; return { tag: 'alpha-v0.2.0' }; } });
    for (const check of step.checks) {
      assert.equal(check.op, 'equals');
      if (check.target === 'result' && check.path === '/notice') assert.equal(result.notice, check.value, step.step_id);
      else if (check.target === 'calls' && check.path === '/resources/release-notice-release-latest') assert.equal(calls - before, check.value, step.step_id);
      else assert.fail(`Unmapped scenario check: ${check.target} ${check.path}`);
    }
  }
});

import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { releaseNotice } from '../src/release-notice.mjs';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, writeFileSync, rmSync, readFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';

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
    assert.equal(readFileSync(marker, 'utf8'), 'fetch\nfetch\n');
  } finally { rmSync(dir, { recursive: true, force: true }); }
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

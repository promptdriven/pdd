import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';

const root = resolve(import.meta.dirname, '..');
// Synthetic values only: none identifies the job's real session.
const sessions = {
  HERDR_ENV: '1', HERDR_SESSION: 'fixture-session', HERDR_SOCKET_PATH: '/fixture/sessions/chat/socket',
  HERDR_PANE_ID: 'fixture-pane', HERDR_TAB_ID: 'fixture-tab', HERDR_WORKSPACE_ID: 'fixture-workspace',
  HERDR_FUTURE_SELECTOR: 'fixture-future', PDD_AGENT_SESSION: '1', PDD_AUTOPILOT_CONTEXT: '{"fixture":true}',
  CLAUDECODE: '1', CLAUDE_CODE_SESSION_ID: 'fixture-claude', CLAUDE_PID: '999999',
  CODEX_THREAD_ID: 'fixture-codex', CODEX_SANDBOX: 'fixture', CODEX_SANDBOX_NETWORK_DISABLED: '1',
};

async function runWithoutInput(command, args, options) {
  const group = process.platform !== 'win32';
  const child = spawn(command, args, { ...options, detached: group, stdio: ['pipe', 'pipe', 'pipe'] });
  const stop = () => {
    if (!child.pid) return;
    try {
      if (group) process.kill(-child.pid, 'SIGKILL');
      else child.kill('SIGKILL');
    } catch (error) { if (error.code !== 'ESRCH') throw error; }
  };
  let stdout = '', stderr = '';
  child.stdout.on('data', data => { stdout += data; });
  child.stderr.on('data', data => { stderr += data; });
  let timedOut = false;
  const timer = setTimeout(() => { timedOut = true; stop(); }, 30000);
  try {
    // Deliberately do not end or write to stdin. Exit must not depend on EOF or a reply.
    const result = await new Promise((resolve, reject) => {
      child.once('error', reject);
      child.once('close', (code, signal) => resolve({ code, signal }));
    });
    assert.equal(timedOut, false, 'test waited with caller input open');
    assert.equal(result.signal, null, stderr + stdout);
    assert.equal(result.code, 0, stderr + stdout);
    return stdout;
  } finally {
    clearTimeout(timer);
    child.stdin.destroy();
    if (child.exitCode === null && child.signalCode === null) stop();
  }
}

for (const entry of ['focused import', 'npm preload']) test(`${entry} isolates caller sessions with stdin open`, async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-session-guard-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  mkdirSync(join(dir, 'test/helpers'), { recursive: true });
  writeFileSync(join(dir, 'test/helpers/test-home.mjs'), readFileSync(join(root, 'test/helpers/test-home.mjs')));
  const manifest = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  writeFileSync(join(dir, 'package.json'), JSON.stringify({ private: true, type: 'module', scripts: { test: manifest.scripts.test } }));
  const env = { ...process.env, ...sessions, PDD_CHECK_CPUS: '3', PDD_SESSION_FIXTURE_VALUE: 'keep',
    npm_config_cache: join(dir, 'npm-cache'), npm_config_userconfig: join(dir, 'no-npmrc'), npm_config_update_notifier: 'false' };
  delete env.NODE_TEST_CONTEXT;
  const before = { ...env }, callerEnv = { ...process.env };
  const file = join(dir, 'test/session.test.mjs');
  writeFileSync(file, `
    ${entry === 'focused import' ? "import './helpers/test-home.mjs';" : ''}
    import test from 'node:test';
    import assert from 'node:assert/strict';
    import { execFileSync } from 'node:child_process';
    const names = ${JSON.stringify(Object.keys(sessions))};
    // Check at module evaluation, before a test body or production call can use a session.
    for (const name of names) assert.equal(process.env[name], undefined, 'inherited session: ' + name);
    const inherited = JSON.parse(execFileSync(process.execPath, ['-e', 'console.log(JSON.stringify(process.env))'], { encoding: 'utf8', timeout: 5000 }));
    for (const name of names) assert.equal(inherited[name], undefined, 'child inherited session: ' + name);
    assert.equal(inherited.PDD_CHECK_CPUS, '3');
    assert.equal(inherited.PDD_SESSION_FIXTURE_VALUE, 'keep');
    test('explicit fixture session remains available', () => {
      process.env.HERDR_SESSION = 'test-owned-session';
      process.env.PDD_AGENT_SESSION = 'fixture-agent';
      const fixture = JSON.parse(execFileSync(process.execPath, ['-e', 'console.log(JSON.stringify(process.env))'], { encoding: 'utf8', timeout: 5000 }));
      assert.equal(fixture.HERDR_SESSION, 'test-owned-session');
      assert.equal(fixture.PDD_AGENT_SESSION, 'fixture-agent');
    });
  `);
  const output = entry === 'focused import'
    ? await runWithoutInput(process.execPath, ['--test', file], { cwd: dir, env })
    : await runWithoutInput('npm', ['test', '--ignore-scripts=false'], { cwd: dir, env });
  assert.match(output, /# pass 1\b/);
  assert.match(output, /# fail 0\b/);
  assert.deepEqual(env, before);
  assert.deepEqual({ ...process.env }, callerEnv);
});

test('product formal test finishes under a synthetic workflow-chat caller with stdin open', async () => {
  const env = { ...process.env, ...sessions };
  delete env.NODE_TEST_CONTEXT;
  const output = await runWithoutInput(process.execPath, ['--test', 'test/product.formal.test.mjs'], { cwd: root, env });
  assert.match(output, /# pass 2\b/);
  assert.match(output, /# fail 0\b/);
  assert.match(output, /2048 status cases/);
});

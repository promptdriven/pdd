import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, readdirSync, lstatSync, existsSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { spawnSync } from 'node:child_process';

const root = resolve(import.meta.dirname, '..');
const bootstrap = pathToFileURL(join(root, 'test/helpers/test-home.mjs')).href;
const redirects = ['PDD_STATE_DIR', 'XDG_CONFIG_HOME', 'XDG_STATE_HOME', 'XDG_CACHE_HOME', 'XDG_DATA_HOME', 'XDG_RUNTIME_DIR', 'CODEX_HOME', 'CLAUDE_CONFIG_DIR', 'GEMINI_CLI_HOME', 'AGY_HOME', 'GH_CONFIG_DIR'];
function caller(t) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-home-guard-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const home = join(dir, 'caller'); mkdirSync(home);
  const env = { ...process.env, HOME: home, USERPROFILE: home };
  delete env.NODE_TEST_CONTEXT;
  for (const key of redirects) { env[key] = join(home, key); mkdirSync(env[key]); writeFileSync(join(env[key], 'keep'), key); }
  for (const path of ['.local/state/pdd', '.config/herdr', '.agents/skills', '.claude/skills', '.codex/skills', '.pdd/runtime']) {
    mkdirSync(join(home, path), { recursive: true }); writeFileSync(join(home, path, 'keep'), path);
  }
  env.PDD_INTERPRETER_QUEUE = join(home, 'interpreter-queue');
  mkdirSync(env.PDD_INTERPRETER_QUEUE); writeFileSync(join(env.PDD_INTERPRETER_QUEUE, 'keep'), 'caller-queue');
  writeFileSync(join(home, '.local/state/pdd/runs.json'), JSON.stringify({ version: 1, runs: [] }));
  return { dir, home, env };
}
function snapshot(directory) {
  return readdirSync(directory, { recursive: true }).sort().map(name => {
    const path = join(directory, name);
    return [name, lstatSync(path).isDirectory() ? null : readFileSync(path).toString('base64')];
  });
}
function child(args, env, cwd = root) {
  return spawnSync(process.execPath, args, { cwd, env, encoding: 'utf8', timeout: 120000, maxBuffer: 8 * 1024 * 1024 });
}

test('default state, skills, homedir fallback and children use a disposable home', t => {
  const f = caller(t), before = snapshot(f.home);
  const script = `
    import ${JSON.stringify(bootstrap)};
    import assert from 'node:assert/strict';
    import { homedir } from 'node:os';
    import { join } from 'node:path';
    import { mkdirSync, writeFileSync, existsSync } from 'node:fs';
    import { execFileSync } from 'node:child_process';
    import { stateDirFor, writeRun } from ${JSON.stringify(pathToFileURL(join(root, 'src/workflow-runs.mjs')).href)};
    import { setupSkills } from ${JSON.stringify(pathToFileURL(join(root, 'src/skills-install.mjs')).href)};
    assert.notEqual(process.env.HOME, ${JSON.stringify(f.home)});
    assert.equal(homedir(), process.env.HOME);
    assert.equal(process.env.PDD_INTERPRETER_QUEUE, join(homedir(), 'interpreter-queue'));
    execFileSync(process.execPath, ['--input-type=module', '-e', ${JSON.stringify(`import {acquireInterpreterSlot} from ${JSON.stringify(pathToFileURL(join(root, 'src/interpreter-queue.mjs')).href)}; await acquireInterpreterSlot({cwd:process.cwd(),origin:'http://127.0.0.1:1',requestId:'child',kind:'lint'});`)}]);
    assert.equal(existsSync(join(process.env.PDD_INTERPRETER_QUEUE, 'ticket-1.json')), true);
    for (const key of ${JSON.stringify(redirects)}) assert.equal(process.env[key], undefined, key);
    const state = join(homedir(), '.local/state/pdd');
    assert.equal(stateDirFor({ env: {} }), state);
    const runDir = join(homedir(), 'repo/.git/pdd/runs/1');
    writeRun({ v: 1, number: 1, repo: 'example/fixture', runDir, root: join(homedir(), 'repo'), state: 'running', areas: [], done: {}, chats: [] }, { skipMetricsDelivery: true });
    assert.equal(existsSync(join(state, 'runs.json')), true);
    setupSkills({ packageRoot: ${JSON.stringify(root)}, cwd: join(homedir(), 'repo'), home: homedir() });
    assert.equal(existsSync(join(homedir(), '.agents/skills/pdd-bug/SKILL.md')), true);
    mkdirSync(join(homedir(), '.config/herdr'), { recursive: true });
    execFileSync(process.execPath, ['-e', "require('node:fs').writeFileSync(require('node:path').join(require('node:os').homedir(), '.config/herdr/child'), 'fixture')"]);
    assert.equal(existsSync(join(homedir(), '.config/herdr/child')), true);
    console.log(JSON.stringify({ home: homedir() }));
  `;
  const result = child(['--input-type=module', '-e', script], f.env);
  assert.equal(result.status, 0, result.stderr);
  const { home } = JSON.parse(result.stdout);
  assert.equal(existsSync(home), false);
  assert.deepEqual(snapshot(f.home), before, 'caller-home-leak');
});

test('shared workspace fixture keeps a default run-index write out of caller HOME', t => {
  const f = caller(t), before = snapshot(f.home);
  const target = process.env.PDD_TEST_HOME_ROOT ?? root;
  const script = `
    import { fixture } from ${JSON.stringify(pathToFileURL(join(target, 'test/helpers/runtime-workspace-fixture.mjs')).href)};
    import { writeRun } from ${JSON.stringify(pathToFileURL(join(target, 'src/workflow-runs.mjs')).href)};
    import { join } from 'node:path';
    const cleanup = [], f = fixture({ after(fn) { cleanup.push(fn); } });
    try {
      writeRun({ v: 1, number: 1, repo: 'example/fixture', runDir: join(f.root, '.git/pdd/runs/1'), root: f.root, state: 'running', areas: [], done: {}, chats: [] }, { env: f.env, skipMetricsDelivery: true });
    } finally { for (const fn of cleanup.reverse()) fn(); }
  `;
  const result = child(['--input-type=module', '-e', script], f.env, target);
  assert.equal(result.status, 0, result.stderr);
  assert.deepEqual(snapshot(f.home), before, 'caller-home-leak');
});

test('shared workspace fixture leaves room for a consumer-owned home', t => {
  const f = caller(t), before = snapshot(f.home);
  const target = process.env.PDD_TEST_HOME_ROOT ?? root;
  const script = `
    import { fixture } from ${JSON.stringify(pathToFileURL(join(target, 'test/helpers/runtime-workspace-fixture.mjs')).href)};
    import { writeRun } from ${JSON.stringify(pathToFileURL(join(target, 'src/workflow-runs.mjs')).href)};
    import assert from 'node:assert/strict';
    import { mkdirSync, readFileSync } from 'node:fs';
    import { join } from 'node:path';
    const cleanup = [], f = fixture({ after(fn) { cleanup.push(fn); } });
    try {
      const consumerHome = join(f.parent, 'home');
      assert.doesNotThrow(() => mkdirSync(consumerHome), 'consumer-home-collision');
      for (const [number, env] of [[1, f.env], [2, { ...f.env, HOME: consumerHome }]]) {
        writeRun({ v: 1, number, repo: 'example/fixture', runDir: join(f.root, '.git/pdd/runs', String(number)), root: f.root, state: 'running', areas: [], done: {}, chats: [] }, { env, skipMetricsDelivery: true });
      }
      for (const [number, home] of [[1, f.env.HOME], [2, consumerHome]]) {
        const index = JSON.parse(readFileSync(join(home, '.local/state/pdd/runs.json'), 'utf8'));
        assert.deepEqual(index.runs.map(run => run.number), [number]);
      }
    } finally { for (const fn of cleanup.reverse()) fn(); }
  `;
  const result = child(['--input-type=module', '-e', script], f.env, target);
  assert.equal(result.status, 0, result.stderr);
  assert.deepEqual(snapshot(f.home), before, 'caller-home-leak');
});

test('home cleanup also runs after a failed native test', t => {
  const f = caller(t), before = snapshot(f.home), file = join(f.dir, 'failing.test.mjs'), record = join(f.dir, 'owned-home');
  writeFileSync(file, `import ${JSON.stringify(bootstrap)};\nimport test from 'node:test';\nimport { writeFileSync } from 'node:fs';\nwriteFileSync(${JSON.stringify(record)}, process.env.HOME);\ntest('intentional failure', () => { throw Error('intentional failure'); });\n`);
  const result = child(['--test', file], f.env);
  assert.equal(result.status, 1);
  assert.match(result.stdout, /# fail 1\b/);
  const home = readFileSync(record, 'utf8');
  assert.notEqual(home, f.home);
  assert.equal(existsSync(home), false);
  assert.deepEqual(snapshot(f.home), before, 'caller-home-leak');
});

// Exercise the same native fixture entrypoints on the old checkout for the
// control. Expected caller bytes come from the isolation contract, not pdd output.
for (const [file, pattern] of [
  ['metrics-selector.integration.test.mjs', '^selector captures'],
  ['metrics-composition.integration.test.mjs', '^composed launcher'],
  ['autopilot-runtime-outage.test.mjs', '^real path:|^real pdd test:'],
  ['workspace-evidence-counting.test.mjs', '^2899/2956: owned'],
  ['workflow-step-results-2922.test.mjs', '^2922 AC'],
  ['autopilot-repair-ceiling.test.mjs', '^repair ceiling:'],
]) test(`focused ${file} leaves caller state and config unchanged`, t => {
  const f = caller(t), before = snapshot(f.home);
  // No preload: this proves focused files load their own isolation. Leave the
  // runtime override absent to exercise the normal HOME fallback as well.
  delete f.env.PDD_STATE_DIR;
  const target = process.env.PDD_TEST_HOME_ROOT ?? root;
  const result = child(['--test', '--test-concurrency=8', `--test-name-pattern=${pattern}`, join(target, 'test', file)], f.env, target);
  assert.equal(result.status, 0, result.stderr + result.stdout);
  assert.deepEqual(snapshot(f.home), before, 'caller-home-leak');
});


test('npm test isolates a new file that omits the helper import', t => {
  const f = caller(t), before = snapshot(f.home), project = join(f.dir, 'project');
  mkdirSync(join(project, 'test/helpers'), { recursive: true });
  writeFileSync(join(project, 'test/helpers/test-home.mjs'), readFileSync(join(root, 'test/helpers/test-home.mjs')));
  const manifest = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  writeFileSync(join(project, 'package.json'), JSON.stringify({ private: true, type: 'module', scripts: { test: manifest.scripts.test } }));
  const record = join(f.dir, 'npm-test-home');
  writeFileSync(join(project, 'test/new.test.mjs'), `
    import test from 'node:test';
    import assert from 'node:assert/strict';
    import { writeFileSync, existsSync } from 'node:fs';
    import { join } from 'node:path';
    import { writeRun } from ${JSON.stringify(pathToFileURL(join(root, 'src/workflow-runs.mjs')).href)};
    writeFileSync(${JSON.stringify(record)}, process.env.HOME);
    test('default write', () => {
      assert.equal(process.env.PDD_INTERPRETER_QUEUE, join(process.env.HOME, 'interpreter-queue'));
      writeRun({ v: 1, number: 1, repo: 'example/new', runDir: join(process.env.HOME, 'repo/.git/pdd/runs/1'), root: process.env.HOME, state: 'running', areas: [], done: {}, chats: [] }, { skipMetricsDelivery: true });
      assert.equal(existsSync(join(process.env.HOME, '.local/state/pdd/runs.json')), true);
    });
  `);
  const result = spawnSync('npm', ['test', '--ignore-scripts=false'], {
    cwd: project, env: { ...f.env, npm_config_cache: join(f.dir, 'npm-cache'), npm_config_userconfig: join(f.dir, 'no-npmrc'), npm_config_update_notifier: 'false' },
    encoding: 'utf8', timeout: 30000,
  });
  assert.equal(result.status, 0, result.stderr + result.stdout);
  const home = readFileSync(record, 'utf8');
  assert.notEqual(home, f.home);
  assert.equal(existsSync(home), false);
  assert.deepEqual(snapshot(f.home), before, 'caller-home-leak');
});


for (const caught of [false, true]) test(`OS account-home lookup is blocked even when caught=${caught}`, t => {
  const f = caller(t), before = snapshot(f.home), record = join(f.dir, 'account-lookup-home');
  const script = `
    import ${JSON.stringify(bootstrap)};
    import { userInfo } from 'node:os';
    import { writeFileSync } from 'node:fs';
    import { alertStatusLine } from ${JSON.stringify(pathToFileURL(join(root, 'src/autopilot-alerts.mjs')).href)};
    writeFileSync(${JSON.stringify(record)}, process.env.HOME);
    ${caught ? "alertStatusLine({ repo: 'example/fixture', env: {} });" : 'userInfo();'}
  `;
  const result = child(['--input-type=module', '-e', script], f.env);
  assert.equal(result.status, 1);
  assert.match(result.stderr, /PDD_TEST_ACCOUNT_HOME/);
  const home = readFileSync(record, 'utf8');
  assert.notEqual(home, f.home);
  assert.equal(existsSync(home), false);
  assert.deepEqual(snapshot(f.home), before, 'caller-home-leak');
});

for (const [port, method] of [['sync', 'mkdirSync'], ['sync', 'readFileSync'],
  ['sync', 'renameSync'], ['callback', 'writeFile'], ['promise', 'readFile'], ['promise', 'rename'],
  ['sync', 'truncateSync'], ['sync', 'opendirSync'], ['sync', 'realpathSync'],
  ['promise', 'truncate'], ['promise', 'opendir'], ['promise', 'realpath']]) {
  test(`machine interpreter queue guard rejects caught ${port} ${method} before I/O`, t => {
    const f = caller(t), before = snapshot(f.home);
    // Stub the underlying operation before loading the guard. Even the old-code
    // control cannot read or write the machine queue.
    const script = `
      import fs from 'node:fs';
      import promises from 'node:fs/promises';
      import {syncBuiltinESMExports} from 'node:module';
      const port=${JSON.stringify(port)} === 'promise' ? promises : fs;
      let io=0;
      const original=port[${JSON.stringify(method)}];
      const machine='/tmp/pdd-interpreter-'+(process.getuid?.() ?? 'user');
      port[${JSON.stringify(method)}]=(...args)=>{
        if(args.some(value=>typeof value==='string'&&(value===machine||value.startsWith(machine+'/')))) {
          io++;throw Object.assign(Error('synthetic I/O'),{code:'SYNTHETIC_IO'});
        }
        return original(...args);
      };
      syncBuiltinESMExports();
      await import(${JSON.stringify(bootstrap)});
      const path='/tmp/pdd-interpreter-'+(process.getuid?.() ?? 'user')+'/ticket-1.json';
      let code;
      try {
        await port[${JSON.stringify(method)}](...(${JSON.stringify(method)}.startsWith('rename') ? ['/synthetic-source',path] : [path,()=>{}]));
      } catch(error) { code=error.code; }
      console.log(JSON.stringify({code,io}));
    `;
    const result = child(['--input-type=module', '-e', script], f.env);
    assert.equal(result.status, 1, 'machine-queue-guard');
    assert.match(result.stderr, /PDD_TEST_INTERPRETER_QUEUE/);
    assert.deepEqual(JSON.parse(result.stdout), {code:'PDD_TEST_INTERPRETER_QUEUE',io:0});
    assert.deepEqual(snapshot(f.home), before, 'caller-queue-leak');
  });
}

test('focused public checks leave an inherited caller interpreter queue unchanged', t => {
  const f = caller(t), before = snapshot(f.home);
  const result = child(['--test', '--test-name-pattern=^a public check gets a slot',
    join(root, 'test/interpreter-queue-runtime.test.mjs')], f.env);
  assert.equal(result.status, 0, result.stderr + result.stdout);
  assert.match(result.stdout, /# pass 1\b/);
  assert.deepEqual(snapshot(f.home), before, 'caller-queue-leak');
});

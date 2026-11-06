import test from 'node:test';
import assert from 'node:assert/strict';
import { EventEmitter } from 'node:events';
import { createServer } from 'node:net';
import { PassThrough } from 'node:stream';
import {
  copyFileSync, existsSync, mkdirSync, mkdtempSync,
  readFileSync, rmSync, writeFileSync,
} from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { spawn, spawnSync } from 'node:child_process';

const repo = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const runnerPath = join(repo, 'src/test-suite-runner.mjs');
const hasRunner = existsSync(runnerPath);

function makeFixture(script) {
  const root = mkdtempSync(join('/tmp', 'pdd-test-suite-'));
  mkdirSync(join(root, 'test'), { recursive: true });
  writeFileSync(join(root, 'package.json'), JSON.stringify({
    name: 'pdd-test-suite-fixture',
    version: '1.0.0',
    type: 'module',
    scripts: { test: script },
  }));
  return root;
}

function writeRunTest(root, name, body = '') {
  const source = [
    "import { appendFileSync } from 'node:fs';",
    "import test from 'node:test';",
    `test(${JSON.stringify(name)}, async () => { ${body}`,
    `  appendFileSync(process.env.PDD_TEST_SUITE_RUNS, ${JSON.stringify(`${name}\n`)});`,
    '});',
  ].join('\n');
  const path = join(root, `test/${name}.test.mjs`);
  writeFileSync(path, source);
  return path;
}

function runNpm(root, testFiles, environment) {
  const args = ['test'];
  if (testFiles.length) args.push('--', ...testFiles);
  return new Promise((resolveResult, reject) => {
    const child = spawn('npm', args, {
      cwd: root,
      env: environment,
      detached: process.platform !== 'win32',
      stdio: ['pipe', 'pipe', 'pipe'],
    });
    let stdout = '';
    let stderr = '';
    const timeout = setTimeout(() => {
      if (process.platform === 'win32') child.kill('SIGKILL');
      else {
        try { process.kill(-child.pid, 'SIGKILL'); }
        catch { child.kill('SIGKILL'); }
      }
    }, 15000);
    child.stdout.setEncoding('utf8').on('data', chunk => { stdout += chunk; });
    child.stderr.setEncoding('utf8').on('data', chunk => { stderr += chunk; });
    child.once('error', error => {
      clearTimeout(timeout);
      reject(error);
    });
    child.once('close', (code, signal) => {
      clearTimeout(timeout);
      resolveResult({ code, signal, stdout, stderr });
    });
  });
}

function recordedRuns(path) {
  if (!existsSync(path)) return [];
  return readFileSync(path, 'utf8').trim().split('\n').filter(Boolean);
}

function fakeChild() {
  const child = new EventEmitter();
  child.stdout = new PassThrough();
  child.stderr = new PassThrough();
  return child;
}

function cleanTestEnvironment() {
  return Object.fromEntries(Object.entries(process.env).filter(([name]) =>
    name !== 'NODE_TEST_CONTEXT' && !name.startsWith('HERDR_') && name !== 'PDD_AGENT_SESSION'));
}

if (!hasRunner) {
  test('focused npm test must select only the requested test file', async () => {
    const root = makeFixture('node --test test/*.test.mjs');
    const runs = join(root, 'runs.jsonl');
    writeRunTest(root, 'default');
    writeRunTest(root, 'focused');
    try {
      const result = await runNpm(root, ['test/focused.test.mjs'], {
        ...cleanTestEnvironment(),
        PDD_TEST_SUITE_RUNS: runs,
      });
      assert.equal(result.code, 0, `${result.stdout}\n${result.stderr}`);
      assert.deepEqual(recordedRuns(runs), ['focused'], 'focused npm test must select only the requested test file');
    } finally {
      rmSync(root, { recursive: true, force: true });
    }
  });
} else {
  const { runTestSuite } = await import(pathToFileURL(runnerPath).href);

  test('runTestSuite selects the default or focused files, filters only session markers, and preserves exit codes', async () => {
    const environment = [
      { name: 'PATH', value: process.env.PATH ?? '/bin' },
      { name: 'HOME', value: process.env.HOME ?? '/tmp' },
      { name: 'HERDR_ENV', value: 'synthetic' },
      { name: 'HERDR_SOCKET_PATH', value: '/tmp/not-a-live-socket' },
      { name: 'PDD_AGENT_SESSION', value: 'synthetic' },
      { name: 'PDD_AGENT_SESSION_EXTRA', value: 'keep' },
      { name: 'PDD_TEST_SUITE_SENTINEL', value: 'keep' },
    ];
    const preserved = environment.filter(({ name }) => !name.startsWith('HERDR_') && name !== 'PDD_AGENT_SESSION');
    for (const { testFiles, code } of [
      { testFiles: [], code: 0 },
      { testFiles: ['test/one.test.mjs'], code: 1 },
      { testFiles: ['test/one.test.mjs', 'test/two.test.mjs'], code: 7 },
    ]) {
      const child = fakeChild();
      const calls = [];
      const result = runTestSuite({ cwd: '/fixture/repo', testFiles, environment }, {
        nodeTest: { run: options => { calls.push(options); setImmediate(() => child.emit('close', code)); return child; } },
      });
      assert.deepEqual(await result, { exit_code: code });
      assert.deepEqual(calls, [{
        cwd: '/fixture/repo',
        args: ['--test', ...(testFiles.length ? testFiles : ['test/*.test.mjs'])],
        environment: preserved,
        stdio: ['ignore', 'pipe', 'pipe'],
      }]);
    }
  });

  test('runTestSuite forwards each stream chunk before close and keeps each run separate', async () => {
    const source = `
      import assert from 'node:assert/strict';
      import { EventEmitter } from 'node:events';
      import { PassThrough } from 'node:stream';
      const { runTestSuite } = await import(${JSON.stringify(pathToFileURL(runnerPath).href)});
      const observed = [];
      async function captureRun(write, expectedOutput, exitCode) {
        const output = { stdout: [], stderr: [] };
        const originalStdout = process.stdout.write;
        const originalStderr = process.stderr.write;
        process.stdout.write = chunk => { output.stdout.push(Buffer.from(chunk).toString()); return true; };
        process.stderr.write = chunk => { output.stderr.push(Buffer.from(chunk).toString()); return true; };
        try {
          const child = new EventEmitter();
          child.stdout = new PassThrough();
          child.stderr = new PassThrough();
          let closed = false;
          child.once('close', () => { closed = true; });
          const completed = runTestSuite({ cwd: '/fixture/repo', testFiles: ['test/one.test.mjs'], environment: [] }, {
            nodeTest: { run: () => child },
          });
          write(child);
          await new Promise(resolveNext => setImmediate(resolveNext));
          assert.equal(closed, false);
          assert.deepEqual(output, expectedOutput);
          child.emit('close', exitCode);
          assert.deepEqual(await completed, { exit_code: exitCode });
          observed.push(true);
        } finally {
          process.stdout.write = originalStdout;
          process.stderr.write = originalStderr;
        }
      }
      await captureRun(child => {
        child.stdout.write(Buffer.from('first stdout\\n'));
        child.stdout.write(Buffer.from('second stdout\\n'));
        child.stderr.write(Buffer.from('stderr chunk\\n'));
      }, { stdout: ['first stdout\\n', 'second stdout\\n'], stderr: ['stderr chunk\\n'] }, 7);
      assert.deepEqual(observed, [true]);
      const timingCases = [
        { stream: 'stdout', text: '# duration_ms 11.125\\n' },
        { stream: 'stderr', text: '# duration_ms 29.875\\n' },
      ];
      for (const timing of timingCases) {
        await captureRun(
          child => child[timing.stream].write(Buffer.from(timing.text)),
          { stdout: timing.stream === 'stdout' ? [timing.text] : [], stderr: timing.stream === 'stderr' ? [timing.text] : [] },
          0,
        );
      }
      process.stdout.write(JSON.stringify({ streamCases: observed.length }));
    `;
    const result = spawnSync(process.execPath, ['--input-type=module', '-e', source], {
      encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], timeout: 5000,
    });
    assert.equal(result.status, 0, `${result.stdout}\n${result.stderr}`);
    assert.deepEqual(JSON.parse(result.stdout), { streamCases: 3 });
  });

  test('the npm entry runs only the top-level defaults or the requested fixture and isolates the child', async t => {
    const packageJson = JSON.parse(readFileSync(join(repo, 'package.json'), 'utf8'));
    assert.equal(packageJson.scripts.test, 'node src/test-suite-runner.mjs');

    const root = makeFixture('node src/test-suite-runner.mjs');
    const runs = join(root, 'runs.jsonl');
    const probe = join(root, 'probe.json');
    const socketPath = join(root, 'herdr.sock');
    mkdirSync(join(root, 'src'), { recursive: true });
    mkdirSync(join(root, 'test/nested'), { recursive: true });
    copyFileSync(runnerPath, join(root, 'src/test-suite-runner.mjs'));
    writeRunTest(root, 'default');
    writeRunTest(root, 'selected', `
      const { writeFileSync } = await import('node:fs');
      const { connect } = await import('node:net');
      if (process.env.HERDR_SOCKET_PATH) {
        const socket = connect(process.env.HERDR_SOCKET_PATH);
        await new Promise((resolveConnect, rejectConnect) => {
          socket.once('connect', resolveConnect);
          socket.once('error', rejectConnect);
        });
        socket.end();
      }
      const environment = Object.fromEntries(Object.entries(process.env));
      writeFileSync(process.env.PDD_TEST_SUITE_PROBE, JSON.stringify({ environment }));
    `);
    writeFileSync(join(root, 'test/nested/ignored.test.mjs'), [
      "import { appendFileSync } from 'node:fs';",
      "import test from 'node:test';",
      `test('nested', () => appendFileSync(process.env.PDD_TEST_SUITE_RUNS, ${JSON.stringify('nested\n')}));`,
    ].join('\n'));

    let connections = 0;
    const server = createServer(() => { connections += 1; });
    await new Promise((resolveListen, rejectListen) => {
      server.once('error', rejectListen);
      server.listen(socketPath, resolveListen);
    });
    t.after(async () => {
      await new Promise(resolveClose => server.close(resolveClose));
      rmSync(root, { recursive: true, force: true });
    });

    const environment = {
      ...cleanTestEnvironment(),
      HERDR_ENV: 'synthetic',
      HERDR_SESSION: 'synthetic',
      HERDR_SOCKET_PATH: socketPath,
      HERDR_PANE_ID: 'synthetic',
      PDD_AGENT_SESSION: 'synthetic',
      PDD_TEST_SUITE_RUNS: runs,
      PDD_TEST_SUITE_PROBE: probe,
      PDD_TEST_SUITE_SENTINEL: 'preserved',
    };

    const defaultResult = await runNpm(root, [], environment);
    assert.equal(defaultResult.code, 0, `${defaultResult.stdout}\n${defaultResult.stderr}`);
    assert.deepEqual(recordedRuns(runs).sort(), ['default', 'selected']);
    const observation = JSON.parse(readFileSync(probe, 'utf8'));
    assert.equal(Object.keys(observation.environment).some(name => name.startsWith('HERDR_')), false);
    assert.equal(Object.hasOwn(observation.environment, 'PDD_AGENT_SESSION'), false);
    assert.equal(observation.environment.PDD_TEST_SUITE_SENTINEL, 'preserved');
    assert.equal(typeof observation.environment.PATH, 'string');
    assert.equal(observation.environment.HOME, environment.HOME);

    writeFileSync(runs, '');
    writeFileSync(probe, '');
    const focusedResult = await runNpm(root, ['test/selected.test.mjs'], environment);
    assert.equal(focusedResult.code, 0, `${focusedResult.stdout}\n${focusedResult.stderr}`);
    assert.deepEqual(recordedRuns(runs), ['selected']);
    assert.equal(connections, 0);
  });
}

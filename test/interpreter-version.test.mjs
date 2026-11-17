import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, writeFileSync, readFileSync, readdirSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { createServer } from 'node:http';
import { runDetailedVersion } from '../src/interpreter-version.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

const exec = promisify(execFile);
const cli = resolve('bin/pdd.mjs');
const version = JSON.parse(readFileSync(new URL('../package.json', import.meta.url))).version;
const sha = '0123456789abcdef0123456789abcdef01234567';
const token = 'fictional-diagnostic-token';
const unknown = `PDD CLI: ${version}\nPDD interpreter: unknown\n`;
const metadata = { engine_sha: sha.toUpperCase(), formats: { interface: ['prompt-runtime.interface.v4', 'prompt-runtime.interface.v2'],
  test: ['prompt-runtime.program-scenario.v1'], app_map: [] }, message: 'PRIVATE-REMOTE\u001b[31m', model: 'PRIVATE-MODEL' };
const known = `PDD CLI: ${version}\nPDD interpreter: ${sha}\nInterface formats: prompt-runtime.interface.v4, prompt-runtime.interface.v2\nTest formats: prompt-runtime.program-scenario.v1\nApp-map formats: none\n`;
const capture = () => ({ text: '', write(value) { this.text += value; } });

function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-detailed-version-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const log = join(root, 'gh-calls.jsonl');
  // This executable is isolated from the person's gh configuration and credentials.
  writeFileSync(join(root, 'gh'), `#!${process.execPath}\nimport fs from 'node:fs';
const args = process.argv.slice(2), stdin = fs.readFileSync(0, 'utf8');
fs.appendFileSync(process.env.DIAGNOSTIC_LOG, JSON.stringify({ args, stdin, sentinel: process.env.DIAGNOSTIC_SENTINEL }) + '\\n');
if (args.join(' ') !== 'auth token') process.exit(91);
if (process.env.DIAGNOSTIC_MODE === 'hang') setInterval(() => {}, 1000);
else { process.stderr.write('PRIVATE-GH-ERROR'); process.stdout.write('${token}\\n'); process.exitCode = process.env.DIAGNOSTIC_MODE === 'fail' ? 1 : 0; }
`, { mode: 0o755 });
  const env = { ...process.env, HOME: root, GH_CONFIG_DIR: root, PATH: root,
    DIAGNOSTIC_LOG: log, DIAGNOSTIC_SENTINEL: 'full-native-environment' };
  // Only the fixture program is on PATH. No process can fall back to an account tool.
  return { root, env, calls: () => { try { return readFileSync(log, 'utf8').trim().split('\n').filter(Boolean).map(JSON.parse); } catch { return []; } },
    async run(args = ['-VV'], extraEnv = {}) {
      try { return { code: 0, ...await exec(process.execPath, [cli, ...args], { cwd: root, env: { ...env, ...extraEnv }, timeout: 16000, encoding: 'utf8' }) }; }
      catch (error) { if (Number.isInteger(error.code)) return { code: error.code, stdout: error.stdout, stderr: error.stderr }; throw error; }
    } };
}

async function server(t, handler) {
  const calls = [];
  const instance = createServer((request, response) => {
    const row = { method: request.method, path: request.url, authorized: request.headers.authorization === `Bearer ${token}`, body: '' };
    calls.push(row);
    request.on('data', chunk => { row.body += chunk; });
    request.on('end', () => handler(request, response, row));
  });
  await new Promise(resolve => instance.listen(0, '127.0.0.1', resolve));
  t.after(() => { instance.closeAllConnections(); return new Promise(resolve => instance.close(resolve)); });
  return { origin: `http://127.0.0.1:${instance.address().port}`, calls };
}

const assertResult = (result, stdout) => {
  assert.equal(result.code, 0); assert.equal(result.stdout, stdout); assert.equal(result.stderr, '');
  for (const secret of [token, 'PRIVATE-REMOTE', 'PRIVATE-MODEL', 'PRIVATE-GH-ERROR', '\u001b']) assert.ok(!`${result.stdout}${result.stderr}`.includes(secret));
};

test('real command reads existing credentials and sends exactly one authenticated metadata GET with no source or jobs', async t => {
  const f = fixture(t), s = await server(t, (_, response) => response.end(JSON.stringify(metadata)));
  assertResult(await f.run(['-VV'], { PDD_RUNTIME_URL: s.origin }), known);
  assert.deepEqual(f.calls(), [{ args: ['auth', 'token'], stdin: '', sentinel: 'full-native-environment' }]);
  assert.deepEqual(s.calls, [{ method: 'GET', path: '/v1/version', authorized: true, body: '' }]);
  assert.deepEqual(readdirSync(f.root).sort(), ['gh', 'gh-calls.jsonl']);
});

test('real token failure stays unknown without a request or login', async t => {
  const f = fixture(t), s = await server(t, (_, response) => response.end(JSON.stringify(metadata)));
  assertResult(await f.run(['-VV'], { PDD_RUNTIME_URL: s.origin, DIAGNOSTIC_MODE: 'fail' }), unknown);
  assert.deepEqual(f.calls().map(row => row.args), [['auth', 'token']]); assert.deepEqual(s.calls, []);
});

test('real credential process is killed at its two-second deadline', async t => {
  const f = fixture(t), s = await server(t, (_, response) => response.end(JSON.stringify(metadata)));
  const start = performance.now();
  assertResult(await f.run(['-VV'], { PDD_RUNTIME_URL: s.origin, DIAGNOSTIC_MODE: 'hang' }), unknown);
  assert.ok(performance.now() - start >= 1900); assert.ok(performance.now() - start < 6500);
  assert.equal(f.calls().length, 1); assert.deepEqual(s.calls, []);
});

test('real redirects are not followed, including to a second origin', async t => {
  const f = fixture(t), destination = await server(t, (_, response) => response.end(JSON.stringify(metadata)));
  const source = await server(t, (_, response) => { response.writeHead(302, { Location: `${destination.origin}/v1/version` }); response.end('PRIVATE-REMOTE'); });
  assertResult(await f.run(['-VV'], { PDD_RUNTIME_URL: source.origin }), unknown);
  assert.equal(source.calls.length, 1); assert.deepEqual(destination.calls, []);
});

test('real HTTP failures and malformed answers stay unknown without retries', async t => {
  const f = fixture(t);
  let answer;
  const s = await server(t, (_, response) => { response.writeHead(answer.status); response.end(answer.body); });
  for (answer of [{ status: 403, body: 'PRIVATE-REMOTE' }, { status: 503, body: JSON.stringify(metadata) },
    { status: 200, body: 'not-json PRIVATE-REMOTE' }, { status: 200, body: 'null' },
    { status: 200, body: JSON.stringify({ engine_sha: 'PRIVATE-REMOTE\u001b' }) }]) {
    const before = s.calls.length;
    assertResult(await f.run(['-VV'], { PDD_RUNTIME_URL: s.origin }), unknown);
    assert.equal(s.calls.length - before, 1);
  }
});

test('real response and body stalls abort within the same ten-second total deadline', async t => {
  await Promise.all(['headers', 'body'].map(async phase => {
    const f = fixture(t); let disconnected = false;
    const s = await server(t, (_, response) => {
      response.on('close', () => { disconnected = true; });
      if (phase === 'body') setTimeout(() => {
        response.writeHead(200, { 'Content-Type': 'application/json' }); response.write('{"engine_sha":"');
      }, 4000);
    });
    const start = performance.now();
    assertResult(await f.run(['-VV'], { PDD_RUNTIME_URL: s.origin }), unknown);
    assert.ok(performance.now() - start >= 9900, phase); assert.ok(performance.now() - start < 13500, phase);
    assert.equal(s.calls.length, 1); assert.equal(disconnected, true, `${phase} work was aborted`);
  }));
});

test('real help, ordinary versions, invalid syntax and invalid origin never read a token or send a request', async t => {
  const f = fixture(t), s = await server(t, (_, response) => response.end(JSON.stringify(metadata)));
  for (const args of [['--version'], ['-V']]) {
    const result = await f.run(args, { PDD_RUNTIME_URL: s.origin }); assert.equal(result.code, 0); assert.equal(result.stdout, `${version}\n`);
  }
  for (const args of [['-VV', '--help'], ['help', '-VV'], ['-V', '--help'], ['--help']]) {
    const result = await f.run(args, { PDD_RUNTIME_URL: s.origin }); assert.equal(result.code, 0);
    assert.match(result.stdout, args[0] === '-V' ? /pdd --version/ : /pdd -VV/);
  }
  for (const args of [['-VV', 'extra'], ['-V', '-V'], ['-VVV'], ['--version', '--verbose'], ['--version', '-VV'], ['-VV', '--help', 'extra']]) {
    const result = await f.run(args, { PDD_RUNTIME_URL: s.origin }); assert.equal(result.code, 2); assert.equal(result.stdout, '');
  }
  assertResult(await f.run(['-VV'], { PDD_RUNTIME_URL: 'http://outside.invalid' }), unknown);
  assert.deepEqual(f.calls(), []); assert.deepEqual(s.calls, []);
});

test('ordinary alias preserves PATH and stale-skill output; detailed version skips both', async () => {
  const run = async argv => {
    const stdout = capture(), stderr = capture(); let paths = 0, skills = 0;
    const code = await runPdd(argv, { stdout, stderr, readPackageVersion: () => ({ ok: true, version }),
      pathDiagnostic: () => { paths++; return ['PATH conflict']; },
      findSkills: () => { skills++; return [{ found: '/fixture/skills', stale: 'older', staleSkills: [{ name: 'pdd-feature', version: '0.0.1', state: 'older' }] }]; },
      interpreterVersionPorts: { resolveOrigin: () => ({ valid: false, origin: '' }) } });
    return { code, stdout: stdout.text, stderr: stderr.text, paths, skills };
  };
  const ordinary = await run(['--version']); assert.match(ordinary.stderr, /PATH conflict/); assert.match(ordinary.stderr, /pdd-feature is 0.0.1/);
  assert.deepEqual(await run(['-V']), ordinary);
  assert.deepEqual(await run(['-VV']), { code: 0, stdout: unknown, stderr: '', paths: 0, skills: 0 });
});

test('unreadable package version fails before helper dispatch and helper failure stays safe', async () => {
  for (const packageRoot of ['/nonexistent-pdd-package']) {
    const stdout = capture(), stderr = capture(); let calls = 0;
    assert.equal(await runPdd(['-VV'], { packageRoot, stdout, stderr, interpreterVersion: { runDetailedVersion() { calls++; } } }), 1);
    assert.equal(stdout.text, ''); assert.equal(stderr.text, 'This PDD package has no readable version metadata.\n'); assert.equal(calls, 0);
  }
  const stdout = capture(), stderr = capture();
  const code = await runPdd(['-VV'], { stdout, stderr, interpreterVersion: { runDetailedVersion() { throw Error(`${token} PRIVATE-REMOTE`); } } });
  assertResult({ code, stdout: stdout.text, stderr: stderr.text }, unknown);
});

test('helper rejects unsafe build bytes and treats unsafe format lists per line', async () => {
  const get = body => runDetailedVersion({ version }, { resolveOrigin: () => ({ valid: true, origin: 'https://fixture.invalid' }),
    readToken: () => ({ token }), getMetadata: () => ({ status: 200, body: JSON.stringify(body) }) });
  for (const body of [null, [], 1, 'PRIVATE-REMOTE', {}, ...[sha + '\n', sha + '\r', sha.slice(1), sha + '0', 'g'.repeat(40), '\u001b' + sha].map(engine_sha => ({ engine_sha }))]) {
    assert.equal((await get(body)).stdout, unknown);
  }
  for (const value of [['prompt-runtime.interface.v4\n'], ['prompt-runtime.a\u001b'], Array(33).fill('prompt-runtime.a'), ['prompt-runtime.' + 'a'.repeat(129)], ['wrong-prefix.v1'], [1], {}, null]) {
    const result = await get({ engine_sha: sha, formats: { interface: value, test: [], app_map: ['prompt-runtime.app-map.v1'] } });
    assert.equal(result.stdout, `PDD CLI: ${version}\nPDD interpreter: ${sha}\nInterface formats: unknown\nTest formats: none\nApp-map formats: prompt-runtime.app-map.v1\n`);
  }
});

test('default fetch transport is injectable and its failures disclose no exception text', async () => {
  let requests = 0;
  const result = await runDetailedVersion({ version, env: { PDD_RUNTIME_URL: 'https://fixture.invalid' } }, {
    readToken: () => ({ token }), fetch: async () => { requests++; throw Error(`${token} PRIVATE-REMOTE`); },
  });
  assert.equal(requests, 1); assert.deepEqual(result, { exit_code: 0, stdout: unknown, stderr: '' });
});

test('service_sha prints lowercased 40-hex when present, unknown when malformed, and omits when absent', async () => {
  const serviceSha = 'fedcba0987654321fedcba0987654321fedcba09';
  const get = body => runDetailedVersion({ version }, { resolveOrigin: () => ({ valid: true, origin: 'https://fixture.invalid' }),
    readToken: () => ({ token }), getMetadata: () => ({ status: 200, body: JSON.stringify(body) }) });
  const withKnownService = await get({ engine_sha: sha, service_sha: serviceSha.toUpperCase(),
    formats: { interface: ['prompt-runtime.interface.v4'], test: ['prompt-runtime.program-scenario.v1'], app_map: ['prompt-runtime.app-map.v1'] } });
  assert.equal(withKnownService.stdout, `PDD CLI: ${version}\nPDD interpreter: ${sha}\nPDD service: ${serviceSha}\nInterface formats: prompt-runtime.interface.v4\nTest formats: prompt-runtime.program-scenario.v1\nApp-map formats: prompt-runtime.app-map.v1\n`);
  for (const bad of ['unknown', '', 'fedcba09', `${serviceSha}\n`, `\u001b[2J${serviceSha}`, null, 42, {}]) {
    const res = await get({ engine_sha: sha, service_sha: bad, formats: { interface: [], test: [], app_map: [] } });
    assert.equal(res.stdout, `PDD CLI: ${version}\nPDD interpreter: ${sha}\nPDD service: unknown\nInterface formats: none\nTest formats: none\nApp-map formats: none\n`);
  }
});

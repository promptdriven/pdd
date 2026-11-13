import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { PLACE, fakeRuntime, harbor, ordinaryCapabilities, portsFor } from './runtime-fake.mjs';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { interfaceBlocks, proseSha256 } from '../src/runtime-preflight.mjs';

const sha = bytes => createHash('sha256').update(bytes).digest('hex');

function stripInterface(repo, relPath = PLACE) {
  const file = join(repo, relPath);
  const text = readFileSync(file, 'utf8');
  const stripped = text.replace(interfaceBlocks(text)[0][0], '').trimEnd() + '\n';
  writeFileSync(file, stripped);
  return stripped;
}

function coldLazyLintAnswer(fake, id, prompts, { tamperScenarioHash = false } = {}) {
  const post = fake.posts.find(item => item.command === 'lint' && item.request.requestId === id);
  const listing = spawnSync('tar', ['-tf', '-'], { input: post.tar, encoding: 'utf8' });
  assert.equal(listing.status, 0, listing.stderr);
  const paths = listing.stdout.split('\n').filter(Boolean);
  const sources = paths.map(path => {
    const file = spawnSync('tar', ['-xOf', '-', path], { input: post.tar });
    assert.equal(file.status, 0, file.stderr.toString());
    return { path, bytes: file.stdout };
  });
  const tests = sources
    .filter(source => { try { return JSON.parse(source.bytes).schema_version === 'prompt-runtime.program-scenario.v1'; } catch { return false; } })
    .map(({ path }) => {
      const base = ordinaryCapabilities(sources, path);
      const report = {
        ...base,
        ...(tamperScenarioHash ? { source: { ...base.source, scenario_sha256: 'f'.repeat(64) } } : {}),
        complete: false,
        verdict: 'unknown',
        operations: [],
        edges: [],
      };
      return { path, verdict: 'passed', capabilities: report };
    });
  return fake.job(id, 'lint', 'passed', {
    exitCode: 0,
    refusals: [],
    capabilities: tests.map(item => ({ path: item.path, report: item.capabilities })),
    capabilities_complete: false,
    report: {
      verdict: 'passed',
      lint: { complete: true, tests: tests.map(({ path, verdict }) => ({ path, verdict })) },
      program: { prompts, refused_prompts: [] },
    },
  });
}

test('LAZY-1: legacy server without lazy-interfaces refuses interface-less prompts locally in lint, test and simulate', async t => {
  const setup = harbor(t, repo => { stripInterface(repo); });
  const fake = await fakeRuntime(t, () => assert.fail('legacy server must not receive uploads for interface-missing'));
  fake.capacity = () => ({ status: 200, json: { maintenance: null, features: ['lint-tests'], engine_sha: 'eae2202a68d00ab762fcbbf1eba0d8607a132a15' } });
  const env = { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state };

  const lintPorts = portsFor(env).ports;
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--lint': true, '--json': true } }, lintPorts), 4);
  const lintJson = JSON.parse(lintPorts.stdout.text);
  assert.ok(lintJson.problems.some(item => item.code === 'interface-missing' && item.path === PLACE));
  assert.equal(fake.posts.length, 0);

  const checkPorts = portsFor(env).ports;
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, checkPorts), 4);
  const checkJson = JSON.parse(checkPorts.stdout.text);
  assert.equal(checkJson.rows[0].refusals[0].code, 'interface-missing');
  assert.equal(fake.posts.length, 0);

  const tryPorts = portsFor(env, { openUrl: async () => true, caseHandoff: async ({ testPath }) => ({ kind: 'closed-editor', testPath }) }).ports;
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true, '--no-wait': true } }, tryPorts), 4);
  assert.match(tryPorts.stdout.text, /interface-missing/);
  assert.equal(fake.posts.length, 0);
});

test('LAZY-2: cold and warm lazy lint pass on lazy-interfaces server, preserve association checks and omit draft noise', async t => {
  const setup = harbor(t, repo => { stripInterface(repo); });
  let mode = 'cold';
  const fake = await fakeRuntime(t, (entry, f) => {
    assert.equal(entry.method, 'POST');
    assert.equal(entry.command, 'lint');
    assert.equal(entry.request.lazy_interfaces, true);
    if (mode === 'cold') {
      return {
        status: 200,
        json: coldLazyLintAnswer(f, entry.request.requestId, [
          { path: PLACE, state: 'missing', admission_state: 'missing', lazy_interface_pending: true, interface: null, dependencies: [] },
        ]),
      };
    }
    if (mode === 'tampered') {
      return {
        status: 200,
        json: coldLazyLintAnswer(f, entry.request.requestId, [
          { path: PLACE, state: 'missing', admission_state: 'missing', lazy_interface_pending: true, interface: null, dependencies: [] },
        ], { tamperScenarioHash: true }),
      };
    }
    return {
      status: 200,
      json: f.lint(entry.request.requestId, [
        { path: PLACE, state: 'draft', admission_state: 'draft', lazy_interface: true, interface: { calls: [] }, dependencies: [] },
      ]),
    };
  });
  fake.capacity = () => ({
    status: 200,
    json: { maintenance: null, features: ['lint-tests', 'lint-call-preflight', 'lazy-interfaces'], engine_sha: 'eae2202a68d00ab762fcbbf1eba0d8607a132a15' },
  });
  const env = { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state };

  const coldPorts = portsFor(env).ports;
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--lint': true, '--json': true } }, coldPorts), 0, coldPorts.stderr.text);
  const coldJson = JSON.parse(coldPorts.stdout.text);
  assert.equal(coldJson.lint_state, 'passed');
  assert.deepEqual(coldJson.coverage.runtime, { checkable: 1, total: 1, native_only: 0 });
  assert.ok(coldJson.rows.every(row => row.state === 'passed' && !row.draft));

  mode = 'warm';
  const warmPorts = portsFor(env).ports;
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--lint': true, '--json': true } }, warmPorts), 0, warmPorts.stderr.text);
  const warmJson = JSON.parse(warmPorts.stdout.text);
  assert.equal(warmJson.lint_state, 'passed');
  assert.ok(warmJson.rows.every(row => row.state === 'passed' && !row.draft));

  mode = 'tampered';
  const tamperedPorts = portsFor(env).ports;
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--lint': true, '--json': true } }, tamperedPorts), 5);
  const tamperedJson = JSON.parse(tamperedPorts.stdout.text);
  assert.ok(tamperedJson.rows.every(row => row.state === 'not run' && row.compatibility?.association !== 'matched'));
});

test('LAZY-3: pdd test runs interface-less dependency closure with pdd-boundary + pdd-bindings.json and caches pass locally', async t => {
  const setup = harbor(t, repo => {
    const base = stripInterface(repo);
    mkdirSync(join(repo, 'src'), { recursive: true });
    writeFileSync(join(repo, 'src/order.mjs'), 'export const ok = true;\n');
    writeFileSync(join(repo, 'prompts/pricing.prompt.md'), '# Pricing helper\n\nCompute line-item totals in cents.\n');
    writeFileSync(join(repo, PLACE), base.replace('None.', '- [Pricing](pricing.prompt.md)'));
    const storyPath = join(repo, 'user_stories/place-order.md');
    writeFileSync(storyPath, `${readFileSync(storyPath, 'utf8').trimEnd()}\n\n\`\`\`pdd-boundary\nprompts/place_order.prompt.md\nprompts/pricing.prompt.md\n\`\`\`\n`);
    writeFileSync(join(repo, 'pdd-bindings.json'), JSON.stringify({
      schema_version: 'pdd.bindings.v1',
      modules: [{ module: 'src/order.mjs', stories: ['user_stories/place-order.md', 'user_stories/unknown-item.md'], prompt: 'prompts/pricing.prompt.md' }],
    }, null, 2) + '\n');
    spawnSync('git', ['add', '-A'], { cwd: repo });
    spawnSync('git', ['-c', 'user.email=t@example.com', '-c', 'user.name=t', 'commit', '-qm', 'plain prompts'], { cwd: repo });
  });

  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') {
      assert.equal(entry.request.lazy_interfaces, true);
      return {
        status: 200,
        json: coldLazyLintAnswer(f, entry.request.requestId, [
          { path: PLACE, state: 'missing', admission_state: 'missing', lazy_interface_pending: true, interface: null, dependencies: ['prompts/pricing.prompt.md'] },
          { path: 'prompts/pricing.prompt.md', state: 'missing', admission_state: 'missing', lazy_interface_pending: true, interface: null, dependencies: [] },
        ]),
      };
    }
    if (entry.method === 'POST' && entry.command === 'check') {
      assert.equal(entry.request.lazy_interfaces, true);
      const listing = spawnSync('tar', ['-tf', '-'], { input: entry.tar, encoding: 'utf8' });
      assert.ok(listing.stdout.split('\n').includes('prompts/pricing.prompt.md'), 'markdown dependency must be uploaded');
      return { status: 202, json: f.check(entry.request.requestId, 'queued') };
    }
    return { status: 200, json: f.check(entry.url.split('/').at(-1)) };
  });
  fake.capacity = () => ({
    status: 200,
    json: { maintenance: null, features: ['lint-tests', 'lazy-interfaces'], engine_sha: 'eae2202a68d00ab762fcbbf1eba0d8607a132a15' },
  });
  const env = { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state };

  const first = portsFor(env).ports;
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--json': true }, cache: true }, first), 0, first.stderr.text);
  const firstJson = JSON.parse(first.stdout.text);
  assert.equal(firstJson.rows.length, 2);
  assert.ok(firstJson.rows.every(row => row.state === 'passed' && !row.draft));
  assert.deepEqual(firstJson.coverage.runtime, { checkable: 2, total: 2, native_only: 0 });
  assert.equal(firstJson.coverage.bound, 1);
  assert.equal(fake.posts.filter(p => p.command === 'lint').length, 1);
  assert.equal(fake.posts.filter(p => p.command === 'check').length, 2);

  // Second run reuses local .pdd/cache/test/ with 0 new server jobs!
  const postsBefore = fake.posts.length;
  const second = portsFor(env).ports;
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--json': true }, cache: true }, second), 0, second.stderr.text);
  const secondJson = JSON.parse(second.stdout.text);
  assert.ok(secondJson.rows.every(row => row.state === 'passed' && row.cached === true && row.calls === 0));
  assert.equal(fake.posts.length, postsBefore);
});

test('LAZY-4: pdd simulate starts, reuses and stops a Try on an interface-less repo with lazy_interfaces: true', async t => {
  const setup = harbor(t, repo => { stripInterface(repo); });
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') {
      assert.equal(entry.request.lazy_interfaces, true);
      return {
        status: 200,
        json: coldLazyLintAnswer(f, entry.request.requestId, [
          { path: PLACE, state: 'missing', admission_state: 'missing', lazy_interface_pending: true, interface: null, dependencies: [] },
        ]),
      };
    }
    if (entry.method === 'POST' && entry.command === 'try') {
      assert.equal(entry.request.lazy_interfaces, true);
      return { status: 202, json: f.job(entry.request.requestId, 'try', 'queued') };
    }
    if (entry.method === 'DELETE') {
      return { status: 202, json: { ...f.job(entry.headers['x-request-id'], 'stop', 'running'), session_id: entry.url.split('/').at(-1) } };
    }
    const id = entry.url.split('/').at(-1), stop = f.deletes.find(item => item.headers['x-request-id'] === id);
    if (stop) return { status: 200, json: f.stopJob(id, stop.url.split('/').at(-1)) };
    const stopped = f.deletes.some(item => item.url.endsWith(`/${id}`));
    return { status: 200, json: f.tryJob(id, undefined, stopped ? 'stopped' : 'running') };
  });
  fake.capacity = () => ({
    status: 200,
    json: { maintenance: null, features: ['lint-tests', 'lazy-interfaces'], engine_sha: 'eae2202a68d00ab762fcbbf1eba0d8607a132a15' },
  });
  const env = { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state };
  const makePorts = () => portsFor(env, { openUrl: async () => true, caseHandoff: async ({ testPath }) => ({ kind: 'closed-editor', testPath }) }).ports;

  const first = makePorts();
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true, '--no-wait': true } }, first), 0, first.stderr.text);
  assert.deepEqual(fake.posts.map(p => p.command), ['lint', 'try']);
  assert.match(first.stdout.text, /Try ready for "Place a coffee order"/);

  const reused = makePorts();
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true, '--no-wait': true } }, reused), 0, reused.stderr.text);
  assert.equal(fake.posts.length, 2, 'unchanged interface-less prompt reuses open Try');

  const stopped = makePorts();
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--stop': true } }, stopped), 0, stopped.stderr.text);
  assert.equal(fake.deletes.length, 1);
});

test('LAZY-5: malformed/stale embedded blocks and transitive native-only prompts still stay local under lazy-interfaces, and --fill-hash skips plain prompts', async t => {
  // 1) --fill-hash on interface-less prompt is a clean no-op
  const plain = harbor(t, repo => { stripInterface(repo); });
  const fillPorts = portsFor({ HOME: plain.home, PDD_STATE_DIR: plain.state }, {
    gh: () => assert.fail('--fill-hash must not authenticate'),
    fetch: () => assert.fail('--fill-hash must not contact Runtime'),
  }).ports;
  const beforeText = readFileSync(join(plain.repo, PLACE), 'utf8');
  assert.equal(await runCheck({ cwd: plain.repo, options: { '--fill-hash': true } }, fillPorts), 0, fillPorts.stderr.text);
  assert.equal(readFileSync(join(plain.repo, PLACE), 'utf8'), beforeText);

  // 2) Stale embedded interface is still refused locally with 0 capacity probes and 0 uploads
  const stale = harbor(t, repo => {
    const file = join(repo, PLACE);
    writeFileSync(file, readFileSync(file, 'utf8').replace('Use this menu.', 'Use this menu right now.'));
  });
  const staleFake = await fakeRuntime(t, () => assert.fail('stale embedded interface must not upload'));
  staleFake.capacity = () => { assert.fail('stale embedded interface must not probe capacity'); };
  const stalePorts = portsFor({ HOME: stale.home, PDD_RUNTIME_URL: staleFake.origin, PDD_STATE_DIR: stale.state }, {
    gh: () => assert.fail('stale embedded interface must not sign in'),
  }).ports;
  assert.equal(await runCheck({ cwd: stale.repo, words: ['place-order'], options: { '--json': true } }, stalePorts), 4);
  assert.equal(JSON.parse(stalePorts.stdout.text).rows[0].refusals[0].code, 'interface-stale');

  // 3) Transitive native-only prompt reached via markdown Dependencies from an interface-less prompt is skipped locally without uploading
  const transitiveNative = harbor(t, repo => {
    const base = stripInterface(repo);
    let native = '# Kernel\n\n<details><summary>Runtime interface</summary>\n\n```json\n'
      + JSON.stringify({ kind: 'native-only', status: 'draft', prose_sha256: '', reason: 'Kernel lock cannot be simulated.' }) + '\n```\n</details>\n';
    native = native.replace('"prose_sha256":""', `"prose_sha256":"${proseSha256(native)}"`);
    writeFileSync(join(repo, 'prompts/kernel.prompt.md'), native);
    writeFileSync(join(repo, PLACE), base.replace('None.', '- [Kernel](kernel.prompt.md)'));
  });
  const nativeFake = await fakeRuntime(t, () => assert.fail('transitive native-only test must not upload'));
  nativeFake.capacity = () => ({ status: 200, json: { maintenance: null, features: ['lint-tests', 'lazy-interfaces'] } });
  const nativePorts = portsFor({ HOME: transitiveNative.home, PDD_RUNTIME_URL: nativeFake.origin, PDD_STATE_DIR: transitiveNative.state }).ports;
  assert.equal(await runCheck({ cwd: transitiveNative.repo, words: ['place-order'], options: { '--json': true } }, nativePorts), 5);
  const nativeJson = JSON.parse(nativePorts.stdout.text);
  assert.equal(nativeJson.rows[0].state, 'not run');
  assert.match(nativeJson.rows[0].reason.message, /Kernel lock/);
  assert.equal(nativeFake.posts.length, 0);
});

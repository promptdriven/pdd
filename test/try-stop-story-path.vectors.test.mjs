import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdirSync, readFileSync, realpathSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runTry } from '../src/runtime-client.mjs';
import { harbor, portsFor } from './runtime-fake.mjs';

const at = (value, pointer) => pointer.split('/').slice(1).reduce((v, key) => v?.[key.replaceAll('~1', '/').replaceAll('~0', '~')], value);
const clone = value => structuredClone(value);

function triesMapToArray(tries = {}) {
  return Object.entries(tries).map(([test_path, record]) => ({ test_path, ...record }));
}

function triesArrayToMap(items = []) {
  return Object.fromEntries(items.map(({ test_path, ...record }) => [test_path, clone(record)]));
}

test('try-stop-story-path: replay approved Story cases on native code', async t => {
  const scenario = JSON.parse(readFileSync(new URL('runtime/try-stop-story-path.json', import.meta.url), 'utf8'));
  const setup = harbor(t);
  const realRoot = realpathSync(setup.repo);
  const repoKey = createHash('sha256').update(realRoot).digest('hex').slice(0, 16);
  const reposDir = join(setup.state, 'repos');
  mkdirSync(reposDir, { recursive: true, mode: 0o700 });
  const repoStatePath = join(reposDir, `${repoKey}.json`);

  const world = clone(scenario.initial_world);
  writeFileSync(repoStatePath, `${JSON.stringify({
    root: realRoot,
    last_batch: null,
    tries: triesArrayToMap(world.kv.tries),
  }, null, 2)}\n`, { mode: 0o600 });

  for (const step of scenario.steps) {
    const counts = {
      '/resources/runtime-client-runtime-stop': 0,
      '/resources/runtime-client-state-save': 0,
    };
    const beforeStat = statSync(repoStatePath);
    const beforeRaw = readFileSync(repoStatePath, 'utf8');

    const { ports } = portsFor(
      { HOME: setup.home, PDD_STATE_DIR: setup.state },
      {
        fetch: async (url, init = {}) => {
          const parsed = new URL(String(url));
          if (init.method === 'DELETE' && parsed.pathname.startsWith('/v1/try/')) {
            counts['/resources/runtime-client-runtime-stop'] += 1;
            const tryId = parsed.pathname.split('/').at(-1);
            const requestId = init.headers?.['X-Request-Id'] ?? init.headers?.['x-request-id'];
            assert.match(String(requestId), /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i);
            world.requests.push({ tryId, requestId });
            const body = JSON.stringify({
              requestId,
              id: requestId,
              command: 'stop',
              state: 'passed',
              engine_sha: 'eae2202a68d00ab762fcbbf1eba0d8607a132a15',
              result: { exitCode: 0, refusals: [], output: 'Try stopped.', session: { id: tryId, state: 'stopped' } },
            });
            return { status: 200, headers: new Headers({ 'content-type': 'application/json' }), text: async () => body };
          }
          assert.fail(`Unexpected fetch call: ${init.method} ${url}`);
        },
      },
    );

    const exit_code = await runTry({ ...clone(step.input), cwd: setup.repo }, ports);
    const afterStat = statSync(repoStatePath);
    const afterRaw = readFileSync(repoStatePath, 'utf8');
    if (afterStat.ino !== beforeStat.ino || afterRaw !== beforeRaw) {
      counts['/resources/runtime-client-state-save'] += 1;
    }
    const savedRepoState = JSON.parse(afterRaw);
    world.kv.tries = triesMapToArray(savedRepoState.tries);

    const result = {
      exit_code,
      stdout: ports.stdout.text,
      stderr: ports.stderr.text,
    };

    for (const check of step.checks) {
      if (check.target === 'calls') assert.ok(Object.hasOwn(counts, check.path), `Unknown call-count path: ${check.path}`);
      const value = check.target === 'calls' ? counts[check.path] : at(check.target === 'world' ? world : result, check.path);
      const label = `try-stop-story-path/${step.step_id}/${check.criterion_id} ${check.target} ${check.path}`;
      if (check.op === 'equals') assert.deepEqual(value, check.value, label);
      else if (check.op === 'contains') assert.ok(value.includes(check.value), label);
      else assert.fail(`Unmapped assertion ${check.op}: ${label}`);
    }
  }
});

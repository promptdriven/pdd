import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { coreWorld } from './helpers/core-world.mjs';
import { readyIssues } from '../src/autopilot-core.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/autopilot-route-other-repo.json', import.meta.url), 'utf8'));
for (const step of scenario.steps) {
  test(step.step_id, async () => {
    const { planIssueRouting } = await import('../src/autopilot-repo-routing.mjs');
    assert.deepEqual(planIssueRouting(step.input), step.checks[0].value);
  });
}

const repository = 'promptdriven/pdd';
const label = 'pdd:elsewhere';
const response = (status, body) => ({ code: status < 300 ? 0 : 1, stdout: `HTTP/2.0 ${status}\r\n\r\n${JSON.stringify(body)}`, stderr: '' });

function routingGithub(world, before = () => undefined) {
  const upstream = world.github.gh;
  let defined = false;
  world.github.gh = async (args, options) => {
    const method = args[args.indexOf('--method') + 1];
    const endpoint = args.find(arg => arg.startsWith(`repos/${repository}/`));
    const input = options?.input ? JSON.parse(options.input) : null;
    const override = before(method, endpoint, input);
    if (override) return override;
    if (method === 'GET' && endpoint === `repos/${repository}/labels/${encodeURIComponent(label)}`) {
      return defined ? response(200, { name: label }) : response(404, { message: 'Not Found' });
    }
    if (method === 'POST' && endpoint === `repos/${repository}/labels` && input?.name === label) {
      defined = true;
      return response(201, { name: label });
    }
    if (method === 'POST' && input?.labels?.includes(label) && !defined) return response(422, { message: 'Undefined label' });
    return upstream(args, options);
  };
}

test('core routes foreign work before claiming and backfills with local work', async t => {
  const world = await coreWorld(t, { repository, settings: { runs: 3 } });
  routingGithub(world);
  for (const [index, step] of scenario.steps.entries()) world.issue(index + 1, step.input);
  world.issue(6, { user: 'outside', title: '[prompt-runtime] Untrusted issue' });
  assert.deepEqual(await readyIssues({ state: world.state, settings: world.settings }, world.ports()), [4, 5]);
  assert.equal(world.github.writes.length, 0, 'the ready listing does not publish routing annotations');

  await world.tick();
  await world.tick();
  for (const [index, target] of ['prompt-runtime', 'runtime-client', 'pdd_cloud'].entries()) {
    const issue = index + 1;
    assert.deepEqual(world.labels(issue), [label]);
    assert.equal(world.comments(issue).length, 1);
    assert.ok(world.comments(issue)[0].includes(`promptdriven/${target}`));
    assert.ok(world.github.issues.get(issue).timeline.every(event => event.label !== 'pdd:working'));
    assert.equal(world.job(issue, 'build'), undefined);
    assert.equal(existsSync(join(world.root, 'worktrees', String(issue))), false);
  }
  assert.deepEqual(world.labels(6), []);
  assert.deepEqual(world.comments(6), []);
  assert.ok(world.job(4, 'build'));
  assert.ok(world.job(5, 'build'));
});

test('active core routes an explicit foreign target even without an intake card', async t => {
  const world = await coreWorld(t, { repository, settings: { intake: 'active' } });
  routingGithub(world);
  world.issue(1, scenario.steps[0].input);
  await world.tick();
  assert.deepEqual(world.labels(1), [label]);
  assert.deepEqual(world.started, []);
});

test('core retries a failed routing label without claiming or repeating the comment', async t => {
  const world = await coreWorld(t, { repository });
  let fail = true;
  routingGithub(world, (method, endpoint, input) => {
    if (fail && method === 'POST' && endpoint === `repos/${repository}/issues/1/labels` && input?.labels?.includes(label)) {
      fail = false;
      return response(503, { message: 'Try again' });
    }
  });
  world.issue(1, scenario.steps[0].input);
  await world.tick();
  assert.deepEqual(world.labels(1), []);
  assert.equal(world.started.length, 0);
  assert.equal(world.comments(1).length, 1);
  await world.tick();
  assert.deepEqual(world.labels(1), [label]);
  assert.equal(world.comments(1).length, 1);
});

test('core rechecks an issue whose target changes before the claim', async t => {
  const world = await coreWorld(t, { repository });
  const issue = world.issue(1, { title: 'Fix retries' });
  routingGithub(world, (method, endpoint) => {
    if (method === 'GET' && endpoint === `repos/${repository}/issues/1`) issue.title = '[prompt-runtime] Fix retries';
  });
  await world.tick();
  assert.deepEqual(world.labels(1), [label]);
  assert.equal(world.started.length, 0);
  assert.equal(existsSync(join(world.root, 'worktrees', '1')), false);
});

test('core leaves an existing claim alone and accepts a corrected target after unlabeling', async t => {
  const world = await coreWorld(t, { repository });
  routingGithub(world);
  const claimed = world.issue(1, scenario.steps[0].input);
  world.github.label(claimed.number, 'pdd:working');
  const routed = world.issue(2, scenario.steps[0].input);
  await world.tick();
  assert.deepEqual(world.labels(1), ['pdd:working']);
  assert.deepEqual(world.comments(1), []);
  assert.deepEqual(world.labels(2), [label]);

  routed.title = '[pdd] Fix duplicate retries';
  world.github.unlabel(routed.number, label);
  await world.tick();
  assert.ok(world.job(2, 'build'));
  assert.deepEqual(world.labels(2), ['pdd:working']);
});

import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { issueVersion, checkIssue, improveIssue, askPerson, intakeGate } from '../src/autopilot-intake.mjs';
import { startAgentJob, readAgentJob, stopAgentJob } from '../src/agent-job.mjs';

const ready = { state: 'ready', missing: [], acceptance: ['Empty input prints an empty list.'], question: '', links: [] };
const improve = { state: 'improve', missing: ['Testable criteria'], acceptance: ['Empty input prints an empty list.'], question: '', links: [] };
const ask = { state: 'ask', missing: ['Empty input policy'], acceptance: [], question: 'Should empty input print a list or an error?', links: [] };
const clone = x => structuredClone(x);
function world(t, results = []) {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-intake-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  let time = 1000;
  const issue = { number: 17, state: 'open', title: 'Handle empty input', body: 'Make empty input useful.', labels: [], assignees: [], comments: [] };
  const started = [], runs = new Map(), writes = [], labels = new Set();
  const ctx = { root, repo: 'example/widgets', state: { cwd: root, agent: { kind: 'codex' } }, now: () => time, timeout: 10000,
    jobs: {
      start(spec) {
        started.push(spec);
        const job = { id: spec.id, pid: started.length, token: join(spec.dir, `${spec.id}.spec.json`),
          result: join(spec.dir, `${spec.id}.result.json`), started: time };
        assert.ok(results.length, 'unexpected second agent check');
        runs.set(job.id, { state: 'exited', exit: { code: 0 }, result: clone(results.shift()) });
        return job;
      },
      read: job => runs.get(job.id),
      stop: job => writes.push(['stop', job.id]),
    },
    gh: {
      async all(path) {
        if (path.includes('/comments?')) return clone(issue.comments);
        if (path.endsWith('/labels?per_page=100')) return [...labels].map(name => ({ name }));
        throw Error(`Unexpected GET ${path}`);
      },
      async ok(method, path, body) {
        if (method === 'POST' && path.endsWith('/comments')) {
          writes.push(['comment', body.body]);
          const comment = { id: issue.comments.length + 1, body: body.body, user: { login: 'operator', type: 'User' } };
          issue.comments.push(comment); return clone(comment);
        }
        if (method === 'POST' && path === 'repos/example/widgets/labels') { writes.push(['create-label', body.name]); labels.add(body.name); return body; }
        if (method === 'POST' && path.endsWith('/labels')) {
          writes.push(['label', body.labels]);
          issue.labels = [...new Set([...issue.labels, ...body.labels])]; return issue.labels;
        }
        throw Error(`Unexpected ${method} ${path}`);
      },
    },
  };
  const ports = () => ({ ...ctx, cwd: ctx.state.cwd, agent: ctx.state.agent });
  return { root, ctx, ports, issue, started, runs, writes, advance: ms => { time += ms; } };
}
const comments = w => w.writes.filter(x => x[0] === 'comment').map(x => x[1]);

test('version tracks body, labels, assignees and person decisions but ignores ordering and bot chatter', () => {
  const issue = { body: 'before', labels: ['z', { name: 'a' }], assignees: ['person', { login: 'other' }],
    comments: [{ id: 1, body: 'Use empty list', user: { login: 'person', type: 'User' } }] };
  const version = issueVersion(issue);
  assert.match(version, /^[a-f0-9]{64}$/);
  assert.equal(issueVersion({ ...issue, labels: ['a', 'z', 'a'], assignees: ['other', 'person'], updatedAt: 'later',
    comments: [...issue.comments, { body: 'noise', author: { login: 'bot', __typename: 'Bot' } },
      { body: 'noise', user: { login: 'automated[bot]' } },
      { body: 'criteria\n<!-- pdd:intake:improve:abc -->', user: { login: 'operator', type: 'User' } }] }), version);
  for (const patch of [{ body: 'after' }, { labels: ['b'] }, { assignees: ['third'] }, { comments: [{ id: 1, body: 'Use error', author: { login: 'person' } }] }]) {
    assert.notEqual(issueVersion({ ...issue, ...patch }), version);
  }
  assert.equal(issueVersion({ ...issue, comments: { nodes: issue.comments } }), version);
});

test('unclear issue gets one improved-criteria comment, follow-up check, then ready without a body edit', async t => {
  const w = world(t, [improve, ready]), body = w.issue.body;
  const result = await intakeGate(w.ctx, [w.issue]);
  assert.deepEqual(result.ready, [w.issue]); assert.equal(result.ready[0], w.issue);
  assert.deepEqual(result.actions.map(a => a.type), ['improve', 'ready']);
  assert.equal(w.started.length, 2); assert.equal(comments(w).length, 1);
  assert.match(comments(w)[0], /1\. Empty input prints an empty list\./);
  assert.match(comments(w)[0], /<!-- pdd:intake:improve:[a-f0-9]{64} -->/);
  assert.equal(w.issue.body, body);
  const again = await intakeGate({ ...w.ctx }, [clone(w.issue)]);
  assert.equal(again.ready.length, 1); assert.equal(w.started.length, 2); assert.equal(comments(w).length, 1);
});

test('still unclear after improvement asks one question, labels it and waits across label versions', async t => {
  const w = world(t, [improve, { ...improve, missing: ['Empty input policy'] }]);
  const result = await intakeGate(w.ctx, [w.issue]);
  assert.deepEqual(result.ready, []); assert.deepEqual(result.actions.map(a => a.type), ['improve', 'ask']);
  assert.equal(comments(w).length, 2); assert.match(comments(w)[1], /\?/);
  assert.ok(w.issue.labels.includes('pdd:needs-decision'));
  for (let i = 0; i < 3; i++) assert.deepEqual((await intakeGate(w.ctx, [w.issue])).ready, []);
  assert.equal(comments(w).length, 2); assert.equal(w.started.length, 2);
});

test('a person answer and removed label permit a fresh ready check; either alone keeps waiting', async t => {
  const w = world(t, [ask, ready]);
  await intakeGate(w.ctx, [w.issue]);
  w.issue.labels = [];
  assert.equal((await intakeGate(w.ctx, [w.issue])).actions[0].type, 'waiting');
  assert.equal(w.started.length, 1, 'label removal alone is not an answer');
  w.issue.labels = ['pdd:needs-decision'];
  w.issue.comments.push({ id: 99, body: 'Use an empty list.', user: { login: 'person', type: 'User' } });
  assert.equal((await intakeGate(w.ctx, [w.issue])).actions[0].type, 'waiting');
  w.issue.labels = [];
  assert.deepEqual((await intakeGate(w.ctx, [w.issue])).ready, [w.issue]);
  assert.equal(w.started.length, 2); assert.equal(comments(w).length, 1);
});

test('same version checks once across concurrent calls, restart, and later ticks', async t => {
  const w = world(t, [ready]);
  const results = await Promise.all([checkIssue(w.issue, w.ports()), checkIssue(clone(w.issue), w.ports())]);
  assert.deepEqual(results, [ready, ready]);
  assert.deepEqual(await checkIssue(w.issue, { ...w.ports() }), ready);
  assert.equal(w.started.length, 1);
  w.issue.body = 'A changed request';
  w.ctx.jobs.start = spec => { w.started.push(spec); return { id: spec.id }; };
  w.ctx.jobs.read = () => ({ state: 'running', exit: null, result: ready });
  assert.equal(await checkIssue(w.issue, w.ports()), null);
  assert.equal(await checkIssue(w.issue, w.ports()), null);
  assert.equal(w.started.length, 2, 'a running result is not yet a completed check');
});

test('shadow records a proposal, makes no GitHub writes and live mode can apply the cached check', async t => {
  const w = world(t, [improve, ready]);
  const result = await intakeGate({ ...w.ctx, shadow: true }, [w.issue]);
  assert.deepEqual(result.ready, []); assert.equal(result.actions[0].type, 'improve');
  assert.equal(result.actions[0].shadow, true); assert.deepEqual(w.writes, []); assert.equal(w.started.length, 1);
  assert.equal((await intakeGate(w.ctx, [w.issue])).ready.length, 1);
  assert.equal(w.started.length, 2); assert.equal(comments(w).length, 1);
});

test('shadow asks without creating an active waiting episode or label', async t => {
  const w = world(t, [ask]);
  assert.equal((await intakeGate({ ...w.ctx, shadow: true }, [w.issue])).actions[0].type, 'ask');
  assert.deepEqual(w.writes, []);
  assert.equal((await intakeGate(w.ctx, [w.issue])).actions[0].type, 'ask');
  assert.equal(comments(w).length, 1); assert.equal(w.started.length, 1);
});

test('a lost comment response is reconciled by marker before continuing', async t => {
  const w = world(t, [improve, ready]), original = w.ctx.gh.ok;
  let lost = true;
  w.ctx.gh.ok = async (...args) => {
    const result = await original(...args);
    if (lost && args[1].endsWith('/comments')) { lost = false; throw Error('lost response'); }
    return result;
  };
  assert.equal((await intakeGate(w.ctx, [w.issue])).actions.at(-1).type, 'error');
  assert.equal((await intakeGate(w.ctx, [w.issue])).ready.length, 1);
  assert.equal(comments(w).length, 1); assert.equal(w.started.length, 2);
});

test('question label failures retry the label without another question or check', async t => {
  const w = world(t, [ask]), original = w.ctx.gh.ok;
  let fail = true;
  w.ctx.gh.ok = async (...args) => {
    if (fail && args[1].endsWith('/17/labels')) { fail = false; throw Error('label unavailable'); }
    return original(...args);
  };
  assert.equal((await intakeGate(w.ctx, [w.issue])).actions.at(-1).type, 'error');
  await intakeGate(w.ctx, [w.issue]);
  assert.equal(comments(w).length, 1); assert.equal(w.started.length, 1);
  assert.ok(w.issue.labels.includes('pdd:needs-decision'));
});

test('held rows are not checked; REST comment counts are hydrated before versioning', async t => {
  const w = world(t, [ready]);
  const held = [{ ...w.issue, number: 1, assignees: [{ login: 'person' }] }, { ...w.issue, number: 2, state: 'closed' },
    { ...w.issue, number: 3, pull_request: {} }, { ...w.issue, number: 4, labels: ['pdd:working'] }];
  w.issue.comments.push({ body: 'Keep existing behavior', user: { login: 'person' } });
  const row = { ...w.issue, comments: 1 };
  const result = await intakeGate(w.ctx, [...held, row]);
  assert.deepEqual(result.ready, [row]); assert.equal(w.started.length, 1);
  assert.match(w.started[0].input, /Keep existing behavior/);
  assert.deepEqual(result.actions.map(a => a.type), ['held', 'held', 'held', 'held', 'ready']);
});

test('malformed or failed agent output never makes ready or asks a person, and failure is cached', async t => {
  for (const output of [{ state: 'ready' }, { ...ready, links: [{ type: 'blocked-by', issue: 9, reason: 'Needs contract' }] },
    { ...ask, question: '' }, { ...improve, acceptance: [] }]) {
    const w = world(t, [output]);
    for (let i = 0; i < 2; i++) {
      const result = await intakeGate(w.ctx, [w.issue]);
      assert.deepEqual(result.ready, []); assert.equal(result.actions[0].type, 'error');
    }
    assert.equal(w.started.length, 1); assert.deepEqual(w.writes, []);
  }
});

test('failed process and timeout are cached, stop running jobs, and never re-launch', async t => {
  const w = world(t, [ready]);
  w.ctx.jobs.read = () => ({ state: 'exited', exit: { code: 4 }, result: ready });
  await assert.rejects(checkIssue(w.issue, w.ports()), /exit|failed/i);
  await assert.rejects(checkIssue(w.issue, w.ports()), /exit|failed/i);
  assert.equal(w.started.length, 1);
  w.issue.body = 'Changed input';
  w.ctx.jobs.read = () => ({ state: 'running', exit: null, result: null });
  // Scripted second start, with a pending outcome.
  w.ctx.jobs.start = spec => { w.started.push(spec); return { id: spec.id, started: 1000 }; };
  assert.equal(await checkIssue(w.issue, w.ports()), null);
  w.advance(10001);
  await assert.rejects(checkIssue(w.issue, w.ports()), /timed out/i);
  assert.equal(w.writes.filter(x => x[0] === 'stop').length, 1);
  await assert.rejects(checkIssue(w.issue, w.ports()), /timed out/i);
  assert.equal(w.started.length, 2);
});

test('dependency and duplicate links are returned as evidence, never native link mutations', async t => {
  const result = { ...ask, links: [{ type: 'blocked-by', issue: 9, reason: 'The required record is defined there.' },
    { type: 'duplicate-of', issue: 'https://github.com/other/project/issues/5', reason: 'Same function and cause.' }] };
  const w = world(t, [result]);
  assert.deepEqual(await checkIssue(w.issue, w.ports()), result);
  await askPerson(w.issue, result, w.ports());
  assert.ok(w.writes.every(x => ['comment', 'label', 'create-label'].includes(x[0])));
});

test('direct improvement reuses its comment and augmented check, with isolated repository caches', async t => {
  const w = world(t, [ready, ready]);
  assert.deepEqual(await improveIssue(w.issue, improve, w.ports()), ready);
  assert.deepEqual(await improveIssue(w.issue, improve, w.ports()), ready);
  assert.equal(comments(w).length, 1); assert.equal(w.started.length, 1);
  assert.deepEqual(await checkIssue(w.issue, { ...w.ports(), repo: 'other/project' }), ready);
  assert.equal(w.started.length, 2);
});

test('native agent-job wrapper runs a scripted process and the next check reads its saved result', async t => {
  const w = world(t), jobs = [];
  const release = join(w.root, 'release-scripted-job');
  const script = `let input=''; process.stdin.on('data', x=>input+=x); process.stdin.on('end',()=>{
    const p=JSON.parse(input.split('\\n').find(x=>x.startsWith('INTAKE_PACKET ')).slice(14));
    const wait=setInterval(()=>{if(require('fs').existsSync(${JSON.stringify(release)})) {
      clearInterval(wait); require('fs').writeFileSync(p.result, JSON.stringify(${JSON.stringify(ready)}));
    }}, 10);
  });`;
  w.ctx.jobs = {
    start(spec) { const job = startAgentJob({ ...spec, command: process.execPath, args: ['-e', script] }); jobs.push(job); return job; },
    read: readAgentJob, stop: stopAgentJob,
  };
  t.after(() => jobs.forEach(job => stopAgentJob(job)));
  assert.equal(await checkIssue(w.issue, w.ports()), null);
  fs.writeFileSync(release, 'continue');
  const deadline = Date.now() + 10000;
  let result = null;
  while (!result && Date.now() < deadline) {
    await new Promise(resolve => setTimeout(resolve, 25)); result = await checkIssue(w.issue, w.ports());
  }
  assert.deepEqual(result, ready); assert.equal(jobs.length, 1);
  assert.deepEqual(await checkIssue(w.issue, w.ports()), ready);
});


test('overlapping improvement and question calls post each marked comment once', async t => {
  const w = world(t, [ready]);
  await Promise.all([improveIssue(w.issue, improve, w.ports()), improveIssue(w.issue, improve, w.ports())]);
  assert.equal(comments(w).length, 1); assert.equal(w.started.length, 1);
  await Promise.all([askPerson(w.issue, ask, w.ports()), askPerson(w.issue, ask, w.ports())]);
  assert.equal(comments(w).length, 2);
  assert.equal(w.writes.filter(x => x[0] === 'label').length, 1);
});

for (const kind of ['improve', 'ask']) {
  test(`uncollected ${kind} output keeps its launch redaction context across rotation`, async t => {
    const canary = `opaque-${kind}-running-fixture-47021`;
    const output = kind === 'improve' ? { ...improve, acceptance: [`Print ${canary} safely.`] }
      : { ...ask, question: `Should ${canary} be accepted?` };
    const w = world(t, [output, ready]), readJob = w.ctx.jobs.read;
    w.ctx.env = { CUSTOM_TOKEN: canary };
    w.ctx.jobs.read = () => ({ state: 'running', exit: null, result: null });
    await intakeGate(w.ctx, [w.issue]);
    w.ctx.jobs.read = readJob;
    await intakeGate({ ...w.ctx, env: {} }, [w.issue]);
    assert.equal(comments(w).length, 1);
    assert.equal(comments(w)[0].includes(canary), false, 'launch credential must be redacted');
    assert.equal(comments(w)[0].includes('[redacted]'), true);
  });

  test(`restart without the launch credential refuses uncollected ${kind} output locally`, async t => {
    const canary = `opaque-${kind}-restart-fixture-47022`;
    const output = kind === 'improve' ? { ...improve, acceptance: [`Print ${canary} safely.`] }
      : { ...ask, question: `Should ${canary} be accepted?` };
    const w = world(t, [output]), readJob = w.ctx.jobs.read;
    w.ctx.env = { CUSTOM_TOKEN: canary };
    w.ctx.jobs.read = () => ({ state: 'running', exit: null, result: null });
    await intakeGate(w.ctx, [w.issue]);
    // Reload the owner module to discard all of its process-local context.
    const restarted = await import(`../src/autopilot-intake.mjs?restart-${kind}`);
    w.ctx.jobs.read = readJob;
    const result = await restarted.intakeGate({ ...w.ctx, env: {} }, [w.issue]);
    assert.deepEqual(result.ready, []);
    assert.equal(result.actions[0].type, 'error');
    assert.match(result.actions[0].error, /redaction context unavailable/);
    assert.deepEqual(w.writes, []);
    assert.equal(w.started.length, 1);
  });

  test(`restart with the same launch context safely collects pending ${kind} output`, async t => {
    const canary = `opaque-${kind}-same-context-fixture-47023`;
    const output = kind === 'improve' ? { ...improve, acceptance: [`Print ${canary} safely.`] }
      : { ...ask, question: `Should ${canary} be accepted?` };
    const w = world(t, [output, ready]), readJob = w.ctx.jobs.read;
    w.ctx.env = { CUSTOM_TOKEN: canary };
    w.ctx.jobs.read = () => ({ state: 'running', exit: null, result: null });
    await intakeGate(w.ctx, [w.issue]);
    const restarted = await import(`../src/autopilot-intake.mjs?same-context-${kind}`);
    w.ctx.jobs.read = readJob;
    const result = await restarted.intakeGate(w.ctx, [w.issue]);
    assert.equal(result.actions[0].type, kind);
    assert.equal(comments(w).length, 1);
    assert.equal(comments(w)[0].includes(canary), false);
    assert.equal(comments(w)[0].includes('[redacted]'), true);
    assert.equal(w.started.length, kind === 'improve' ? 2 : 1);
  });

  test(`child-only credential is redacted in ${kind} comments and cached results resumed after rotation`, async t => {
    const canary = `opaque-${kind}-fixture-47019`;
    assert.equal(Object.values(process.env).includes(canary), false);
    const output = kind === 'improve' ? { ...improve, acceptance: [`Print ${canary} safely.`] }
      : { ...ask, question: `Should ${canary} be accepted?` };
    const w = world(t, [output, ready]);
    w.ctx.env = { CUSTOM_TOKEN: canary };
    await intakeGate({ ...w.ctx, shadow: true }, [w.issue]);
    assert.equal(w.started[0].env.CUSTOM_TOKEN === canary, true, 'child receives the override');
    // New context, no old credential inventory: the saved result must already be safe.
    const resumed = { ...w.ctx, env: {} };
    await intakeGate(resumed, [w.issue]);
    assert.equal(comments(w).length, 1);
    assert.equal(comments(w)[0].includes(canary), false, 'cached result must not publish the credential');
    assert.equal(comments(w)[0].includes('[redacted]'), true);
  });

  test(`direct ${kind} comment retry redacts the effective child environment before saving`, async t => {
    const canary = `opaque-${kind}-retry-fixture-47020`;
    const w = world(t, [ready]), original = w.ctx.gh.all;
    w.ctx.env = { CUSTOM_TOKEN: canary };
    let fail = true;
    w.ctx.gh.all = async path => {
      if (fail && path.includes('/comments?')) { fail = false; throw Error('temporary read failure'); }
      return original(path);
    };
    const output = kind === 'improve' ? { ...improve, acceptance: [`Print ${canary} safely.`] }
      : { ...ask, question: `Should ${canary} be accepted?` };
    const operation = kind === 'improve' ? improveIssue : askPerson;
    await assert.rejects(operation(w.issue, output, w.ports()), /temporary read failure/);
    await operation(w.issue, output, { ...w.ports(), env: {} });
    assert.equal(comments(w).length, 1);
    assert.equal(comments(w)[0].includes(canary), false, 'saved write must already be redacted');
    assert.equal(comments(w)[0].includes('[redacted]'), true);
  });
}

test('editing a pending issue stops the superseded check before launching and never repeats old inputs', async t => {
  const w = world(t, [ready, ready]);
  w.ctx.jobs.read = () => ({ state: 'running', exit: null, result: null });
  const initial = clone(w.issue);
  assert.equal(await checkIssue(initial, w.ports()), null);
  const oldJob = w.started[0].id, start = w.ctx.jobs.start;
  w.ctx.jobs.start = spec => {
    assert.ok(w.writes.some(x => x[0] === 'stop' && x[1] === oldJob), 'obsolete job stopped before replacement');
    return start(spec);
  };
  w.issue.body = 'Use the revised requirement.';
  assert.equal(await checkIssue(w.issue, w.ports()), null);
  assert.equal(w.started.length, 2);
  w.advance(10001);
  await assert.rejects(checkIssue(w.issue, w.ports()), /timed out/);
  assert.deepEqual(w.writes.filter(x => x[0] === 'stop').map(x => x[1]), w.started.map(x => x.id));
  await assert.rejects(checkIssue(initial, w.ports()), /superseded/);
  assert.equal(w.started.length, 2);
});

for (const hold of [{ state: 'closed' }, { labels: ['pdd:working'] }, { assignees: ['contributor'] }]) {
  test(`pending check is stopped when issue becomes held: ${Object.keys(hold)[0]}`, async t => {
    const w = world(t, [ready]);
    w.ctx.jobs.read = () => ({ state: 'running', exit: null, result: null });
    const initial = clone(w.issue);
    assert.equal((await intakeGate(w.ctx, [w.issue])).actions[0].type, 'check');
    Object.assign(w.issue, hold);
    const result = await intakeGate({ ...w.ctx }, [w.issue]);
    assert.deepEqual(result.ready, []); assert.equal(result.actions[0].type, 'held');
    assert.deepEqual(w.writes, [['stop', w.started[0].id]]);
    w.advance(10001);
    await intakeGate(w.ctx, [w.issue]);
    await assert.rejects(checkIssue(initial, w.ports()), /held/);
    assert.equal(w.started.length, 1); assert.equal(w.writes.length, 1);
  });
}

test('repository sweep times out saved checks even when their issue disappears from candidates', async t => {
  const w = world(t, [ready]);
  w.ctx.jobs.read = () => ({ state: 'running', exit: null, result: null });
  await intakeGate(w.ctx, [w.issue]);
  w.advance(10001);
  assert.deepEqual(await intakeGate({ ...w.ctx }, []), { ready: [], actions: [] });
  assert.deepEqual(w.writes, [['stop', w.started[0].id]]);
  await assert.rejects(checkIssue(w.issue, w.ports()), /timed out/);
  assert.equal(w.started.length, 1);
});

test('a refused stop leaves the old handle retryable and prevents a replacement launch', async t => {
  const w = world(t, [ready, ready]);
  w.ctx.jobs.read = () => ({ state: 'running', exit: null, result: null });
  await checkIssue(w.issue, w.ports());
  w.issue.body = 'New requirement';
  w.ctx.jobs.stop = () => false;
  await assert.rejects(checkIssue(w.issue, w.ports()), /stop/);
  assert.equal(w.started.length, 1);
  w.ctx.jobs.stop = job => { w.writes.push(['stop', job.id]); return true; };
  assert.equal(await checkIssue(w.issue, w.ports()), null);
  assert.equal(w.started.length, 2);
});

test('a process already exited successfully can be collected after the deadline', async t => {
  const w = world(t, [ready]);
  const readJob = w.ctx.jobs.read;
  w.ctx.jobs.read = () => ({ state: 'running', exit: null, result: null });
  await checkIssue(w.issue, w.ports());
  w.advance(10001);
  w.ctx.jobs.read = readJob;
  assert.deepEqual(await checkIssue(w.issue, w.ports()), ready);
  assert.deepEqual(w.writes, []);
});

test('reading a cached initial check preserves its pending augmented check, which still times out', async t => {
  const w = world(t, [improve, ready]), readJob = w.ctx.jobs.read;
  w.ctx.jobs.read = job => w.started.length === 1 ? readJob(job) : { state: 'running', exit: null, result: null };
  assert.equal((await intakeGate(w.ctx, [w.issue])).actions.at(-1).type, 'check');
  assert.equal((await intakeGate(w.ctx, [w.issue])).actions.at(-1).type, 'check');
  assert.equal(w.started.length, 2); assert.equal(w.writes.filter(x => x[0] === 'stop').length, 0);
  w.advance(10001);
  await intakeGate(w.ctx, []);
  assert.deepEqual(w.writes.filter(x => x[0] === 'stop'), [['stop', w.started[1].id]]);
});

import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { createTryTools } from '../src/try-mcp.mjs';
import { runTry } from '../src/runtime-client.mjs';
import { createRunJudge } from '../src/agent-judge.mjs';
import { harbor, fakeRuntime, portsFor, PLACE } from './runtime-fake.mjs';

test('explicit try_id in pdd mcp never creates or reopens a missing, paused, stopped or cap-mismatched Try', async t => {
  const setup = harbor(t, root => rmSync(join(root, 'tests/unknown-item.json')));
  let modelStatus = 200, modelCap = 40, sessionState = 'running', reopenCalls = 0;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.url.endsWith('/reopen')) { reopenCalls++; return { status: 200, json: f.tryJob(entry.url.split('/').at(-2)) }; }
    if (entry.url.endsWith('/model')) {
      if (modelStatus !== 200) return { status: modelStatus, json: { error: { code: modelStatus === 409 ? 'session-stopped' : 'not-found', message: 'not running' } } };
      return { status: 200, json: { entries: [{ entry_path: PLACE, operation: 'placeOrder', cli: false, errors: ['unknown-item'], input_schema: { type: 'object' } }], calls: { cap: modelCap, remaining: modelCap } } };
    }
    if (entry.url.endsWith('/state')) return { status: 200, json: { world: { kv: {} }, actions: [] } };
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') {
      const job = f.tryJob(entry.request.requestId);
      job.max_calls = entry.request.max_calls;
      job.source_sha256 = entry.request.source_sha256;
      job.server_commit = '217f8d38036f5dfaa98f915bc1b9011805ac9ac6';
      job.result.session.max_calls = entry.request.max_calls;
      job.result.session.remaining_calls = entry.request.max_calls;
      return { status: 200, json: job };
    }
    const id = entry.url.split('/').at(-1);
    const job = f.tryJob(id);
    job.result.session.state = sessionState;
    job.result.session.max_calls = 40;
    job.result.session.remaining_calls = 40;
    return { status: 200, json: job };
  });

  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  const tools = createTryTools({ cwd: setup.repo }, ports);

  // 1. Before any Try exists, explicit try_id refuses without opening a Try.
  await assert.rejects(tools.call('try_open', { try_id: '99999999-9999-4999-8999-999999999999' }), /No open Try with ID/);
  assert.equal(fake.posts.filter(p => p.command === 'try').length, 0);

  // 2. Operator creates an explicit 40-call Try via pdd simulate.
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--max-calls': 40, '--no-open': true, '--no-wait': true } }, ports), 0);
  assert.equal(fake.posts.filter(p => p.command === 'try').length, 1);
  const tryId = fake.posts.find(p => p.command === 'try').request.requestId;

  // 3. Explicit try_id binds the running 40-call Try and reports pinned source_sha256 and cap 40.
  const opened = await tools.call('try_open', { try_id: tryId });
  assert.equal(opened.try_id, tryId);
  assert.equal(opened.calls.cap, 40);
  assert.equal(opened.calls.remaining, 40);
  assert.match(opened.source_sha256, /^[0-9a-f]{64}$/);
  assert.equal(opened.server_commit, '217f8d38036f5dfaa98f915bc1b9011805ac9ac6');
  assert.equal(fake.posts.filter(p => p.command === 'try').length, 1);

  // 4. Cap mismatch (e.g., 400 vs pinned 40) is refused without replacement.
  modelCap = 400;
  await assert.rejects(tools.call('try_state', { try_id: tryId }), /call cap 400 instead of pinned cap 40/);
  modelCap = 40;

  // 5. Paused session (409 session-stopped + state=paused) is refused when try_id is given: zero reopen, zero new Try.
  modelStatus = 409;
  sessionState = 'paused';
  await assert.rejects(tools.call('try_state', { try_id: tryId }), /not running.*session-stopped/);
  assert.equal(reopenCalls, 0);
  assert.equal(fake.posts.filter(p => p.command === 'try').length, 1);

  // 6. Stopped or expired session (409 stopped / 404 / 410) is also refused with zero new Try.
  sessionState = 'stopped';
  await assert.rejects(tools.call('try_open', { try_id: tryId }), /not running/);
  modelStatus = 404;
  await assert.rejects(tools.call('try_open', { try_id: tryId }), /not running/);
  modelStatus = 410;
  await assert.rejects(tools.call('try_open', { try_id: tryId }), /not running/);
  assert.equal(reopenCalls, 0);
  assert.equal(fake.posts.filter(p => p.command === 'try').length, 1);
});

test('pure JSON try_run with try_id returns normal results, structured declared errors, replay metadata and read-only try_observe without /v1/runs recovery', async t => {
  // Use Harbor's unknown-item Story (which already has an authored error-target check on unknown-item!).
  const setup = harbor(t, root => rmSync(join(root, 'tests/place-order.json')));
  const unknownDoc = JSON.parse(readFileSync(join(setup.repo, 'tests/unknown-item.json'), 'utf8'));
  const badStep = unknownDoc.steps[0];

  let tryId = null, sessionState = 'running', nextMode = 'normal';
  const runGetIds = [], observations = new Map(), callReceipts = new Map(), actions = [];

  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.url.endsWith('/model')) {
      return {
        status: 200,
        json: {
          entries: [{
            entry_path: badStep.entry_path,
            operation: badStep.operation,
            cli: false,
            errors: ['unknown-item'],
            input_schema: { type: 'object' },
          }],
          calls: { cap: 40, remaining: 38 },
        },
      };
    }
    if (entry.method === 'DELETE' && entry.url.startsWith('/v1/try/')) {
      sessionState = 'stopped';
      return { status: 200, json: f.job(entry.headers['x-request-id'], 'stop', 'passed') };
    }
    if (entry.url.endsWith('/state')) return { status: 200, json: { world: unknownDoc.initial_world ?? {}, actions } };
    if (entry.url.includes('/calls/') && entry.url.endsWith('/observation')) {
      const reqId = entry.url.split('/').at(-2);
      const saved = observations.get(reqId);
      if (!saved) return { status: 404, json: { error: { code: 'not-found', message: 'no such call' } } };
      return { status: 200, json: { ...saved, session_state: sessionState } };
    }
    if (entry.url.endsWith('/call') && entry.method === 'POST') {
      const reqId = entry.json.requestId;
      if (nextMode === 'unknown') {
        observations.set(reqId, {
          request_id: reqId,
          action_id: 'act-unknown-999',
          session_id: tryId,
          state: 'unknown',
          session_state: sessionState,
          source_sha256: 'src-sha-1',
          server_commit: 'srv-1',
          engine_sha: 'eng-1',
        });
        return { status: 202, json: { id: reqId, command: 'call', state: 'running' } };
      }
      const actionId = `act-${observations.size + 1}`;
      if (nextMode === 'normal' || nextMode === 'replay') {
        const replayed = nextMode === 'replay';
        observations.set(reqId, {
          request_id: reqId,
          action_id: actionId,
          session_id: tryId,
          state: 'passed',
          session_state: sessionState,
          source_sha256: 'src-sha-1',
          server_commit: 'srv-1',
          engine_sha: 'eng-1',
        });
        actions.push({ action_id: actionId, input_world: unknownDoc.initial_world ?? {}, world: unknownDoc.initial_world ?? {} });
        callReceipts.set(reqId, {
          requestId: reqId,
          id: reqId,
          command: 'call',
          session_id: tryId,
          state: 'passed',
          usage: { calls: replayed ? 0 : 1 },
          result: {
            program_result: { item: 'latte', totalCents: 900 },
            report: { action_id: actionId, verdict: 'passed', error: null, replayed, provider_calls: replayed ? 0 : 1, remaining_calls: replayed ? 38 : 39 },
          },
        });
        return { status: 200, json: callReceipts.get(reqId) };
      }
      if (nextMode === 'declared-error' || nextMode === 'undeclared-error') {
        const code = nextMode === 'declared-error' ? 'unknown-item' : 'database-down';
        observations.set(reqId, {
          request_id: reqId,
          action_id: actionId,
          session_id: tryId,
          state: 'failed',
          session_state: sessionState,
          source_sha256: 'src-sha-1',
          server_commit: 'srv-1',
          engine_sha: 'eng-1',
        });
        actions.push({ action_id: actionId, input_world: unknownDoc.initial_world ?? {}, world: unknownDoc.initial_world ?? {} });
        callReceipts.set(reqId, {
          requestId: reqId,
          id: reqId,
          command: 'call',
          session_id: tryId,
          state: 'failed',
          usage: { calls: 1 },
          result: {
            output: null,
            refusals: [{ code, message: `Refused: ${code}` }],
            report: { action_id: actionId, verdict: 'failed', error: { code }, replayed: false, provider_calls: 1, remaining_calls: 38 },
          },
        });
        return { status: 200, json: callReceipts.get(reqId) };
      }
    }
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') {
      tryId = entry.request.requestId;
      const job = f.tryJob(tryId);
      job.max_calls = entry.request.max_calls;
      job.result.session.max_calls = entry.request.max_calls;
      job.result.session.remaining_calls = entry.request.max_calls;
      return { status: 200, json: job };
    }
    const id = entry.url.split('/').at(-1);
    if (callReceipts.has(id)) {
      runGetIds.push(id);
      return { status: 200, json: callReceipts.get(id) };
    }
    if (observations.has(id)) {
      runGetIds.push(id);
    }
    return { status: 200, json: f.tryJob(id) };
  });

  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(await runTry({ cwd: setup.repo, words: ['unknown-item'], options: { '--max-calls': 40, '--no-open': true, '--no-wait': true } }, ports), 0);

  const tools = createTryTools({ cwd: setup.repo }, ports);
  const fullEntry = `${badStep.entry_path}#${badStep.operation}`;

  // 1. Normal pure JSON call
  nextMode = 'normal';
  const normal = await tools.call('try_run', {
    try_id: tryId,
    entry: fullEntry,
    input: { item: 'latte', quantity: 2 },
  });
  assert.deepEqual(normal.result, { item: 'latte', totalCents: 900 });
  assert.equal(normal.error, null);
  assert.equal(normal.replayed, false);
  assert.equal(normal.action_id, 'act-1');
  assert.notEqual(normal.run_id, normal.action_id);
  assert.deepEqual(normal.usage, { calls: 1, remaining: 39, cap: 40, used: 1 });

  // 2. Exact repeat surfaces replayed: true and 0 calls
  nextMode = 'replay';
  const repeated = await tools.call('try_run', {
    try_id: tryId,
    entry: fullEntry,
    input: { item: 'latte', quantity: 2 },
  });
  assert.equal(repeated.replayed, true);
  assert.deepEqual(repeated.usage, { calls: 0, remaining: 38, cap: 40, used: 2 });

  // 3. Declared domain refusal returns structured error (not MCP isError), judges error checks, and saves expected_error case
  nextMode = 'declared-error';
  const domainErr = await tools.call('try_run', {
    try_id: tryId,
    entry: fullEntry,
    input: badStep.input,
  });
  assert.equal(domainErr.result, null);
  assert.deepEqual(domainErr.error, { code: 'unknown-item' });
  assert.equal(domainErr.action_id, 'act-3');
  const checkedErr = await tools.call('try_check', { try_id: tryId, run_id: domainErr.run_id });
  assert.equal(checkedErr.verdict.state, 'pass');
  // Staging without a writeOwnership lease retains the case pending; applying with closed_editor_for commits it!
  let pendingId = null;
  await assert.rejects(async () => {
    await tools.call('try_save_case', { try_id: tryId, run_id: domainErr.run_id, criterion_id: unknownDoc.criteria[0].id });
  }, error => {
    const match = /\(pending ([0-9a-f]{64}\.[0-9a-f]{64})\)/.exec(error.message);
    assert.ok(match, `expected pending ID in ${error.message}`);
    pendingId = match[1];
    return true;
  });
  await assert.rejects(tools.call('try_save_case', { try_id: tryId, pending_id: pendingId, closed_editor_for: 'tests/unknown-item.json' }), /Pending application accepts only/);
  const appliedErr = await tools.call('try_save_case', { pending_id: pendingId, closed_editor_for: 'tests/unknown-item.json' });
  assert.match(appliedErr.result, /^added to tests\/unknown-item\.try-/);
  const savedDoc = JSON.parse(readFileSync(join(setup.repo, `tests/unknown-item.try-${domainErr.run_id}.json`), 'utf8'));
  assert.equal(savedDoc.steps[0].expected_error, 'unknown-item');
  assert.deepEqual(savedDoc.steps[0].checks[0], { criterion_id: unknownDoc.criteria[0].id, target: 'error', path: '/code', op: 'equals', value: 'unknown-item' });

  // 4. Undeclared refusal remains an error
  nextMode = 'undeclared-error';
  await assert.rejects(tools.call('try_run', {
    try_id: tryId,
    entry: fullEntry,
    input: { item: 'tea', quantity: -5 },
  }), /database-down/);

  // 5. Uncertain observation (state: "unknown") fails without calling GET /v1/runs/<id> and blocks later try_run calls
  const runGetsBeforeUnknown = runGetIds.length;
  nextMode = 'unknown';
  await assert.rejects(tools.call('try_run', {
    try_id: tryId,
    entry: fullEntry,
    input: { item: 'tea', quantity: 9 },
  }), /unknown/);
  assert.equal(runGetIds.length, runGetsBeforeUnknown, 'unknown observation must not trigger GET /v1/runs/<id> recovery');
  await assert.rejects(tools.call('try_run', {
    try_id: tryId,
    entry: fullEntry,
    input: { item: 'tea', quantity: 1 },
  }), /prior run has an unknown outcome/);

  // 6. Read-only try_observe works both while running and after session_state becomes "stopped", without /v1/runs/<id>
  const obsRunning = await tools.call('try_observe', { try_id: tryId, run_id: normal.run_id });
  assert.equal(obsRunning.run_id, normal.run_id);
  assert.equal(obsRunning.action_id, 'act-1');
  assert.equal(obsRunning.state, 'passed');
  assert.equal(obsRunning.session_state, 'running');
  assert.equal(obsRunning.terminal, true);
  assert.equal(obsRunning.unknown_outcome, false);

  // Path traversal or internal 32-hex action_id in run_id is rejected locally before network and never hits GET /v1/runs/<id>
  await assert.rejects(tools.call('try_observe', { try_id: tryId, run_id: `../../../runs/${normal.run_id}#` }), /Invalid external run UUID/);
  await assert.rejects(tools.call('try_observe', { try_id: tryId, run_id: '605cd2d9e23745f990720a7a5103490c' }), /Invalid external run UUID/);
  assert.equal(runGetIds.length, runGetsBeforeUnknown, 'invalid run_id must never hit GET /v1/runs/<id>');

  sessionState = 'stopped';
  const obsStopped = await tools.call('try_observe', { try_id: tryId, run_id: normal.run_id });
  assert.equal(obsStopped.session_state, 'stopped');
  assert.equal(obsStopped.state, 'passed');
  assert.equal(obsStopped.action_id, 'act-1');
  // 7. After explicit `pdd simulate --stop <TRY_ID>` deletes repo.tries, try_observe still works via calls/<runId>.meta.json while try_open refuses
  assert.equal(await runTry({ cwd: setup.repo, words: [tryId], options: { '--stop': true } }, ports), 0);
  const obsAfterStopCmd = await tools.call('try_observe', { try_id: tryId, run_id: normal.run_id });
  assert.equal(obsAfterStopCmd.session_state, 'stopped');
  assert.equal(obsAfterStopCmd.state, 'passed');
  assert.equal(obsAfterStopCmd.action_id, 'act-1');
  await assert.rejects(tools.call('try_observe', { try_id: tryId, story: 'place-order', run_id: normal.run_id }), /belongs to/);
  await assert.rejects(tools.call('try_open', { try_id: tryId }), /No open Try with ID/);
  assert.equal(runGetIds.length, runGetsBeforeUnknown, 'try_observe never calls GET /v1/runs/<id>');
  assert.equal(fake.posts.filter(p => p.command === 'try').length, 1, 'try_observe never opens a second Try');
});

test('pdd simulate --stop <TRY_ID> stops only the matching Try UUID and refuses unknown IDs before sign-in', async t => {
  const setup = harbor(t);
  const deleted = [];
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'DELETE' && entry.url.startsWith('/v1/try/')) {
      const id = entry.url.split('/').at(-1);
      deleted.push(id);
      return { status: 200, json: f.job(entry.headers['x-request-id'], 'stop', 'passed') };
    }
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') {
      const job = f.tryJob(entry.request.requestId);
      job.max_calls = entry.request.max_calls;
      job.result.session.max_calls = entry.request.max_calls;
      job.result.session.remaining_calls = entry.request.max_calls;
      return { status: 200, json: job };
    }
    return { status: 200, json: f.tryJob(entry.url.split('/').at(-1)) };
  });

  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--max-calls': 40, '--no-open': true, '--no-wait': true } }, ports), 0);
  assert.equal(await runTry({ cwd: setup.repo, words: ['unknown-item'], options: { '--max-calls': 40, '--no-open': true, '--no-wait': true } }, ports), 0);
  const [firstId, secondId] = fake.posts.filter(p => p.command === 'try').map(p => p.request.requestId);

  // Unknown Try UUID exits 2 before sign-in or network
  let ghCalled = false;
  const noAuthPorts = { ...ports, gh: () => { ghCalled = true; throw new Error('unexpected sign-in'); } };
  assert.equal(await runTry({ cwd: setup.repo, words: ['99999999-9999-4999-8999-999999999999'], options: { '--stop': true } }, noAuthPorts), 2);
  assert.equal(ghCalled, false);
  assert.equal(deleted.length, 0);

  // Stopping by exact firstId stops only firstId and leaves secondId intact
  const stopEnv = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(await runTry({ cwd: setup.repo, words: [firstId], options: { '--stop': true } }, stopEnv.ports), 0);
  assert.deepEqual(deleted, [firstId]);
  assert.match(stopEnv.ports.stdout.text, /is stopped\./);

  // Second Try remains recorded and can still be stopped by its own UUID
  const stopSecond = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(await runTry({ cwd: setup.repo, words: [secondId], options: { '--stop': true } }, stopSecond.ports), 0);
  assert.deepEqual(deleted, [firstId, secondId]);
});

test('agent-judge compares error checks cleanly without changing result or missing-observation rules', () => {
  const scenario = {
    criteria: [{ id: 'AC1', text: 'Declared refusal' }, { id: 'AC2', text: 'Normal' }],
    initial_world: {},
    steps: [
      { step_id: 'bad', entry_path: 'prompts/q.prompt.md', operation: 'quote', input: { qty: 0 }, expected_error: 'invalid-quantity', checks: [{ criterion_id: 'AC1', target: 'error', path: '/code', op: 'equals', value: 'invalid-quantity' }, { criterion_id: 'AC1', target: 'world', path: '', op: 'equals', value: {} }] },
      { step_id: 'ok', entry_path: 'prompts/q.prompt.md', operation: 'quote', input: { qty: 2 }, checks: [{ criterion_id: 'AC2', target: 'result', path: '/total', op: 'equals', value: 200 }] },
    ],
  };
  const judge = createRunJudge({ scenario });
  assert.equal(judge.record({ id: 'r1', entry: 'prompts/q.prompt.md#quote', input: { qty: 0 }, error: { code: 'invalid-quantity' }, world_before: {}, world_after: {}, lossless: true }).state, 'pass');
  assert.equal(judge.record({ id: 'r2', entry: 'prompts/q.prompt.md#quote', input: { qty: 0 }, result: { total: 0 }, error: null, world_before: {}, world_after: {}, lossless: true }).state, 'fail');
  assert.equal(judge.record({ id: 'r3', entry: 'prompts/q.prompt.md#quote', input: { qty: 2 }, error: { code: 'invalid-quantity' }, world_before: {}, world_after: {}, lossless: true }).state, 'fail');
  // Even when a run object carries both result: null and a non-null error object, whole-result null checks must fail with missing: true
  const nullResultScenario = {
    criteria: [{ id: 'ACN', text: 'Returns explicit null' }],
    initial_world: {},
    steps: [{ step_id: 's1', entry_path: 'prompts/q.prompt.md', operation: 'quote', input: { qty: 1 }, checks: [{ criterion_id: 'ACN', target: 'result', path: '', op: 'equals', value: null }] }],
  };
  const nullJudge = createRunJudge({ scenario: nullResultScenario });
  const errOnNullCheck = nullJudge.record({ id: 'rn1', entry: 'prompts/q.prompt.md#quote', input: { qty: 1 }, result: null, error: { code: 'invalid-quantity' }, world_before: {}, lossless: true });
  assert.equal(errOnNullCheck.state, 'fail');
  assert.equal(errOnNullCheck.first_difference?.missing, true);
});

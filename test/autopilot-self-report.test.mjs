import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import {
  SELF_REPORT_REPO,
  FORBIDDEN_RUNTIME_REPO,
  DAILY_SELF_REPORT_CAP,
  CONSENT_PROMPT,
  classifyFailureCause,
  classifyRuntimeFailure,
  redactSelfReport,
  selfReportConsent,
  resolveSelfReportConsent,
  diagnosePddFailure,
  formatSelfReportBody,
  fileSelfReport,
  recordCommandCrash,
  reconcileSelfReports,
} from '../src/autopilot-self-report.mjs';
import { captureCosts, costReport, costStatusLines } from '../src/cost-ledger.mjs';
import { parkingSummary, parkingWords, wakeCondition } from '../src/autopilot-parking.mjs';

test('cause classification table separates PDD/Autopilot, Runtime service, user code and person decisions', () => {
  const table = [
    // 1. PDD/Autopilot side (reportable: true, side: 'pdd')
    {
      name: 'pdd command crash from saved commandFailure',
      run: {
        state: 'stuck',
        commandFailure: {
          code: 'TypeError',
          module: 'src/workflow-runner.mjs',
          fn: 'stepDoneCommand',
          line: 3120,
          message: "Cannot read properties of null (reading 'verify')",
          stack: "TypeError: Cannot read properties of null (reading 'verify')\n    at stepDoneCommand (src/workflow-runner.mjs:3120:15)",
        },
      },
      expect: { side: 'pdd', kind: 'command-crash', reportable: true, module: 'src/workflow-runner.mjs', fn: 'stepDoneCommand' },
    },
    {
      name: 'pdd internal error in parkReason stack',
      run: {
        state: 'stuck',
        parkReason: 'pdd stopped with an internal error. Reason: ReferenceError: broken is not defined at reconcileParking (src/autopilot-parking.mjs:148:7)',
      },
      expect: { side: 'pdd', kind: 'command-crash', reportable: true, module: 'src/autopilot-parking.mjs', fn: 'reconcileParking' },
    },
    {
      name: 'contract or state invariant broken',
      run: {
        state: 'stuck',
        invariantFailure: {
          code: 'ERR_STATE_INVARIANT',
          module: 'src/workflow-runs.mjs',
          fn: 'updateRun',
          message: 'Status record area index is out of bounds',
        },
      },
      expect: { side: 'pdd', kind: 'invariant-broken', reportable: true, module: 'src/workflow-runs.mjs', fn: 'updateRun' },
    },
    {
      name: 'supported command missing or wrong',
      run: {
        state: 'stuck',
        parkReason: 'Unsupported command in pdd: workflow verify-Check',
      },
      expect: { side: 'pdd', kind: 'missing-command', reportable: true },
    },
    {
      name: 'Autopilot state bug in claims, parking, wake or admission',
      run: {
        state: 'stuck',
        autopilotBug: {
          Subsystem: 'parking',
          code: 'ERR_PARKING_STATE',
          module: 'src/autopilot-parking.mjs',
          fn: 'reconcileParking',
          message: 'Parked run lost its blocker record during wake transition',
        },
      },
      expect: { side: 'pdd', kind: 'autopilot-state', reportable: true, module: 'src/autopilot-parking.mjs', fn: 'reconcileParking' },
    },

    // 2. Runtime service side (reportable: true, side: 'runtime')
    {
      name: 'Runtime no-verdict batch',
      run: {
        state: 'paused',
        runtimeWait: { at: 1000, batch: '20261110-010000-abcd', reason: 'Interpreter batch 20261110-010000-abcd: no-verdict.', cause: 'service' },
      },
      expect: { side: 'runtime', kind: 'no-verdict', reportable: true },
    },
    {
      name: 'Runtime runner-stopped',
      run: {
        state: 'paused',
        runtimeWait: { at: 1000, batch: '20261110-010000-efgh', reason: 'Interpreter batch 20261110-010000-efgh: runner-stopped.', cause: 'unknown' },
      },
      expect: { side: 'runtime', kind: 'runner-stopped', reportable: true },
    },
    {
      name: 'Runtime provider error',
      run: { state: 'waiting', gate: { kind: 'approve-pr', area: 'prompt' }, done: { check: { summary: 'done' } } },
      check: {
        batch: '20261110-010000-prov',
        states: [{ state: 'service-unavailable', reason: { code: 'provider-error', message: 'Upstream model 503 overloaded' } }],
      },
      expect: { side: 'runtime', kind: 'provider-error', reportable: true },
    },
    {
      name: 'Runtime server refusal not the prompt fault',
      run: { state: 'waiting', gate: { kind: 'approve-pr', area: 'prompt' }, done: { check: { summary: 'done' } } },
      check: {
        batch: '20261110-010000-ref',
        states: [{ state: 'refused', reason: { code: 'runtime-internal-refusal', message: 'Runtime sandbox worker refused container init' } }],
      },
      expect: { side: 'runtime', kind: 'server-refusal', reportable: true },
    },

    // 3. User code or tests (reportable: false, side: 'user')
    {
      name: 'User prompt test expectation failed',
      run: { state: 'waiting', gate: { kind: 'approve-pr', area: 'prompt' }, done: { check: { summary: 'done' } } },
      check: {
        batch: '20261110-010000-user',
        states: [{ state: 'failed', reason: { code: 'assertion-failed', message: 'Expected /value to equal 2, got 1' } }],
      },
      expect: { side: 'user', kind: 'expectation-failed', reportable: false },
    },
    {
      name: 'User missing binding in prompt check',
      run: { state: 'waiting', gate: { kind: 'approve-pr', area: 'prompt' }, done: { check: { summary: 'done' } } },
      check: {
        batch: '20261110-010000-bind',
        states: [{ state: 'refused', reason: { code: 'binding-missing', message: 'Missing binding for operation value' } }],
      },
      expect: { side: 'user', kind: 'binding-missing', reportable: false },
    },
    {
      name: 'User test suite failure',
      run: {
        state: 'stuck',
        stuckCause: 'suite',
        parkReason: 'npm test failed in test/user-feature.test.mjs: AssertionError: expected 42 to equal 43',
      },
      expect: { side: 'user', kind: 'suite', reportable: false },
    },

    {
      name: 'provider call cap is an account limit',
      run: { state: 'waiting', gate: { kind: 'approve-pr' } },
      check: { states: [{ state: 'refused', reason: { code: 'provider-call-cap', message: 'Provider call cap reached' } }] },
      expect: { side: 'person', kind: 'account', reportable: false },
    },
    {
      name: 'call cap reached is an account limit',
      run: { state: 'waiting' },
      check: { states: [{ state: 'refused', reason: { code: 'call-cap-reached' } }] },
      expect: { side: 'person', kind: 'account', reportable: false },
    },
    {
      name: 'HTTP 429 is an account limit',
      run: { state: 'waiting' },
      check: { states: [{ state: 'refused', reason: { code: 'provider-error', message: 'HTTP 429: quota exceeded' } }] },
      expect: { side: 'person', kind: 'account', reportable: false },
    },

    // 4. Person decision (reportable: false, side: 'person')
    {
      name: 'Open person question',
      run: {
        state: 'waiting',
        question: { text: 'Should empty strings be rejected or trimmed?', at: 1000, area: 'prompt' },
      },
      expect: { side: 'person', kind: 'question', reportable: false },
    },
    {
      name: 'Story or code approval gate waiting for person',
      run: {
        state: 'waiting',
        gate: { id: 'gate-1', area: 'story', kind: 'approve-story', at: 1000 },
      },
      expect: { side: 'person', kind: 'gate', reportable: false },
    },
  ];

  for (const row of table) {
    const actual = classifyFailureCause(row.run, { check: row.check });
    assert.equal(actual.side, row.expect.side, `${row.name}: side`);
    assert.equal(actual.kind, row.expect.kind, `${row.name}: kind`);
    assert.equal(actual.reportable, row.expect.reportable, `${row.name}: reportable`);
    if (row.expect.module) assert.equal(actual.module, row.expect.module, `${row.name}: module`);
    if (row.expect.fn) assert.equal(actual.fn, row.expect.fn, `${row.name}: fn`);
    if (actual.reportable) assert.match(actual.signature, /^[^:]+:[^:]+:[^:]+$/, `${row.name}: signature format`);
  }

  assert.equal(classifyRuntimeFailure({ states: [{ state: 'passed' }] }), null);
});

test('diagnose subagent runs one read-only session with the brief and formats docs/ISSUES.md sections', async t => {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-self-report-diag-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));

  const run = {
    runId: 'run-17',
    number: 17,
    repo: 'promptdriven/pdd',
    agent: 'claude',
    launchProfile: { agent: 'codex', configDir: '/saved/codex-account', model: 'saved-model' },
    agentDefinition: { kind: 'claude', name: 'wrong-agent', command: 'wrong-agent' },
    state: 'stuck',
    area: 0,
    areas: [{ name: 'code', steps: ['change', 'verify'] }],
    done: { change: { summary: 'Changed files' } },
    root,
    runDir: root,
    commandFailure: {
      command: 'workflow-done',
      code: 'TypeError',
      module: 'src/workflow-runner.mjs',
      fn: 'stepDoneCommand',
      line: 3120,
      fileLine: 'src/workflow-runner.mjs:3120',
      message: "Cannot read properties of null (reading 'verify')",
      stack: "TypeError: Cannot read properties of null (reading 'verify')\n    at stepDoneCommand (src/workflow-runner.mjs:3120:15)",
    },
  };
  const cause = classifyFailureCause(run);
  assert.equal(cause.side, 'pdd');

  const execCalls = [];
  const report = await diagnosePddFailure(run, cause, {
    home: '/home/alice',
    env: { HOME: '/home/alice', GITHUB_TOKEN: 'ghp_superSecretTokenValue123456', CODEX_HOME: '/decoy/codex', CLAUDE_CONFIG_DIR: '/decoy/claude', CLAUDECODE: 'parent', CLAUDE_CODE_SESSION_ID: 'parent', CODEX_THREAD_ID: 'parent', HERDR_SESSION: 'parent', PDD_AGENT_SESSION: 'parent', PDD_AUTOPILOT_CONTEXT: 'parent' },
    agentDefinitions: async () => [{ kind: 'codex', name: 'saved', env: { CODEX_HOME: '/profile/decoy', CODEX_THREAD_ID: 'profile', HERDR_PROFILE: 'profile', PDD_AUTOPILOT_CONTEXT: 'profile' } }],
    execute: async (file, args, options) => {
      execCalls.push({ file, args, options });
      const sessionId = '11111111-2222-7333-8444-555555555555';
      const payload = {
        title: 'PDD command-crash: TypeError in src/workflow-runner.mjs (stepDoneCommand)',
        problem: 'PRIVATE_SOURCE_MARKER and RESPONSE_PROSE_MARKER from the diagnosis output.',
        steps: ['PRIVATE_STEP_SOURCE_MARKER', 'PRIVATE_BATCH_20301231_MARKER'],
        expected: 'pdd workflow done initializes or validates run.done without throwing an uncaught TypeError.',
        actual: 'PRIVATE_RUN_ID_9a6c-marker and PRIVATE_RESPONSE_MARKER.',
        evidence: 'PRIVATE_USER_SOURCE_MARKER PRIVATE_RESPONSE_MARKER PRIVATE_BATCH_20301231_MARKER',
        rootCause: {
          module: 'src/autopilot-self-report.mjs',
          fn: 'safePublicReport',
          line: 50,
          fileLine: 'src/autopilot-self-report.mjs:50',
          explanation: 'PRIVATE_ROOT_CAUSE_PROSE_MARKER',
        },
        signature: 'TypeError:src/workflow-runner.mjs:stepDoneCommand',
      };
      return {
        code: 0,
        stdout: [
          JSON.stringify({ type: 'thread.started', thread_id: sessionId }),
          JSON.stringify({ type: 'item.completed', item: { type: 'agent_message', text: JSON.stringify(payload) } }),
        ].join('\n'),
        stderr: '',
      };
    },
  });

  assert.equal(execCalls.length, 1, 'must start exactly one diagnose subagent session');
  assert.equal(execCalls[0].file, 'codex');
  assert.ok(execCalls[0].args.includes('read-only'), 'subagent session must be read-only');
  assert.match(execCalls[0].options.input, /# Autopilot PDD Self-Report Diagnose Brief/);
  assert.equal(report.signature, 'TypeError:src/workflow-runner.mjs:stepDoneCommand');
  assert.equal(report.fileLine, null, 'a diagnosis location must belong to the failing function');
  assert.equal(report.diagnosisLocation, null);
  assert.match(report.body, /no source location was verified/);
  assert.equal(report.session.agent, 'codex', 'saved launch profile selects the diagnose agent');
  assert.equal(report.session.configDir, '/saved/codex-account', 'saved account is recorded');
  assert.equal(execCalls[0].options.env.CODEX_HOME, '/saved/codex-account');
  for (const marker of ['CLAUDECODE', 'CLAUDE_CODE_SESSION_ID', 'CODEX_THREAD_ID', 'HERDR_SESSION', 'HERDR_PROFILE', 'PDD_AGENT_SESSION', 'PDD_AUTOPILOT_CONTEXT']) {
    assert.equal(Object.hasOwn(execCalls[0].options.env, marker), false, marker + ' must be removed after env sources merge');
  }
  assert.equal(execCalls[0].options.env.CLAUDE_CONFIG_DIR, '/decoy/claude', 'the saved Codex profile does not rewrite another agent account');
  const savedChat = JSON.parse(fs.readFileSync(join(root, 'self-reports', fs.readdirSync(join(root, 'self-reports'))[0]), 'utf8')).chat;
  assert.equal(savedChat.agent, 'codex');
  assert.equal(savedChat.configDir, '/saved/codex-account');
  assert.equal(report.session.id, '11111111-2222-7333-8444-555555555555');
  assert.match(report.body, /## Problem/);
  assert.match(report.body, /## Steps to reproduce/);
  assert.match(report.body, /## Expected vs\. actual/);
  assert.match(report.body, /## Evidence/);
  assert.match(report.body, /## Versions/);
  assert.match(report.body, /## Suspected root cause/);
  assert.match(report.body, /<!-- pdd:self-report:TypeError:src\/workflow-runner\.mjs:stepDoneCommand -->/);
  // The public report uses structured local facts and excludes every free-form diagnosis field.
  for (const privateValue of ['PRIVATE_SOURCE_MARKER', 'PRIVATE_STEP_SOURCE_MARKER', 'PRIVATE_RUN_ID_9a6c-marker', 'PRIVATE_BATCH_20301231_MARKER', 'PRIVATE_RESPONSE_MARKER', 'PRIVATE_ROOT_CAUSE_PROSE_MARKER', 'run-17', '/home/alice']) {
    assert.ok(!report.body.includes(privateValue), 'public report must omit ' + privateValue);
  }
});


test('diagnosis keeps a location only when it belongs to the classified function', async t => {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-self-report-owned-location-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const source = fs.readFileSync(new URL('../src/autopilot-self-report.mjs', import.meta.url), 'utf8');
  const line = source.split('\n').findIndex(value => value.includes("const code = cause.code || 'ERR_PDD_CRASH'")) + 1;
  assert.ok(line > 0);
  const run = { runId: 'owned-location', root, runDir: root, launchProfile: { agent: 'codex', configDir: null, model: null } };
  const cause = {
    side: 'pdd', kind: 'command-crash', code: 'TypeError',
    module: 'src/autopilot-self-report.mjs', fn: 'diagnosePddFailure', line,
    evidence: 'at diagnosePddFailure (src/autopilot-self-report.mjs:' + line + ':1)',
  };
  const signature = 'TypeError:src/autopilot-self-report.mjs:diagnosePddFailure';
  const report = await diagnosePddFailure(run, cause, {
    home: root,
    env: { HOME: root },
    execute: async () => ({
      code: 0,
      stdout: [
        JSON.stringify({ type: 'thread.started', thread_id: '11111111-2222-7333-8444-555555555555' }),
        JSON.stringify({ type: 'item.completed', item: { type: 'agent_message', text: JSON.stringify({
          signature,
          rootCause: { module: cause.module, fn: cause.fn, line },
        }) } }),
      ].join('\n'),
    }),
  });
  assert.deepEqual(report.diagnosisLocation, { module: cause.module, fn: cause.fn, line });
  assert.equal(report.fileLine, cause.module + ':' + line);
});

test('dedupe adds one comment on open issue, cap limits new issues to 5 per machine per day, and PDD target is guarded', async t => {
  const stateRoot = fs.mkdtempSync(join(tmpdir(), 'pdd-self-report-cap-'));
  t.after(() => fs.rmSync(stateRoot, { recursive: true, force: true }));

  const now = Date.parse('2026-11-10T12:00:00Z');
  const openIssues = [];
  const comments = [];
  const created = [];

  const ports = {
    stateRoot,
    now: () => now,
    searchIssues: async () => openIssues,
    createIssue: async input => {
      const issue = { number: 600 + created.length + 1, url: `https://github.com/${input.repo}/issues/${600 + created.length + 1}`, state: 'open', ...input };
      created.push(issue);
      openIssues.push(issue);
      return issue;
    },
    commentIssue: async input => {
      comments.push(input);
    },
  };

  // Refuses to file in promptdriven/prompt-runtime or a user repo:
  await assert.rejects(
    fileSelfReport({ targetRepo: FORBIDDEN_RUNTIME_REPO, repo: 'promptdriven/pdd' }, ports),
    /PDD self-reports must target promptdriven\/pdd/
  );
  await assert.rejects(
    fileSelfReport({ targetRepo: 'acme/private-app', repo: 'acme/private-app', config: { selfReport: 'auto' } }, ports),
    /target must be/
  );

  const state = {};
  const occurrenceRun = { runId: 'cost-run', repo: 'acme/app', selfReports: [] };
  const config = { selfReport: 'auto', maintainer: 'core-maintainer' };

  // First occurrence of signature-1 files a new issue in promptdriven/pdd:
  const first = await fileSelfReport({
    side: 'pdd',
    kind: 'command-crash',
    code: 'ERR_1',
    module: 'src/workflow-runner.mjs',
    fn: 'fn1',
    repo: 'acme/app',
    state,
    config,
    run: occurrenceRun,
  }, ports);
  assert.equal(first.action, 'filed');
  assert.equal(first.targetRepo, SELF_REPORT_REPO);
  assert.equal(first.issue.number, 601);
  assert.deepEqual(first.labels, ['pdd:self-report']);
  assert.equal(first.assignee, 'core-maintainer');
  assert.equal(created.length, 1);
  assert.equal(comments.length, 0);

  // Second occurrence of the SAME open signature-1 adds ONE comment and creates NO new issue:
  const dup = await fileSelfReport({
    side: 'pdd',
    kind: 'command-crash',
    code: 'ERR_1',
    module: 'src/workflow-runner.mjs',
    fn: 'fn1',
    repo: 'acme/app',
    state,
    config,
    run: occurrenceRun,
  }, ports);
  assert.equal(dup.action, 'commented');
  assert.equal(dup.issue.number, 601);
  assert.equal(created.length, 1, 'dedupe must not file a second issue');
  assert.equal(comments.length, 1, 'dedupe must add one comment');
  const outcomeCost = captureCosts(null, occurrenceRun, { now: () => now });
  assert.deepEqual(outcomeCost.selfReports, { filed: 1, commented: 1, skipped: 0 }, 'file and comment remain separate cost outcomes');
  assert.match(comments[0].body, /New occurrence of ERR_1:src\/workflow-runner\.mjs:fn1/);

  // File 4 more distinct signatures (2..5) to reach the daily cap of 5:
  for (let i = 2; i <= DAILY_SELF_REPORT_CAP; i++) {
    const res = await fileSelfReport({
      side: i === 2 ? 'runtime' : 'pdd',
      cause: i === 2 ? 'no-verdict' : undefined,
      code: `ERR_${i}`,
      module: 'src/workflow-runner.mjs',
      fn: `fn${i}`,
      repo: 'acme/app',
      state,
      config: i === 2 ? { selfReport: 'auto' } : config, // unassigned when maintainer is absent
    }, ports);
    assert.equal(res.action, 'filed');
    if (i === 2) {
      assert.deepEqual(res.labels, ['pdd:self-report', 'pdd:runtime-report']);
      assert.equal(res.assignee, null);
    }
  }
  assert.equal(created.length, 5, '5 new issues allowed per machine per day');

  // 6th new distinct signature on the same machine & day hits the cap and only comments:
  const sixth = await fileSelfReport({
    side: 'pdd',
    code: 'ERR_6',
    module: 'src/workflow-runner.mjs',
    fn: 'fn6',
    repo: 'acme/app',
    state,
    config,
  }, ports);
  assert.equal(sixth.action, 'commented');
  assert.equal(sixth.capped, true);
  assert.equal(created.length, 5, 'cap must prevent a 6th new issue on the same day');
  assert.equal(comments.length, 2, '6th occurrence must comment instead');
  assert.deepEqual(state.selfReports, { filed: 5, commented: 2, skipped: 0 });
});



test('missing repo context asks for consent and stops before issue reads or writes', async () => {
  const asked = [], calls = [];
  const state = {};
  const result = await fileSelfReport({
    code: 'ERR_NO_REPO', module: 'src/workflow-runner.mjs', fn: 'runPdd',
    state, config: {},
  }, {
    askConsent: async prompt => { asked.push(prompt); return 'off'; },
    searchIssues: async () => { calls.push('search'); return []; },
    createIssue: async () => { calls.push('create'); return { number: 1 }; },
  });
  assert.deepEqual(asked, [CONSENT_PROMPT]);
  assert.equal(result.action, 'skipped');
  assert.equal(result.reason, 'consent-declined');
  assert.deepEqual(calls, []);
  assert.equal(state.selfReports.skipped, 1);
});

test('a lost create response keeps a reserved cap slot and retry reconciles the issue as filed', async t => {
  const stateRoot = fs.mkdtempSync(join(tmpdir(), 'pdd-self-report-reservation-'));
  t.after(() => fs.rmSync(stateRoot, { recursive: true, force: true }));
  const now = Date.parse('2026-11-10T12:00:00Z');
  const issues = [], comments = [];
  let creates = 0;
  const run = { runId: 'uncertain-create', repo: 'promptdriven/pdd', selfReports: [] };
  const state = { repo: 'promptdriven/pdd' };
  const input = {
    code: 'ERR_UNCERTAIN', module: 'src/workflow-runner.mjs', fn: 'runPdd',
    run, state, config: { selfReport: 'auto' },
  };
  const ports = {
    stateRoot, now: () => now,
    searchIssues: async () => issues,
    createIssue: async value => {
      creates++;
      issues.push({ number: 701, url: 'https://github.com/promptdriven/pdd/issues/701', state: 'open', body: value.body });
      throw Error('synthetic lost create response');
    },
    commentIssue: async value => comments.push(value),
  };
  await assert.rejects(fileSelfReport(input, ports), /synthetic lost create response/);
  let cap = JSON.parse(fs.readFileSync(join(stateRoot, 'self-report-machine.json'), 'utf8'));
  assert.equal(cap.days['2026-11-10'].length, 1);
  assert.equal(cap.days['2026-11-10'][0].status, 'reserved');
  const retry = await fileSelfReport(input, ports);
  assert.equal(retry.action, 'filed');
  assert.equal(retry.issue.number, 701);
  assert.equal(creates, 1, 'retry must find the uncertain create before attempting another create');
  assert.deepEqual(comments, [], 'reconciliation must not report a new occurrence as a comment');
  assert.equal(state.selfReports.filed, 1);
  assert.equal(state.selfReports.commented, 0);
  cap = JSON.parse(fs.readFileSync(join(stateRoot, 'self-report-machine.json'), 'utf8'));
  assert.equal(cap.days['2026-11-10'][0].status, 'filed');
  assert.equal(cap.days['2026-11-10'][0].issue.number, 701);
});

test('legacy plus signatures still dedupe and missing comment writer does not claim success', async t => {
  const stateRoot = fs.mkdtempSync(join(tmpdir(), 'pdd-self-report-legacy-marker-'));
  t.after(() => fs.rmSync(stateRoot, { recursive: true, force: true }));
  const state = { repo: 'promptdriven/pdd' };
  const oldIssue = {
    number: 702, state: 'open',
    body: '<!-- pdd:self-report:ERR_LEGACY+src/workflow-runner.mjs+legacyFn -->',
  };
  const comments = [];
  const ports = {
    stateRoot,
    searchIssues: async () => [oldIssue],
    commentIssue: async value => comments.push(value),
  };
  const legacy = await fileSelfReport({
    code: 'ERR_LEGACY', module: 'src/workflow-runner.mjs', fn: 'legacyFn',
    repo: 'promptdriven/pdd', state, config: { selfReport: 'auto' },
  }, ports);
  assert.equal(legacy.action, 'commented');
  assert.equal(comments.length, 1);
  assert.match(comments[0].body, /ERR_LEGACY:src\/workflow-runner\.mjs:legacyFn/);

  const noWriterState = { repo: 'promptdriven/pdd' };
  const report = { code: 'ERR_COMMENT', module: 'src/workflow-runner.mjs', fn: 'commentFn' };
  const marker = '<!-- pdd:self-report:ERR_COMMENT:src/workflow-runner.mjs:commentFn -->';
  await assert.rejects(fileSelfReport({
    ...report, repo: 'promptdriven/pdd', state: noWriterState, config: { selfReport: 'auto' },
  }, {
    stateRoot,
    searchIssues: async () => [{ number: 703, state: 'open', body: marker }],
  }), /No GitHub comment writer/);
  assert.deepEqual(noWriterState.selfReports, { filed: 0, commented: 0, skipped: 0 });
});

test('Runtime target follows private write permission and public reports omit run, batch and free-form text', async t => {
  const stateRoot = fs.mkdtempSync(join(tmpdir(), 'pdd-self-report-target-'));
  t.after(() => fs.rmSync(stateRoot, { recursive: true, force: true }));
  const now = Date.parse('2026-11-10T12:00:00Z');
  const issues = new Map();
  const comments = [];
  const created = [];
  const ports = permission => ({
    stateRoot,
    now: () => now,
    repoPermission: async repo => {
      assert.equal(repo, FORBIDDEN_RUNTIME_REPO);
      return permission;
    },
    searchIssues: async (_marker, { targetRepo }) => issues.get(targetRepo) ?? [],
    createIssue: async input => {
      const issue = { number: 71 + created.length, url: 'https://github.com/' + input.repo + '/issues/' + (71 + created.length), state: 'open', body: input.body };
      created.push({ ...input, issue });
      issues.set(input.repo, [...(issues.get(input.repo) ?? []), { ...issue, ...input }]);
      return issue;
    },
    commentIssue: async input => comments.push(input),
  });
  const unsafe = {
    side: 'runtime',
    cause: 'no-verdict',
    code: 'RUNTIME_NO_VERDICT',
    module: 'runtime-service',
    fn: 'pdd-test',
    targetRepo: FORBIDDEN_RUNTIME_REPO,
    batch: 'PRIVATE_BATCH_20301231_MARKER',
    summary: 'PRIVATE_SUMMARY_MARKER',
    problem: 'PRIVATE_SOURCE_MARKER',
    evidence: 'PRIVATE_RESPONSE_MARKER',
    body: '<!-- pdd:self-report:RUNTIME_NO_VERDICT+runtime-service+pdd-test -->' + String.fromCharCode(10) + 'PRIVATE_BODY_MARKER',
    run: { runId: 'PRIVATE_RUN_ID_9a6c-marker', number: 99 },
    repo: 'promptdriven/pdd',
    config: { selfReport: 'auto' },
  };

  const fallback = await fileSelfReport(unsafe, ports('READ'));
  assert.equal(fallback.targetRepo, SELF_REPORT_REPO);
  assert.deepEqual(created[0].labels, ['pdd:self-report', 'pdd:runtime-report']);
  for (const privateValue of ['PRIVATE_BATCH_20301231_MARKER', 'PRIVATE_SUMMARY_MARKER', 'PRIVATE_SOURCE_MARKER', 'PRIVATE_RESPONSE_MARKER', 'PRIVATE_BODY_MARKER', 'PRIVATE_RUN_ID_9a6c-marker']) {
    assert.ok(!created[0].body.includes(privateValue), 'issue body must omit ' + privateValue);
  }

  await fileSelfReport(unsafe, ports('READ'));
  assert.equal(comments.length, 1);
  for (const privateValue of ['PRIVATE_BATCH_20301231_MARKER', 'PRIVATE_RUN_ID_9a6c-marker', 'PRIVATE_SUMMARY_MARKER']) {
    assert.ok(!comments[0].body.includes(privateValue), 'comment must omit ' + privateValue);
  }

  const privateReport = await fileSelfReport({ ...unsafe, targetRepo: undefined }, ports('WRITE'));
  assert.equal(privateReport.targetRepo, FORBIDDEN_RUNTIME_REPO);
  assert.equal(created[1].repo, FORBIDDEN_RUNTIME_REPO);
  assert.deepEqual(created[1].labels, [], 'private Runtime does not assume PDD labels exist');

  const accessReads = [];
  const defaultPortReport = await fileSelfReport({ ...unsafe, targetRepo: undefined }, {
    now: () => now,
    execute: async (file, args, options) => {
      accessReads.push({ file, args, options });
      return { code: 0, stdout: JSON.stringify({ viewerPermission: 'MAINTAIN' }) };
    },
    searchIssues: async () => [],
    createIssue: async input => ({ number: 99, url: 'https://github.com/' + input.repo + '/issues/99' }),
  });
  assert.equal(defaultPortReport.targetRepo, FORBIDDEN_RUNTIME_REPO);
  assert.equal(accessReads.length, 1);
  assert.deepEqual(accessReads[0].args, ['repo', 'view', FORBIDDEN_RUNTIME_REPO, '--json', 'viewerPermission']);
  assert.equal(accessReads[0].options.purpose, 'self-report-access');
});

test('filing retries reuse the saved diagnosis twice and attach its actual session to run cost', async t => {
  const at = Date.parse('2026-11-10T12:00:00Z');
  const sessionId = '11111111-2222-7333-8444-555555555555';
  const home = fs.mkdtempSync(join(tmpdir(), 'pdd-self-report-cost-'));
  t.after(() => fs.rmSync(home, { recursive: true, force: true }));
  const sessionDate = new Date(at);
  const savedConfigDir = join(home, 'saved-codex-account');
  const sessionDir = join(savedConfigDir, 'sessions', String(sessionDate.getUTCFullYear()), String(sessionDate.getUTCMonth() + 1).padStart(2, '0'), String(sessionDate.getUTCDate()).padStart(2, '0'));
  fs.mkdirSync(sessionDir, { recursive: true });
  fs.writeFileSync(join(sessionDir, 'rollout-test-' + sessionId + '.jsonl'), JSON.stringify({
    type: 'event_msg',
    payload: { type: 'token_count', info: { total_token_usage: { input_tokens: 123, cached_input_tokens: 0, output_tokens: 45, reasoning_output_tokens: 0, total_tokens: 168 } } },
  }) + String.fromCharCode(10));
  const run = {
    runId: 'run-private-1',
    number: 71,
    repo: 'promptdriven/pdd',
    agent: 'claude',
    launchProfile: { agent: 'codex', configDir: savedConfigDir, model: null },
    state: 'stuck',
    root: '/tmp',
    commandFailure: {
      code: 'TypeError',
      module: 'src/workflow-runner.mjs',
      fn: 'stepDoneCommand',
      stack: 'TypeError: fail' + String.fromCharCode(10) + '    at stepDoneCommand (src/workflow-runner.mjs:3120:15)',
    },
  };
  const state = { repo: 'promptdriven/pdd' };
  let diagnosisCalls = 0, searchCalls = 0;
  const ports = {
    now: () => at,
    readCheck: async () => null,
    diagnose: async () => {
      diagnosisCalls++;
      return { session: { id: sessionId }, diagnosis: { problem: 'PRIVATE_DIAGNOSIS_PROSE' } };
    },
    searchIssues: async () => {
      searchCalls++;
      throw new Error('offline');
    },
    save: async () => {},
    warn: () => {},
  };

  await reconcileSelfReports(state, ports, { selfReport: 'auto' }, [run]);
  await reconcileSelfReports(state, ports, { selfReport: 'auto' }, [run]);
  await reconcileSelfReports(state, ports, { selfReport: 'auto' }, [run]);

  assert.equal(diagnosisCalls, 1, 'filing retry must reuse the diagnosis result');
  assert.equal(searchCalls, 2, 'a failed canonical search stops each of the two bounded filing attempts');
  const custody = Object.values(state.selfReportLedger.seen)[0];
  assert.equal(custody.diagnosisAttempted, true);
  assert.equal(custody.diagnosisStatus, 'complete');
  assert.equal(custody.diagnosisSession.id, sessionId);
  assert.equal(custody.filingAttempts, 2);
  assert.equal(custody.filingStatus, 'exhausted');
  assert.ok(!JSON.stringify(custody.diagnosisResult).includes('PRIVATE_DIAGNOSIS_PROSE'));

  const diagnosisEntry = run.selfReports.find(row => row.action === 'diagnosed');
  assert.equal(diagnosisEntry.session.id, sessionId);
  assert.equal(diagnosisEntry.session.agent, 'codex');
  assert.equal(diagnosisEntry.session.configDir, savedConfigDir);
  const cost = captureCosts(null, run, { now: () => at, env: { HOME: home, CODEX_HOME: join(home, 'decoy-codex-account') } });
  assert.deepEqual(cost.selfReports, { filed: 0, commented: 0, skipped: 0 });
  assert.equal(cost.tokens[0].total, 168, 'the saved account usage must reach the cost ledger');
  assert.ok(!cost.coverage.includes('self-report-usage-unavailable'));
});


test('missing diagnose usage remains unknown in cost coverage', () => {
  const home = fs.mkdtempSync(join(tmpdir(), 'pdd-self-report-usage-missing-'));
  try {
    const run = {
      runId: 'missing-diagnose-usage', root: home, runDir: home,
      launchProfile: { agent: 'codex', configDir: null, model: null },
      selfReports: [{
        id: 'diagnosed-without-session', action: 'diagnosed', side: 'pdd', signature: 'ERR:src/x.mjs:fn',
        session: { id: null, agent: 'codex', configDir: null, at: Date.parse('2026-11-10T12:00:00Z') },
      }],
    };
    const cost = captureCosts(null, run, { env: { HOME: home, CODEX_HOME: join(home, 'decoy') } });
    assert.ok(cost.coverage.includes('self-report-usage-unavailable'));
    assert.deepEqual(cost.tokens, []);
  } finally { fs.rmSync(home, { recursive: true, force: true }); }
});

test('redaction removes secrets, tokens, request/response prose, user source code and home paths except PDD state paths', () => {
  const home = '/home/serhan';
  const env = {
    HOME: home,
    CUSTOM_API_SECRET: 'my-ultra-secret-value-9999',
  };
  const raw = [
    'Token ghp_1234567890abcdefghijklmnopqrstuv and github_pat_1234567890abcdefghijklmnop',
    'OpenAI sk-proj-abcdefghijklmnopqrstuvwx and Anthropic sk-ant-api03-abcdefghijklmnop',
    'Header Authorization: Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.secret',
    'Slack https://hooks.slack.com/services/T000/B000/XXXXXXXXXXXXXXXX and env my-ultra-secret-value-9999',
    'Try link https://runtime.promptdriven.ai/s/abc123def456/index.html',
    'User repo path: /home/serhan/projects/private-customer-app/src/ billing.js',
    'macOS path: /Users/alice/Documents/secret-project/index.ts',
    'PDD state path kept: /home/serhan/.local/state/pdd/autopilot/1234567890abcdef.json',
    'PDD runtime path kept: /home/serhan/.pdd/runtime/batches/20261110/batch.json',
    'PDD skills path kept: /home/serhan/.agents/skills/pdd-autopilot/SKILL.md',
    'request_body: {"prompt":"secret customer prompt"}',
    'response_prose: "Here is the confidential response prose"',
    '```js\nconst customerSecret = 42;\nconsole.log(customerSecret);\n```',
    '```text\nTypeError: boom\n    at stepDoneCommand (src/workflow-runner.mjs:3120:15)\n```',
  ].join('\n');

  const redacted = redactSelfReport(raw, { home, env });

  assert.ok(!redacted.includes('ghp_1234567890'));
  assert.ok(!redacted.includes('github_pat_1234567890'));
  assert.ok(!redacted.includes('sk-proj-'));
  assert.ok(!redacted.includes('sk-ant-'));
  assert.ok(!redacted.includes('eyJhbGciOi'));
  assert.ok(!redacted.includes('hooks.slack.com'));
  assert.ok(!redacted.includes('my-ultra-secret-value-9999'));
  assert.ok(!redacted.includes('/s/abc123def456'));
  assert.ok(!redacted.includes('private-customer-app'));
  assert.ok(!redacted.includes('secret-project'));
  assert.ok(!redacted.includes('secret customer prompt'));
  assert.ok(!redacted.includes('confidential response prose'));
  assert.ok(!redacted.includes('customerSecret'));

  // PDD's own state paths and PDD stack frames are preserved:
  assert.match(redacted, /~\/\.local\/state\/pdd\/autopilot\/1234567890abcdef\.json/);
  assert.match(redacted, /~\/\.pdd\/runtime\/batches\/20261110\/batch\.json/);
  assert.match(redacted, /~\/\.agents\/skills\/pdd-autopilot\/SKILL\.md/);
  assert.match(redacted, /at stepDoneCommand \(src\/workflow-runner\.mjs:3120:15\)/);
  assert.match(redacted, /~\/<redacted>/);
});

test('consent defaults to auto inside promptdriven/* and asks once outside, while respecting autopilot.selfReport in pdd.json', async () => {
  // 1. Inside promptdriven/* organization: default is auto
  assert.deepEqual(selfReportConsent('promptdriven/pdd', {}, {}), {
    mode: 'auto',
    source: 'org-default',
    prompt: null,
  });
  assert.deepEqual(selfReportConsent('PromptDriven/other-repo', {}, {}), {
    mode: 'auto',
    source: 'org-default',
    prompt: null,
  });

  // 2. Outside promptdriven/* organization: default is ask-once with exact prompt
  assert.deepEqual(selfReportConsent('acme/widget', {}, {}), {
    mode: 'ask-once',
    source: 'outside-default',
    prompt: CONSENT_PROMPT,
  });
  assert.equal(CONSENT_PROMPT, 'May Autopilot file PDD bug reports for failures in PDD itself? auto / ask each time / off');

  // Asking once persists the answer in state so a second failure does not ask again:
  const stateAuto = {};
  let prompts = 0;
  const firstAuto = await resolveSelfReportConsent({
    repo: 'acme/widget',
    config: {},
    state: stateAuto,
    ask: async q => { prompts++; assert.equal(q, CONSENT_PROMPT); return 'auto'; },
  });
  assert.equal(firstAuto.allowed, true);
  assert.equal(firstAuto.asked, true);
  assert.equal(stateAuto.selfReportConsent, 'auto');

  const secondAuto = await resolveSelfReportConsent({
    repo: 'acme/widget',
    config: {},
    state: stateAuto,
    ask: async () => { prompts++; return 'off'; },
  });
  assert.equal(secondAuto.allowed, true);
  assert.equal(secondAuto.asked, false);
  assert.equal(prompts, 1, 'ask-once must not prompt a second time after saving auto');

  // 3. Explicit pdd.json autopilot.selfReport setting overrides defaults:
  for (const mode of ['auto', 'ask', 'off']) {
    const decision = selfReportConsent('promptdriven/pdd', { selfReport: mode }, {});
    assert.equal(decision.mode, mode);
    assert.equal(decision.source, 'config');
  }
  const offRes = await resolveSelfReportConsent({ repo: 'promptdriven/pdd', config: { selfReport: 'off' }, state: {} });
  assert.equal(offRes.allowed, false);
  assert.equal(offRes.reason, 'self-report-off');
});

test('status and cost ledger report self-reports filed, commented and skipped, and parking summary shows issue wake condition', () => {
  const at = Date.parse('2026-11-10T15:00:00Z');
  const run = {
    runId: 'attempt-1',
    number: 17,
    repo: 'promptdriven/pdd',
    startedAt: at - 60_000,
    updatedAt: at,
    state: 'paused',
    runDir: '/tmp/nonexistent-run-dir',
    root: '/tmp/nonexistent-root',
    chats: [],
    pr: [],
    areas: [{ name: 'code' }],
    parking: {
      at,
      phase: 'parked',
      blocker: { kind: 'pdd', until: '#501' },
    },
    selfReports: [
      { id: 'sr-1', at: at - 20_000, action: 'filed', side: 'pdd', signature: 'ERR_1+m+f', issue: { number: 501 } },
      { id: 'sr-2', at: at - 10_000, action: 'commented', side: 'pdd', signature: 'ERR_1+m+f', issue: { number: 501 } },
      { id: 'sr-3', at: at - 5_000, action: 'skipped', side: 'pdd', signature: 'ERR_2+m+f', issue: null },
    ],
  };

  run.cost = captureCosts(null, run, { now: () => at });
  assert.deepEqual(run.cost.selfReports, { filed: 1, commented: 1, skipped: 1 });

  const report = costReport([run], at);
  assert.deepEqual(report.selfReports, { filed: 1, commented: 1, skipped: 1 });
  assert.deepEqual(report.runs[0].selfReports, { filed: 1, commented: 1, skipped: 1 });
  assert.deepEqual(report.day.totals.selfReports, { filed: 1, commented: 1, skipped: 1 });

  const statusText = costStatusLines(report);
  assert.match(statusText, /Self-reports: filed 1, commented 1, skipped 1/);
  assert.match(statusText, /self-reports 1 filed, 1 commented, 1 skipped/);

  const summary = parkingSummary([run], 2, at);
  const words = parkingWords(summary);
  assert.equal(wakeCondition({ kind: 'pdd', until: '#501' }), 'when issue #501 closes or the installed PDD has the fix');
  assert.equal(wakeCondition({ kind: 'runtime', until: '502' }), 'when Runtime issue #502 closes or a later check gets a verdict');
  assert.match(words, /#17: when issue #501 closes or the installed PDD has the fix/);
});

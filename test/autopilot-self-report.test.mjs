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
    if (actual.reportable) assert.match(actual.signature, /^[^:]+\+[^:]+\+[^:]+$/, `${row.name}: signature format`);
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
    env: { HOME: '/home/alice', GITHUB_TOKEN: 'ghp_superSecretTokenValue123456' },
    execute: async (file, args, options) => {
      execCalls.push({ file, args, options });
      const sessionId = '11111111-2222-7333-8444-555555555555';
      const payload = {
        title: 'PDD command-crash: TypeError in src/workflow-runner.mjs (stepDoneCommand)',
        problem: 'stepDoneCommand throws TypeError when run.done is null in status.json.',
        steps: ['Corrupt status.json with done: null', 'Run pdd workflow done verify --summary "Tests: 1 passed"'],
        expected: 'pdd workflow done initializes or validates run.done without throwing an uncaught TypeError.',
        actual: 'Uncaught TypeError at src/workflow-runner.mjs:3120 in stepDoneCommand.',
        evidence: 'at stepDoneCommand (/home/alice/work/repo/src/workflow-runner.mjs:3120:15)\nState log: /home/alice/.local/state/pdd/autopilot/state.json',
        rootCause: {
          module: 'src/workflow-runner.mjs',
          fn: 'stepDoneCommand',
          line: 3120,
          fileLine: 'src/workflow-runner.mjs:3120',
          explanation: 'stepDoneCommand reads run.done[step] without guarding against a null done field.',
        },
        signature: 'TypeError+src/workflow-runner.mjs+stepDoneCommand',
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
  assert.equal(report.signature, 'TypeError+src/workflow-runner.mjs+stepDoneCommand');
  assert.equal(report.rootCause.fileLine, 'src/workflow-runner.mjs:3120');
  assert.equal(report.session.id, '11111111-2222-7333-8444-555555555555');
  assert.match(report.body, /## Problem/);
  assert.match(report.body, /## Steps to reproduce/);
  assert.match(report.body, /## Expected vs\. actual/);
  assert.match(report.body, /## Evidence/);
  assert.match(report.body, /## Versions/);
  assert.match(report.body, /## Suspected root cause/);
  assert.match(report.body, /<!-- pdd:self-report:TypeError\+src\/workflow-runner\.mjs\+stepDoneCommand -->/);
  // Home path redaction inside evidence preserves ~/.local/state/pdd and redacts /home/alice/work/repo:
  assert.match(report.body, /~\/\.local\/state\/pdd\/autopilot\/state\.json/);
  assert.ok(!report.body.includes('/home/alice/work'));
});

test('dedupe adds one comment on open issue, cap limits new issues to 5 per machine per day, and target repo is always promptdriven/pdd', async t => {
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
    /Refusing to file in private repository promptdriven\/prompt-runtime/
  );
  await assert.rejects(
    fileSelfReport({ targetRepo: 'acme/private-app', repo: 'acme/private-app', config: { selfReport: 'auto' } }, ports),
    /self-reports must target promptdriven\/pdd/
  );

  const state = {};
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
  }, ports);
  assert.equal(dup.action, 'commented');
  assert.equal(dup.issue.number, 601);
  assert.equal(created.length, 1, 'dedupe must not file a second issue');
  assert.equal(comments.length, 1, 'dedupe must add one comment');
  assert.match(comments[0].body, /New occurrence of `ERR_1\+src\/workflow-runner\.mjs\+fn1`/);

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

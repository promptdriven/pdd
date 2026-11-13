import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import * as runtimeOutcome from '../src/runtime-outcome.mjs';
import { exitCodeFor, projectAnswer, renderJson, renderText, summaryLine } from '../src/runtime-output.mjs';
import { resendableStoryChecks, runCheck } from '../src/runtime-client.mjs';
import { checkCause, savedCheckCause } from '../src/workflow-results.mjs';
import { fakeRuntime, harbor, PLACE, portsFor, TOKEN } from './runtime-fake.mjs';

const { resultOutcome, PROVIDER_TEXT } = runtimeOutcome;

function formatBytesAnswer(fake, id) {
  const answer = fake.job(id, 'check', 'unknown', {
    outcome: 'Inconclusive',
    exitCode: 3,
    why: 'The run may have executed. Its result is unknown.',
    next_step: 'run `pdd test --read 20261111-112222-qlfr` to inspect saved results; do not resend automatically.',
    refusals: [{
      code: 'graph-provider-failure',
      message: 'The runtime refused this job. See the reported reason.',
      engine_message: 'step execution refused',
      section: 'samples[0].steps[3]'
    }],
    report: {
      criterion_results: [
        { criterion_id: 'AC1', status: 'passed' },
        { criterion_id: 'AC2', status: 'failed' },
        { criterion_id: 'AC3', status: 'failed' },
        { criterion_id: 'AC4', status: 'not_checked' }
      ],
      samples: [{
        sample: 1,
        refusal: {
          code: 'graph-provider-failure',
          section: 'samples[0].steps[3]',
          failure_cause: { kind: 'transport_unknown', detail: 'internal-retry' }
        },
        steps: [
          {
            step_id: 'one-kib',
            result: { text: '1 KiB' },
            checks: [{ criterion_id: 'AC1', target: 'result', path: '/text', op: 'equals', expected: '1 KiB', actual: '1 KiB', passed: true }]
          },
          {
            step_id: 'format-10',
            result: { text: '8 TiB' },
            checks: [{ criterion_id: 'AC2', target: 'result', path: '/text', op: 'equals', expected: '7 PiB', actual: '8 TiB', passed: false }]
          },
          {
            step_id: 'zibi',
            result: { text: '1024 EiB' },
            checks: [{ criterion_id: 'AC3', target: 'result', path: '/text', op: 'equals', expected: '1 ZiB', actual: '1024 EiB', passed: false }]
          }
        ]
      }]
    }
  }, 3);
  answer.draft_prompts = [PLACE];
  Object.assign(answer.usage, {
    calls: 3,
    known_calls: 3,
    unknown_calls: 1,
    accounting_complete: false,
    seconds: 1.2
  });
  return answer;
}

test('R1 & R2: summaryLine, resultOutcome, and renderText surface failed checks and never claim "not a failed check"', () => {
  const n2 = { state: 'unknown', provider: { code: 'graph-provider-failure' }, failed_checks: [{ step_id: 'format-10' }, { step_id: 'zibi' }] };
  const n1 = { state: 'unknown', provider: { code: 'graph-provider-failure' }, failed_checks: [{ step_id: 'format-10' }] };
  const n0 = { state: 'unknown', provider: { code: 'graph-provider-failure' }, failed_checks: [], criteria: { passed: 0, total: 4 } };

  assert.deepEqual(resultOutcome(n2).reason, {
    code: 'graph-provider-failure',
    message: 'the AI provider failed during the run after 2 checks failed. Do not send it again yet.'
  });
  assert.deepEqual(resultOutcome(n1).reason, {
    code: 'graph-provider-failure',
    message: 'the AI provider failed during the run after 1 check failed. Do not send it again yet.'
  });
  assert.deepEqual(resultOutcome(n0).reason, {
    code: 'graph-provider-failure',
    message: PROVIDER_TEXT
  });
  assert.doesNotMatch(resultOutcome(n2).reason.message, /not a failed check/i);
  assert.doesNotMatch(resultOutcome(n1).reason.message, /not a failed check/i);

  assert.equal(typeof runtimeOutcome.failedCheckCount, 'function');
  assert.equal(typeof runtimeOutcome.providerText, 'function');
  assert.equal(runtimeOutcome.failedCheckCount({ criteria: { passed: 0, total: 4 }, checks: null, failed_checks: [] }), 0,
    'never infer failed checks from unexecuted criteria');
  assert.equal(runtimeOutcome.failedCheckCount({ checks: { passed: 1, total: 3 }, failed_checks: [] }), 2,
    'fall back to checks.total - checks.passed when both are safe integers');
  assert.equal(runtimeOutcome.failedCheckCount({ checks: { passed: 0, total: 5 }, failed_checks: [{ step_id: 's1' }] }), 1,
    'prefer positive failed_checks.length');
  assert.equal(runtimeOutcome.providerText(n0), PROVIDER_TEXT);

  const row = {
    story: 'format-bytes',
    title: 'Format bytes',
    test: 'tests/runtime/format-bytes.json',
    phase: 'server',
    draft: true,
    state: 'unknown',
    provider: { code: 'graph-provider-failure', detail: 'transport_unknown, internal-retry' },
    criteria: { passed: 1, total: 4 },
    checks: { passed: 1, total: 3 },
    failed_checks: [
      { criterion_id: 'AC2', step_id: 'format-10', target: 'result', path: '/text', expected: '7 PiB', actual: '8 TiB' },
      { criterion_id: 'AC3', step_id: 'zibi', target: 'result', path: '/text', expected: '1 ZiB', actual: '1024 EiB' }
    ],
    calls: 'unknown',
    known_calls: 3,
    unknown_calls: 1,
    accounting_complete: false,
    seconds: 1.2,
    report_url: 'https://runtime.example/r/check-format-bytes',
    next_step: 'run `pdd test --read 20261111-112222-qlfr` to inspect saved results; do not resend automatically.'
  };

  assert.equal(
    summaryLine([row], 'format-bytes'),
    'Prompt tests (format-bytes) (DRAFT): ✗ 1 of 4 criteria · 1/3 checks · 2 failed · 1 partial (graph-provider-failure) · 3 AI calls + 1 unknown'
  );
  assert.equal(
    summaryLine([row]),
    'Prompt tests (DRAFT): ✗ 1 of 4 criteria · 1/3 checks · 2 failed · 1 partial (graph-provider-failure) · 3 AI calls + 1 unknown'
  );
  assert.equal(
    summaryLine([{
      ...row,
      criteria: { passed: 10, total: 13 },
      checks: { passed: 17, total: 19 },
      known_calls: 39,
      unknown_calls: 1
    }], 'format-bytes'),
    'Prompt tests (format-bytes) (DRAFT): ✗ 10 of 13 criteria · 17/19 checks · 2 failed · 1 partial (graph-provider-failure) · 39 AI calls + 1 unknown'
  );
  assert.equal(
    summaryLine([{
      ...row,
      checks: { passed: 1, total: 1 },
      failed_checks: [],
      known_calls: 1,
      unknown_calls: 1
    }], 'format-bytes'),
    'Prompt tests (format-bytes) (DRAFT): no verdict · 1 of 4 criteria · 1/1 checks · 1 partial (graph-provider-failure) · 1 AI call + 1 unknown'
  );

  const code = exitCodeFor([row]);
  assert.equal(code, 3);
  const text = renderText({ batch: '20261111-112222-qlfr', rows: [row], exitCode: code });
  assert.match(text, /Prompt tests \(format-bytes\) \(DRAFT\): ✗ 1 of 4 criteria · 1\/3 checks · 2 failed · 1 partial \(graph-provider-failure\) · 3 AI calls \+ 1 unknown/);
  assert.match(text, /1 Story failed its checks\. That Story also has checks with no verdict, so the exit code is 3\./);
  assert.match(text, /FAILED {2}Format bytes \(tests\/runtime\/format-bytes\.json\)/);
  assert.match(text, /AC2 {2}step format-10 {2}result \/text {2}expected "7 PiB", got "8 TiB"/);
  assert.match(text, /AC3 {2}step zibi {2}result \/text {2}expected "1 ZiB", got "1024 EiB"/);
  assert.match(text, /UNKNOWN {2}Format bytes: the AI provider failed during the run after 2 checks failed\. Do not send it again yet\./);
  assert.doesNotMatch(text, /not a failed check/i);
});

test('R3: projectAnswer aggregates failed_checks across multiple samples and supports result.failed_checks fallback', () => {
  const multiSample = {
    command: 'check',
    state: 'unknown',
    usage: { calls: 4, known_calls: 4, unknown_calls: 1, accounting_complete: false },
    result: {
      refusals: [{ code: 'graph-provider-failure', section: 'samples[1].steps[1]' }],
      report: {
        criterion_results: [
          { criterion_id: 'AC1', status: 'passed' },
          { criterion_id: 'AC2', status: 'failed' },
          { criterion_id: 'AC3', status: 'failed' }
        ],
        samples: [
          {
            sample: 1,
            steps: [
              {
                step_id: 'one-kib',
                result: { text: '1 KiB' },
                checks: [{ criterion_id: 'AC1', target: 'result', path: '/text', expected: '1 KiB', actual: '1 KiB', passed: true }]
              },
              {
                step_id: 'format-10',
                result: { text: '8 TiB' },
                checks: [{ criterion_id: 'AC2', target: 'result', path: '/text', expected: '7 PiB', actual: '8 TiB', passed: false }]
              }
            ]
          },
          {
            sample: 2,
            refusal: { code: 'graph-provider-failure', failure_cause: { kind: 'transport_unknown', detail: 'timeout-stream' } },
            steps: [
              {
                step_id: 'zibi',
                result: { text: '1024 EiB' },
                checks: [{ criterion_id: 'AC3', target: 'result', path: '/text', expected: '1 ZiB', actual: '1024 EiB', passed: false }]
              }
            ]
          }
        ]
      }
    }
  };
  const view = projectAnswer(multiSample);
  assert.equal(view.state, 'unknown');
  assert.deepEqual(view.checks, { passed: 1, total: 3 });
  assert.deepEqual(view.failed_checks.map(item => [item.step_id, item.criterion_id, item.expected, item.actual]), [
    ['format-10', 'AC2', '7 PiB', '8 TiB'],
    ['zibi', 'AC3', '1 ZiB', '1024 EiB']
  ]);

  const fallbackAnswer = {
    command: 'check',
    state: 'unknown',
    usage: { calls: 2, known_calls: 2, unknown_calls: 1, accounting_complete: false },
    result: {
      refusals: [{ code: 'graph-provider-failure' }],
      checks: { passed: 1, total: 3 },
      failed_checks: [
        { step_id: 'format-10', criterion_id: 'AC2', target: 'result', path: '/text', expected: '7 PiB', actual: `8 TiB ${TOKEN}` },
        { step_number: 3, criterion_id: 'AC3', target: 'result', path: '/text', expected: '1 ZiB', actual: '1024 EiB sk-abcdefghijklmnop' }
      ],
      report: { samples: [] }
    }
  };
  const fallbackView = projectAnswer(fallbackAnswer, {
    secrets: [TOKEN],
    steps: [{ step_id: 'one-kib' }, { step_id: 'format-10' }, { step_id: 'zibi' }]
  });
  assert.deepEqual(fallbackView.checks, { passed: 1, total: 3 });
  assert.deepEqual(fallbackView.failed_checks.map(item => [item.step_id, item.criterion_id, item.actual]), [
    ['format-10', 'AC2', '8 TiB [secret]'],
    ['zibi', 'AC3', '1024 EiB [secret]']
  ]);
});

test('R4: fake batch with 2 failed steps and 1 provider failure keeps ✗ 2 failed, truthful reason, JSON/batch.json/--read failed_checks, and checkCause issue', async t => {
  const setup = harbor(t, repo => {
    const promptPath = join(repo, PLACE);
    const promptDoc = readFileSync(promptPath, 'utf8')
      .replace('"status": "approved"', '"status": "draft"')
      .replace('"totalCents": {"type": "integer"}', '"totalCents": {"type": "integer"},\n          "text": {"type": "string"}');
    writeFileSync(promptPath, promptDoc);
    writeFileSync(join(repo, 'user_stories/format-bytes.md'), [
      '# Format bytes',
      '',
      'As a user, I want byte counts formatted cleanly.',
      '',
      '## Acceptance criteria',
      '',
      '1. Format 1024 bytes as 1 KiB.',
      '2. Format petabytes accurately.',
      '3. Format zebibytes accurately.',
      '4. Format yobibytes accurately.'
    ].join('\n'));
    const scenario = JSON.parse(readFileSync(join(repo, 'tests/place-order.json'), 'utf8'));
    const template = scenario.steps[0];
    writeFileSync(join(repo, 'tests/format-bytes.json'), JSON.stringify({
      ...scenario,
      story_path: 'user_stories/format-bytes.md',
      criteria: [
        { id: 'AC1', text: 'Format 1024 bytes as 1 KiB.' },
        { id: 'AC2', text: 'Format petabytes accurately.' },
        { id: 'AC3', text: 'Format zebibytes accurately.' },
        { id: 'AC4', text: 'Format yobibytes accurately.' }
      ],
      steps: [
        { ...template, step_id: 'one-kib', checks: [{ criterion_id: 'AC1', target: 'result', path: '/text', op: 'equals', value: '1 KiB' }] },
        { ...template, step_id: 'format-10', checks: [{ criterion_id: 'AC2', target: 'result', path: '/text', op: 'equals', value: '7 PiB' }] },
        { ...template, step_id: 'zibi', checks: [{ criterion_id: 'AC3', target: 'result', path: '/text', op: 'equals', value: '1 ZiB' }] },
        { ...template, step_id: 'yobi', checks: [{ criterion_id: 'AC4', target: 'result', path: '/text', op: 'equals', value: '1 YiB' }] }
      ]
    }, null, 2));
  });

  let offline = false;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'lint') {
      return { status: 200, json: f.lint(entry.request.requestId, [{ path: PLACE, state: 'draft', admission_state: 'draft', interface: { calls: [] } }]) };
    }
    if (entry.method === 'GET' && offline) return { destroy: true };
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    const answer = formatBytesAnswer(f, id);
    f.jobs.set(id, answer);
    return { status: 200, json: answer };
  });

  const env = { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state };
  const run = async (options = {}, words = ['format-bytes']) => {
    const { ports } = portsFor(env);
    const code = await runCheck({ words, options, cwd: setup.repo }, ports);
    return {
      code,
      out: ports.stdout.text,
      err: ports.stderr.text,
      json: options['--json'] ? JSON.parse(ports.stdout.text) : null
    };
  };

  // Immediate JSON + text run
  const initial = await run({ '--json': true });
  assert.equal(initial.code, 3, initial.err);
  assert.equal(
    initial.json.summary_line,
    'Prompt tests (DRAFT): ✗ 1 of 4 criteria · 1/3 checks · 2 failed · 1 partial (graph-provider-failure) · 3 AI calls + 1 unknown'
  );
  const row = initial.json.rows[0];
  assert.equal(row.state, 'partial');
  assert.equal(
    row.summary_line,
    'Prompt tests (format-bytes) (DRAFT): ✗ 1 of 4 criteria · 1/3 checks · 2 failed · 1 partial (graph-provider-failure) · 3 AI calls + 1 unknown'
  );
  assert.deepEqual(row.reason, {
    code: 'graph-provider-failure',
    message: 'the AI provider failed during the run after 2 checks failed. Do not send it again yet.'
  });
  assert.doesNotMatch(row.reason.message, /not a failed check/i);
  assert.deepEqual(row.checks, { passed: 1, total: 3 });
  assert.deepEqual(row.criteria, { passed: 1, total: 4 });
  assert.deepEqual(row.failed_checks.map(item => [item.step_id, item.criterion_id, item.expected, item.actual]), [
    ['format-10', 'AC2', '7 PiB', '8 TiB'],
    ['zibi', 'AC3', '1 ZiB', '1024 EiB']
  ]);

  // Saved batch.json and summary.json also retain checks, criteria, and both failed_checks
  const folder = join(setup.state, 'batches', initial.json.batch);
  const savedBatch = JSON.parse(readFileSync(join(folder, 'batch.json'), 'utf8'));
  const savedSummary = JSON.parse(readFileSync(join(folder, 'summary.json'), 'utf8'));
  assert.deepEqual(savedBatch.rows[0].checks, { passed: 1, total: 3 });
  assert.deepEqual(savedBatch.rows[0].criteria, { passed: 1, total: 4 });
  assert.deepEqual(savedBatch.rows[0].failed_checks.map(item => item.step_id), ['format-10', 'zibi']);
  assert.doesNotMatch(savedBatch.rows[0].reason.message, /not a failed check/i);
  assert.deepEqual(savedSummary.rows[0].failed_checks.map(item => item.step_id), ['format-10', 'zibi']);

  // Workflow checkCause / savedCheckCause classify as 'issue' (not 'service'), and resendableStoryChecks classifies as 'failed'
  assert.equal(checkCause(initial.json.rows), 'issue');
  assert.equal(checkCause(savedBatch.rows), 'issue');
  assert.equal(savedCheckCause(initial.json.batch, { env }), 'issue');
  const resendable = await resendableStoryChecks({ root: setup.repo }, { env });
  assert.deepEqual(resendable.failed, ['user_stories/format-bytes.md']);
  assert.deepEqual(resendable.noVerdict, []);

  // pdd test --read with --timeout 0 (zero network GETs) preserves failed_checks, summary, and truthful reason
  const getsBeforeZeroTimeout = fake.gets.length;
  const zeroTimeoutJson = await run({ '--read': true, '--timeout': 0, '--json': true }, [initial.json.batch]);
  assert.equal(zeroTimeoutJson.code, 3, zeroTimeoutJson.err);
  assert.equal(fake.gets.length, getsBeforeZeroTimeout, '--timeout 0 performs no GET');
  assert.equal(zeroTimeoutJson.json.summary_line, initial.json.summary_line);
  assert.deepEqual(zeroTimeoutJson.json.rows[0].checks, { passed: 1, total: 3 });
  assert.deepEqual(zeroTimeoutJson.json.rows[0].failed_checks.map(item => item.step_id), ['format-10', 'zibi']);
  assert.deepEqual(zeroTimeoutJson.json.rows[0].reason, row.reason);

  const zeroTimeoutText = await run({ '--read': true, '--timeout': 0 }, [initial.json.batch]);
  assert.equal(zeroTimeoutText.code, 3);
  assert.match(zeroTimeoutText.out, /✗ 1 of 4 criteria · 1\/3 checks · 2 failed · 1 partial \(graph-provider-failure\)/);
  assert.match(zeroTimeoutText.out, /FAILED {2}Format bytes \(tests\/format-bytes\.json\)/);
  assert.doesNotMatch(zeroTimeoutText.out, /not a failed check/i);

  // Offline GET poll during pdd test --read still preserves saved receipt failed_checks and truthful reason
  offline = true;
  const offlineRead = await run({ '--read': true, '--json': true }, [initial.json.batch]);
  assert.equal(offlineRead.code, 3);
  assert.deepEqual(offlineRead.json.rows[0].checks, { passed: 1, total: 3 });
  assert.deepEqual(offlineRead.json.rows[0].failed_checks.map(item => item.step_id), ['format-10', 'zibi']);
  assert.deepEqual(offlineRead.json.rows[0].reason, row.reason);

  // Even if <id>.json is absent, batch.json row fallback preserves checks, criteria, and failed_checks on --timeout 0 read
  rmSync(join(folder, `${savedBatch.rows[0].request_ids[0]}.json`));
  const batchOnlyRead = await run({ '--read': true, '--timeout': 0, '--json': true }, [initial.json.batch]);
  assert.equal(batchOnlyRead.code, 3);
  assert.deepEqual(batchOnlyRead.json.rows[0].checks, { passed: 1, total: 3 });
  assert.deepEqual(batchOnlyRead.json.rows[0].criteria, { passed: 1, total: 4 });
  assert.deepEqual(batchOnlyRead.json.rows[0].failed_checks.map(item => item.step_id), ['format-10', 'zibi']);
  assert.match(batchOnlyRead.json.summary_line, /✗ 1 of 4 criteria · 1\/3 checks · 2 failed/);

  assert.equal(fake.posts.filter(post => post.command === 'check').length, 1, 'no extra paid check POST');
});

import test from 'node:test';
import assert from 'node:assert/strict';
import { exitCodeFor, projectAnswer, renderJson, renderText, summaryLine } from '../src/runtime-output.mjs';
import { TOKEN, ordinaryCapabilities, sha } from './runtime-fake.mjs';

// Expected outcomes through the public output functions, so they are part of the contract.
const selected = { test: 'tests/one.json', steps: [{ step_id: 'one', operation: 'one', entry_path: 'prompts/one.prompt.md' }] };
const sources = [{ path: selected.test, bytes: Buffer.from(JSON.stringify({ steps: selected.steps })) }];
selected.sourceFiles = sources.map(source => ({ path: source.path, sha256: sha(source.bytes) }));
const lint = () => ({ command: 'lint', state: 'passed', engine_sha: 'eae2202a68d00ab762fcbbf1eba0d8607a132a15', result: {
  capabilities: [{ path: selected.test, report: ordinaryCapabilities(sources, selected.test) }],
  report: { lint: { complete: true, tests: [{ path: selected.test, verdict: 'passed' }] } } } });
const refused = { code: 'bad-input', field: '/steps/0/input', message: 'Correct this input.', fix: 'Use an integer.' };
const row = view => ({ ...view, story: 'one', title: 'One', test: selected.test, phase: 'server' });

for (const shape of ['no-inventory', 'empty-inventory', 'partial-inventory']) test(`OUTCOME model: an ended incomplete lint without a verdict is not run (${shape})`, () => {
  const answer = lint();
  answer.result.report.lint = { complete: false, tests: [] };
  answer.result.report.program = shape === 'no-inventory' ? {} : { prompts: shape === 'empty-inventory' ? [] : [{ path: 'prompts/other.prompt.md' }] };
  const view = projectAnswer(answer, selected);
  assert.equal(view.state, 'not_run');
  assert.equal(exitCodeFor([view]), 5);
});

for (const location of ['test', 'entry', 'entry-no-inventory']) test(`OUTCOME model: an explicit ${location} refusal defeats a selected pass`, () => {
  const answer = lint();
  if (location === 'test') answer.result.refusals = [{ ...refused, file: selected.test }];
  else answer.result.report.program = { ...(location === 'entry' ? { prompts: [] } : {}), refused_prompts: [{ ...refused, path: selected.steps[0].entry_path }] };
  const view = projectAnswer(answer, selected);
  assert.equal(view.state, 'refused');
  if (location === 'test') assert.equal(view.refusals[0].field, refused.field);
});

test('OUTCOME model: an unrelated refusal is scoped out by a selected pass; the input is unchanged', () => {
  const answer = lint(); answer.state = 'refused'; answer.result.refusals = [{ ...refused, file: 'tests/other.json' }];
  const before = structuredClone(answer);
  assert.equal(projectAnswer(answer, selected).state, 'passed');
  assert.deepEqual(answer, before);
  assert.equal(projectAnswer(answer, { ...selected, test: 'tests/other.json' }).state, 'refused');
});

test('OUTCOME model: a test with its own pass passes although the lint did not finish', () => {
  const answer = lint();
  answer.result.report.lint = { complete: false, tests: [{ path: selected.test, verdict: 'passed' }, { path: 'tests/other.json', verdict: 'not-checked' }] };
  assert.equal(projectAnswer(answer, selected).state, 'passed');
  assert.equal(projectAnswer(answer, { ...selected, test: 'tests/other.json' }).state, 'not_run');
});

test('OUTCOME model: unknown means not ended; a passed check needs a result; failed stays failed', () => {
  assert.equal(projectAnswer({ command: 'lint', state: 'unknown', result: { refusals: [refused] } }, selected).state, 'unknown');
  assert.equal(projectAnswer({ command: 'lint', state: 'running' }, selected).state, 'running');
  assert.equal(projectAnswer({ command: 'check', state: 'passed', result: null }).state, 'unknown');
  assert.equal(projectAnswer({ command: 'check', state: 'passed', result: {} }).state, 'passed');
  assert.equal(projectAnswer({ command: 'check', state: 'failed', result: { report: { verdict: 'refused' } } }).state, 'failed');
});

test('OUTCOME model: the exit precedence', () => {
  assert.equal(exitCodeFor([]), 3);
  assert.equal(exitCodeFor([{ state: 'refused' }, { state: 'not_run' }]), 5);
  assert.equal(exitCodeFor([{ state: 'failed' }, { state: 'refused' }]), 4);
  assert.equal(exitCodeFor([{ state: 'passed' }], { lintUnknown: true }), 3);
});

test('OUTCOME model: queued keeps its place in the table and JSON', () => {
  const view = row(projectAnswer({ command: 'check', state: 'queued', queue: { ahead: 2 } }));
  assert.match(renderText({ batch: 'b', rows: [view], exitCode: 3 }), /One +tests\/one\.json +sent \(awaiting-server-verdict\) · 2 ahead/);
  assert.equal(renderJson({ repo: 'r', rows: [view], exitCode: 3 }).rows[0].ahead, 2);
});

test('OUTCOME model: progress keeps only valid supplied fields and invents no numbers', () => {
  const partial = row(projectAnswer({ command: 'check', state: 'running', progress: { step: 'prepare', calls_settled: -1 } }));
  assert.deepEqual(partial.progress, { step: 'prepare' });
  assert.match(summaryLine([partial]), /sent \(awaiting-server-verdict\) · prepare/);
  assert.doesNotMatch(summaryLine([partial]), /0 AI calls|step \d/);
  assert.equal(projectAnswer({ command: 'check', state: 'running', progress: { step: 0 } }).progress, undefined, 'steps are one-based');
  const counted = row(projectAnswer({ command: 'check', state: 'running', progress: { steps_done: 2, steps_total: 5 } }));
  assert.match(summaryLine([counted]), /sent \(awaiting-server-verdict\) · step 3 of 5/);
  const named = row(projectAnswer({ command: 'check', state: 'running', progress: { steps_done: 2, steps_total: 5, step: 'render', calls_open: 1 } }));
  assert.match(summaryLine([named]), /sent \(awaiting-server-verdict\) · step 3 of 5 \(render\) · 1 not yet settled/, 'a named step keeps its number');
  assert.doesNotMatch(summaryLine([named]), /in flight/, 'an open call is not shown as live traffic');
});

test('OUTCOME model: one progress part per line, and the calls of ended rows stay', () => {
  const progress = { steps_done: 2, steps_total: 5, step: 3, calls_settled: 4, calls_open: 1 };
  const moving = row(projectAnswer({ command: 'check', state: 'running', progress }));
  const ended = { ...row({ state: 'passed' }), calls: 5, criteria: { passed: 1, total: 1 }, checks: { passed: 1, total: 1 } };
  assert.match(summaryLine([moving, ended]), /sent \(awaiting-server-verdict\) · step 3 of 5 · 4 AI calls so far · 1 not yet settled · 1 sent \(awaiting-server-verdict\) · 5 AI calls$/);
  assert.match(summaryLine([moving, moving, ended]), /checks · sent \(awaiting-server-verdict\) · 8 AI calls so far · 2 not yet settled · 2 sent \(awaiting-server-verdict\) · 5 AI calls$/);
});

test('OUTCOME model: a typed step timeout stays unknown even when the report verdict is refused', () => {
  const answer = { command: 'check', state: 'refused', result: { report: { verdict: 'refused', refusal: { code: 'graph-provider-failure', failure_cause: { kind: 'step_timeout' } } } } };
  assert.equal(projectAnswer(answer).state, 'unknown');
});

test('OUTCOME model: refusal fields and server text are cleaned at the public boundary', () => {
  const answer = lint();
  answer.state = 'refused'; answer.result.report.lint.tests = [];
  answer.result.refusals = [{ ...refused, message: `No ${TOKEN} at /srv/private/work\u001b[31m`, field: '/steps/0/input' }];
  const view = projectAnswer(answer, { ...selected, secrets: [TOKEN] });
  assert.equal(view.state, 'refused'); assert.equal(view.refusals[0].field, '/steps/0/input');
  assert.doesNotMatch(JSON.stringify(view), new RegExp(TOKEN + '|/srv/private|\\\\u001b'));
});

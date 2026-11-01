import test from 'node:test';
import assert from 'node:assert/strict';
import { hasProgress, outcomeDone, outcomeExitCode, outcomeFor, outcomeOverall, outcomeText } from '../src/runtime-outcome.mjs';
import { projectAnswer, summaryLine } from '../src/runtime-output.mjs';
import { TOKEN } from './runtime-fake.mjs';

const selected = { test: 'tests/one.json', steps: [{ entry_path: 'prompts/one.prompt.md' }] };
const lint = () => ({ command: 'lint', state: 'passed', result: { report: { lint: { complete: true, tests: [{ path: selected.test, verdict: 'passed' }] } } } });
const refused = { code: 'bad-input', field: '/steps/0/input', message: 'Correct this input.', fix: 'Use an integer.' };

for (const shape of ['no-inventory', 'empty-inventory', 'partial-inventory']) test(`OUTCOME model: incomplete ${shape} is unknown, never an invented refusal`, () => {
  const answer = lint();
  answer.result.report.lint = { complete: false, tests: [] };
  answer.result.report.program = shape === 'no-inventory' ? {} : { prompts: shape === 'empty-inventory' ? [] : [{ path: 'prompts/other.prompt.md' }] };
  const outcome = outcomeFor(answer, selected);
  assert.equal(outcome.state, 'unknown'); assert.equal(outcome.reason, 'lint did not finish');
  assert.equal(outcomeExitCode([outcome]), 3);
});

for (const location of ['test', 'entry', 'entry-no-inventory']) test(`OUTCOME model: an explicit ${location} refusal defeats a selected pass`, () => {
  const answer = lint();
  if (location === 'test') answer.result.refusals = [{ ...refused, file: selected.test }];
  else answer.result.report.program = { ...(location === 'entry' ? { prompts: [] } : {}), refused_prompts: [{ ...refused, path: selected.steps[0].entry_path }] };
  const outcome = outcomeFor(answer, selected);
  assert.equal(outcome.state, 'refused'); assert.equal(outcome.code, refused.code);
  assert.equal(outcome.field, refused.field); assert.equal(outcome.fix, refused.fix);
});

test('OUTCOME model: an unrelated refusal is scoped out by a complete selected pass; the input is unchanged', () => {
  const answer = lint(); answer.state = 'refused'; answer.result.refusals = [{ ...refused, file: 'tests/other.json' }];
  const before = structuredClone(answer);
  const first = outcomeFor(answer, selected);
  assert.equal(first.state, 'passed');
  assert.deepEqual(outcomeFor(answer, selected), first); assert.deepEqual(answer, before);
  assert.equal(outcomeFor(answer, { ...selected, test: 'tests/other.json' }).state, 'refused');
});

test('OUTCOME model: a job in an unknown state is unknown even with refusals; a passed check needs a result', () => {
  assert.equal(outcomeFor({ command: 'lint', state: 'unknown', result: { refusals: [refused] } }, selected).state, 'unknown');
  assert.equal(outcomeFor({ command: 'check', state: 'passed', result: null }).state, 'unknown');
  assert.equal(outcomeFor({ command: 'check', state: 'passed', result: {} }).state, 'passed');
});

test('OUTCOME model: unknown is not done; the exit precedence comes from one table', () => {
  for (const state of ['passed', 'failed', 'refused', 'not_run']) assert.equal(outcomeDone({ state }), true);
  for (const state of ['unknown', 'queued', 'running', 'ready']) assert.equal(outcomeDone({ state }), false);
  assert.equal(outcomeExitCode([]), 3); assert.equal(outcomeOverall([]), 'unknown');
  assert.equal(outcomeOverall([{ state: 'refused' }, { state: 'not_run' }]), 'not_run');
  assert.equal(outcomeExitCode([{ state: 'failed' }, { state: 'refused' }]), 4);
  assert.equal(outcomeExitCode([{ state: 'passed' }], { lintUnknown: true }), 3);
});

test('OUTCOME model: queued keeps its place and partial progress invents no numbers', () => {
  assert.equal(outcomeText(projectAnswer({ command: 'check', state: 'queued', queue: { ahead: 2 } })), 'queued · 2 ahead');
  const running = projectAnswer({ command: 'check', state: 'running', progress: { step: 'prepare', calls_settled: -1 } });
  assert.equal(hasProgress(running), true); assert.deepEqual(running.progress, { step: 'prepare' });
  assert.match(summaryLine([{ ...running, phase: 'server' }]), /running · prepare/);
  assert.doesNotMatch(summaryLine([{ ...running, phase: 'server' }]), /0 AI calls|step \d/);
  assert.equal(outcomeText({ state: 'running', progress: { steps_done: 2, steps_total: 5 } }), 'running · step 3 of 5');
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

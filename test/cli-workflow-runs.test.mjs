import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, mkdir, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';

const id = '123e4567-e89b-42d3-a456-426614174000';
const capture = () => ({ text: '', isTTY: true, write(value) { this.text += value; } });
async function fixture(t, overrides = {}) {
  const cwd = await mkdtemp(join(tmpdir(), 'pdd-runs-cli-'));
  await mkdir(join(cwd, '.git'));
  const stage = { id: 'scope', state: 'done', startedAt: 1700000000000, endedAt: 1700000005000,
    agent: 'codex', session: { agent: 'codex', id: '123e4567-e89b-42d3-a456-426614174001' }, ...overrides };
  const run = { runId: id, workflow: 'small-change', repo: 'octo/app', issue: { number: 7, title: 'Change label' }, root: cwd,
    runDir: join(cwd, '.git/pdd/workflows', id), state: 'completed', steps: [stage] };
  const records = { readRunIndex: async () => ({ entries: [run] }), readJournalLast: async () => ({ value: { state: run } }), runStatusFromState: async value => value };
  return { cwd, stdout: capture(), stderr: capture(), stdin: { isTTY: true }, workflowRecords: records, run };
}
for (const ref of ['7', '#7', 'app#7', 'octo/app#7', 'https://github.com/octo/app/issues/7', id.slice(0, 8), id]) {
  test(`runs resolves ${ref} through shared issue lookup`, async t => {
    const f = await fixture(t);
    assert.equal(await runPdd(['workflow', 'runs', ref], f), 0, f.stderr.text);
    assert.match(f.stdout.text, /scope.*done.*start \d{2}:\d{2}:\d{2}.*duration 5s/);
    assert.match(f.stdout.text, /pdd workflow open (?:octo\/)?(?:app#)?7 scope/);
    assert.doesNotMatch(f.stdout.text, /codex resume|170000000/);
  });
}
test('runs without operand includes stages and JSON has human times', async t => {
  const f = await fixture(t);
  assert.equal(await runPdd(['workflow', 'runs'], f), 0);
  assert.match(f.stdout.text, /scope.*done.*session/);
  f.stdout.text = '';
  assert.equal(await runPdd(['workflow', 'runs', '7', '--json'], f), 0);
  assert.equal(JSON.parse(f.stdout.text).stages[0].duration, '5s');
  assert.doesNotMatch(f.stdout.text, /170000000/);
});
test('open confirms warning then reopens the saved session without invoking runner', async t => {
  const f = await fixture(t); let opened = 0;
  f.confirmOpen = async question => { assert.match(question, /octo\/app#7.*Change label/); assert.match(question, /typing could change files after the stage was accepted/i); assert.match(question, /y\/N/); return true; };
  f.reopenSession = async request => { opened++; assert.equal(request.session.id, f.run.steps[0].session.id); assert.equal(request.cwd, f.cwd); return 0; };
  f.workflowRunner = new Proxy({}, { get() { throw Error('must not mutate workflow'); } });
  assert.equal(await runPdd(['workflow', 'open', '7', 'scope'], f), 0, f.stderr.text);
  assert.equal(opened, 1);
});
test('open decline, missing TTY, unknown session and live stage never reopen', async t => {
  for (const variant of ['decline', 'no-tty', 'unknown', 'live', 'missing-stage']) {
    const f = await fixture(t, variant === 'unknown' ? { session: null } : variant === 'live' ? { state: 'running' } : {});
    let confirmations = 0; f.confirmOpen = async () => { confirmations++; return false; };
    f.reopenSession = async () => assert.fail('must not reopen');
    if (variant === 'no-tty') f.stdin.isTTY = false;
    const result = await runPdd(['workflow', 'open', '7', variant === 'missing-stage' ? 'absent' : 'scope'], f);
    assert.equal(result, variant === 'decline' ? 0 : 1, variant);
    assert.equal(confirmations, variant === 'decline' ? 1 : 0, variant);
    if (variant === 'live') assert.match(f.stderr.text, /pdd workflow attach 7/);
  }
});
test('ambiguous issue does not guess or open', async t => {
  const f = await fixture(t);
  f.workflowRecords.readRunIndex = async () => ({ entries: [f.run, { ...f.run, runId: '223e4567-e89b-42d3-a456-426614174000' }] });
  assert.equal(await runPdd(['workflow', 'open', '7', 'scope'], f), 1);
  assert.match(f.stderr.text, /More than one saved run/);
});

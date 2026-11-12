import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { handoffFixture, packageRoot } from './helpers/bounded-area-handoff.mjs';
import { runStatus, askPerson } from '../src/workflow-runner.mjs';

const manifest = JSON.parse(readFileSync(join(packageRoot, 'test/authoring-guidance/bounded-area-handoff-cases.json'), 'utf8'));
const marker = ' … [summary shortened; read ledger]';
const bytes = value => Buffer.byteLength(value, 'utf8');
const preview = text => text.split('\n').find(line => line.startsWith('Approved so far:'));
const clean = value => value.replace(/\s+/g, ' ').trim().replace(/[.\s]+$/, '') || 'done';
const item = (step, summary) => `${step}: ${clean(summary)}`;

function checkRecovery(f, text, needed) {
  const lines = text.split('\n').filter(line => line.includes('Incomplete previews:'));
  assert.equal(lines.length, needed ? 1 : 0, 'exactly one recovery line when a preview is incomplete');
  if (!needed) return;
  const line = lines[0], ledgerPath = join(f.record().runDir, 'status.json');
  assert.ok(line.includes(JSON.stringify(ledgerPath)), 'exact original ledger path is JSON quoted');
  assert.deepEqual(JSON.parse(readFileSync(ledgerPath, 'utf8')).done, f.record().done);
  assert.match(line, /\/done\/STEP\/summary/);
  assert.match(line, /original workflow step name/);
  assert.match(line, /~ as ~0 and \/ as ~1/);
  assert.match(line, /Before relying.*shortened or omitted result, check\/approval claim, unresolved failure or decision.*full entries.*reports\/notes/);
  assert.match(line, /does not establish that failures or decisions are absent/);
  assert.match(line, /cannot identify a safe subset.*read all full earlier summaries/);
  assert.match(line, /cannot establish a check pass or approval/);
}
function checkCapped(actual, original) {
  assert.ok(bytes(actual) <= 1024, 'whole displayed STEP: SUMMARY item must fit 1024 UTF-8 bytes');
  if (bytes(original) <= 1024) { assert.equal(actual, original); return; }
  assert.ok(actual.endsWith(marker), 'oversized item has the exact shortening marker');
  const prefix = actual.slice(0, -marker.length);
  const points = [...prefix], source = [...original];
  assert.equal(prefix, source.slice(0, points.length).join(''), 'prefix preserves exact original code points');
  assert.ok(bytes(prefix + source[points.length] + marker) > 1024, 'prefix is maximal');
  assert.ok(!prefix.includes('\ufffd'), 'no inserted replacement character');
}
async function launch(t, rows, options) {
  const f = await handoffFixture(t, { steps: rows.map(([step]) => step), ...options });
  await f.start();
  for (const [step, summary] of rows) await f.done(step, summary);
  const before = f.record();
  const out = await f.approve(); assert.equal(out.exitCode, 0, out.message);
  assert.deepEqual(f.record().done, before.done, 'formatting keeps complete durable records');
  assert.equal(f.record().decisions.length, before.decisions.length + 1, 'only the explicit approval advances');
  return f;
}
function checkAggregate(f, rows) {
  const text = f.brief(), line = preview(text);
  assert.ok(bytes(line) <= 8192, 'whole Approved so far line must fit 8192 UTF-8 bytes');
  const omission = /\[(\d+) further step summaries omitted; read ledger\]\.$/.exec(line);
  const count = rows.length - (omission ? Number(omission[1]) : 0);
  assert.ok(count >= 0 && count <= rows.length);
  let offset = 'Approved so far: '.length;
  for (let i = 0; i < count; i++) {
    assert.ok(line.startsWith(`${rows[i][0]}: `, offset), 'included steps form the original leading sequence');
    const end = i + 1 < count ? line.indexOf(`; ${rows[i + 1][0]}: `, offset) : omission ? line.indexOf('; [', offset) : line.length - 1;
    assert.ok(end >= offset);
    checkCapped(line.slice(offset, end), item(...rows[i])); offset = end + 2;
  }
  if (omission) {
    assert.equal(Number(omission[1]), rows.length - count, 'omission count includes every remaining completed step');
    const nextOriginal = item(...rows[count]);
    // Fixtures use ASCII summaries here, so a whole original item or its maximal capped prefix is exact.
    const next = bytes(nextOriginal) <= 1024 ? nextOriginal : nextOriginal.slice(0, 1024 - bytes(marker)) + marker;
    const expanded = line.slice(0, line.lastIndexOf(omission[0])) + next + (rows.length - count === 1 ? '.' : `; [${rows.length - count - 1} further step summaries omitted; read ledger].`);
    assert.ok(bytes(expanded) > 8192, 'one more leading capped item cannot fit with the remaining count');
  }
  checkRecovery(f, text, Boolean(omission) || rows.some(row => bytes(item(...row)) > 1024));
  return { line, count };
}

const cases = {
  async 'short-empty-order'(t) {
    const f = await handoffFixture(t, { steps: ['scope', 'inspect', 'blank', 'unfinished'], optional: ['unfinished'] });
    await f.start(); await f.done('current', 'current area is excluded');
    for (const row of [['scope', 'Ready.  '], ['inspect', 'First line\nsecond   line.'], ['blank', '']]) await f.done(...row);
    await f.done('unfinished', 'fixture gate setup'); f.removeDone('unfinished');
    const before = f.record().done;
    { const out = await f.approve(); assert.equal(out.exitCode, 0, out.message); }
    assert.equal(preview(f.brief()), 'Approved so far: scope: Ready; inspect: First line second line; blank: done.');
    assert.deepEqual(f.record().done, before); checkRecovery(f, f.brief(), false);
  },
  async 'no-earlier-summaries'(t) {
    const f = await handoffFixture(t); await f.start();
    assert.equal(preview(f.brief()), undefined); checkRecovery(f, f.brief(), false);
    await f.done('scope', 'fixture gate setup'); f.removeDone('scope');
    { const out = await f.approve(); assert.equal(out.exitCode, 0, out.message); }
    assert.equal(preview(f.brief()), 'Approved so far: no step summaries.'); checkRecovery(f, f.brief(), false);
  },
  async 'item-equality-and-overflow'(t) {
    for (const size of [1021, 1022]) {
      const summary = 'a'.repeat(size), f = await launch(t, [['x', summary]]);
      const actual = preview(f.brief()).slice('Approved so far: '.length, -1);
      checkCapped(actual, `x: ${summary}`); assert.equal(bytes(actual), 1024);
      checkRecovery(f, f.brief(), size === 1022); assert.equal(f.record().done.x.summary, summary);
    }
  },
  async 'unicode-prefix'(t) {
    for (const summary of ['é'.repeat(800), '界'.repeat(800), '😀'.repeat(800), 'a'.repeat(1024 - bytes(marker) - 4) + 'e\u0301' + 'z'.repeat(100)]) {
      const f = await launch(t, [['x', summary]]);
      checkCapped(preview(f.brief()).slice('Approved so far: '.length, -1), `x: ${summary}`); checkRecovery(f, f.brief(), true);
      assert.equal(f.record().done.x.summary, summary);
    }
  },
  async 'aggregate-equality-and-overflow'(t) {
    for (const extra of [0, 1]) {
      const rows = Array.from({ length: 8 }, (_, i) => [`s${i}`, 'a'.repeat((i === 7 ? 992 + extra : 1024) - 4)]);
      const f = await launch(t, rows); const { line, count } = checkAggregate(f, rows);
      assert.equal(count, extra ? 7 : 8); if (!extra) assert.equal(bytes(line), 8192);
    }
  },
  async 'many-steps-and-large-label'(t) {
    const rows = Array.from({ length: 100 }, (_, i) => [i === 0 ? 's'.repeat(64) : `s${i}`, i % 4 === 0 ? `short-${i}` : String(i).padEnd(1500, 'a')]);
    const f = await launch(t, rows); const { count } = checkAggregate(f, rows);
    assert.ok(count < rows.length); assert.ok(f.brief().includes(`${'s'.repeat(64)}: short-0`));
  },
  async 'late-failure-and-report-recovery'(t) {
    const report = 'https://reports.example.invalid/r/late-failure';
    const rows = Array.from({ length: 10 }, (_, i) => [`s${i}`, 'a'.repeat(1500) + (i === 0 ? `\nNot checked: verification unavailable\nReport: ${report}` : i === 9 ? '\nUnresolved failure: approval was not granted' : '')]);
    const f = await launch(t, rows); checkAggregate(f, rows);
    const ledger = JSON.parse(readFileSync(join(f.record().runDir, 'status.json'), 'utf8'));
    assert.ok(ledger.done.s0.summary.includes(`Not checked: verification unavailable\nReport: ${report}`));
    assert.ok(ledger.done.s9.summary.endsWith('Unresolved failure: approval was not granted'));
    assert.ok(!preview(f.brief()).includes(report));
    writeFileSync(join(f.record().runDir, 'verify.md'), `Not checked: verification unavailable\nReport: ${report}\n`);
    assert.ok(readFileSync(join(f.record().runDir, 'verify.md'), 'utf8').includes(report));
  },
  async 'ledger-path-quoting-and-persistence'(t) {
    const summary = 'first line\n' + '界'.repeat(1200) + '\nDecision: await evidence\nReport: https://reports.example.invalid/r/source';
    const f = await launch(t, [['scope', summary]], { buildApproval: true }); checkRecovery(f, f.brief(), true);
    await f.done('current', 'current evidence'); await f.done('finish', 'gate evidence');
    assert.equal((await askPerson({ text: 'Which report should be used?', cwd: f.record().root }, f.ports)).exitCode, 0);
    f.seedPriorPr();
    assert.ok(join(f.record().runDir, 'status.json').includes('"界'));
    const before = f.record(); assert.equal((await f.open({ newSession: true })).exitCode, 0);
    checkRecovery(f, f.brief(), true);
    assert.ok(before.pr.length && before.gate && before.question && before.approvalRecord, 'persistence checks cover populated protected records');
    const after = f.record();
    for (const field of ['done', 'decisions', 'approvalRecord', 'pr', 'gate', 'question']) assert.deepEqual(after[field], before[field], field);
    assert.equal(after.done.scope.summary, summary);
    const pointerValue = JSON.parse(readFileSync(join(after.runDir, 'status.json'), 'utf8')).done.scope.summary;
    assert.equal(pointerValue, summary, '/done/scope/summary resolves to the complete original');
  },
  async 'launch-recovery-and-replacement'(t) {
    const f = await handoffFixture(t, { buildApproval: true }); await f.start(); await f.done('scope', 'a'.repeat(1500));
    const healthy = f.ports.herdr;
    f.ports.herdr = async () => { throw Object.assign(Error('Synthetic channel closed'), { code: 'closed_channel' }); };
    const approval = await f.approve(); assert.equal(approval.exitCode, 1);
    const failed = f.record(); assert.equal(failed.area, 1); assert.ok(failed.chatFailure);
    f.ports.herdr = healthy; assert.equal((await f.open()).exitCode, 0);
    assert.equal(f.record().decisions.length, failed.decisions.length); checkRecovery(f, f.brief(), true);
    await f.done('current', 'Current continuation fact\nNot checked: keep this detail');
    assert.equal((await askPerson({ text: 'Which evidence should the current stage use?', cwd: f.record().root }, f.ports)).exitCode, 0);
    const before = f.record(); assert.equal((await f.open({ newSession: true })).exitCode, 0);
    const text = f.brief(); checkRecovery(f, text, true);
    assert.ok(bytes(preview(text)) <= 8192); assert.match(text, /Completed in this area: current: Current continuation fact\nNot checked: keep this detail/);
    assert.match(text, /Pending question: Which evidence should the current stage use\?/);
    assert.match(text, /Remaining steps: finish/); assert.match(text, /Do not rerun already completed steps/); assert.match(text, /Prior approval does not approve new work/);
    for (const field of ['done', 'decisions', 'approvalRecord', 'pr', 'gate', 'question', 'area']) assert.deepEqual(f.record()[field], before[field], field);
    assert.equal(f.record().chatReplacement.phase, 'launched');
    await f.done('finish', 'gate result');
    const atGate = f.record(); assert.equal((await f.open({ newSession: true })).exitCode, 0);
    assert.match(f.brief(), /Open gate: approve for build/);
    assert.deepEqual(f.record().gate, atGate.gate); assert.deepEqual(f.record().decisions, atGate.decisions);
  },
  async 'unchanged-authority-and-renderers'(t) {
    for (const strict of [false, true]) {
      const summary = 'a'.repeat(1500) + '\nNot checked: no passing evidence';
      const f = await handoffFixture(t, { strict }); await f.start(); await f.done('scope', summary);
      const atGate = f.record();
      const refused = await f.approve({ said: strict ? 'fixture words' : '' }); assert.notEqual(refused.exitCode, 0);
      assert.deepEqual(f.record().done, atGate.done); assert.deepEqual(f.record().decisions, atGate.decisions); assert.equal(f.record().area, 0);
      { const out = await f.approve(); assert.equal(out.exitCode, 0, out.message); } checkRecovery(f, f.brief(), true);
      const status = await runStatus({ ref: '17', cwd: f.source, json: true }, f.ports); assert.equal(status.exitCode, 0);
      assert.ok(!status.message.includes(marker), 'status does not receive clipped preview records');
      assert.equal(f.record().done.scope.summary, summary);
      assert.ok(!f.calls.some(call => call.file === 'git' && call.args[0] === 'push'), 'a preview never publishes');
      writeFileSync(join(f.record().root, 'value.mjs'), 'export const value = 2;\n');
      await f.done('current', 'current work'); await f.done('finish', 'finished');
      assert.equal(f.prs.length, 1);
      assert.ok(f.prs[0].body.includes('Not checked: no passing evidence'), 'PR uses full original earlier summaries');
      assert.ok(!f.prs[0].body.includes(marker), 'PR rendering retains its own contract');
    }
  },
};
for (const vector of manifest.cases) {
  test(`bounded-area-handoff ${vector.id} (${vector.criteria.join(', ')})`, async t => {
    assert.equal(typeof cases[vector.id], 'function', `Not replayed: ${vector.id}`);
    await cases[vector.id](t);
  });
}

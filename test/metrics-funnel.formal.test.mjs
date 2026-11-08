import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { calculateMetrics } from '../src/metrics-model.mjs';

const cutoff = '2026-02-10T00:00:00Z';
const scope = { kind: 'cohort', snapshotId: 'fixed' };
const event = (id, issue, type, data = {}, extra = {}) => ({ schema: 'pdd.metrics.event.v1', id, issue, type, data, repo: 'Org/Repo', at: '2026-02-01T12:00:00Z', observedAt: '2026-02-01T12:00:00Z', source: 'm1', ...extra });
const selection = issue => event(`s${issue}`, issue, 'selection', { snapshotId: 'fixed', inScope: true, state: 'ready' });
const calc = (events, options = {}) => calculateMetrics({ events, repo: 'org/repo', scope, timezone: 'UTC', observedAt: cutoff, sources: ['m1', 'm2'], ...options });
const start = (issue, origin) => event(`start${issue}`, issue, 'start', { origin }, { attempt: `run${issue}` });
const pr = issue => event(`pr${issue}`, issue, 'pr', { pr: 100 + issue, head: 'a' });
const ready = issue => event(`ready${issue}`, issue, 'milestone', { stage: 'implementation-ready', pr: 100 + issue, head: 'a' });
const check = issue => event(`check${issue}`, issue, 'check', { pr: 100 + issue, head: 'a', verdict: 'PASS', reviewer: 'r', evidence: 'link', acceptance: 'accepted' });
const delivery = issue => event(`delivery${issue}`, issue, 'delivery', { explicit: true, evidence: 'link', pr: 100 + issue });

test('bounded independent stage intersections, unknowns, retries and fixed membership', () => {
  // All 32 subsets of independently observed stages for issue 1; issue 2 is manual.
  for (let mask = 0; mask < 32; mask++) {
    const events = [selection(1), selection(2), start(2, 'manual')];
    const stages = [start(1, 'autopilot'), pr(1), ready(1), check(1), delivery(1)];
    stages.forEach((e, bit) => { if (mask & (1 << bit)) events.push(e); });
    const report = calc(events);
    assert.deepEqual(report.issues.map(i => i.issue), [1, 2], `membership mask ${mask}`);
    const issue = report.issues[0];
    const ap = !!(mask & 1), hasPr = !!(mask & (2 | 4 | 8 | 16)), isReady = !!(mask & 4), valid = isReady && !!(mask & 8), delivered = !!(mask & 16);
    const expectations = [
      ['autopilotStarts', [1, 2], ap ? [1] : [], ap ? 1 : 2],
      ['prCreation', ap ? [1] : [], ap && hasPr ? [1] : [], ap && !hasPr ? 1 : 0],
      ['implementationReady', ap ? [1] : [], ap && isReady ? [1] : [], ap && !isReady ? 1 : 0],
      ['validation', isReady ? [1] : [], valid ? [1] : [], isReady && !valid ? 1 : 0],
      ['delivery', valid ? [1] : [], valid && delivered ? [1] : [], valid && !delivered ? 1 : 0],
      ['failedFix', delivered ? [1] : [], [], delivered ? 1 : 0],
    ];
    for (const [name, denominator, numerator, unknown] of expectations) {
      const m = report.transitions[name];
      assert.deepEqual(m.denominatorIssues, denominator, `${name} denominator mask ${mask}`);
      assert.deepEqual(m.issues, numerator, `${name} numerator mask ${mask}`);
      assert.equal(m.unknown, unknown, `${name} unknown mask ${mask}`);
      assert.equal(m.percentage, denominator.length ? numerator.length * 100 / denominator.length : null, `${name} percentage mask ${mask}`);
    }
    assert.equal(issue.delivered, delivered ? 'yes' : 'unknown');
    assert.equal(issue.started, ap ? 'yes' : 'unknown');
    assert.deepEqual(report.coverage.missingSources, ['m2']);
  }
  const duplicate = start(1, 'autopilot');
  const result = calc([selection(1), selection(2), duplicate, {...duplicate, observedAt: '2026-02-02T00:00:00Z'}, start(2, 'unknown'), event('retry', 1, 'start', {origin:'autopilot'}, {attempt:'run-retry'}), pr(1), event('pr2', 1, 'pr', {pr: 999, head:'b'}, {source:'m2'})]);
  assert.deepEqual(result.issues.map(i => i.issue), [1, 2]);
  assert.equal(result.issues[0].starts.length, 2);
  assert.equal(result.transitions.autopilotStarts.numerator, 1);
});

test('candidate supersession and return to old head require new readiness and validation', () => {
  const dated = (e, day) => ({...e, at:`2026-02-0${day}T12:00:00Z`, observedAt:`2026-02-0${day}T12:00:00Z`});
  const base = [selection(1), dated(ready(1), 2), dated(check(1), 3)];
  assert.equal(calc(base).issues[0].validated, 'yes');
  const changed = dated(event('changed', 1, 'candidate', {pr:101, head:'b'}), 4);
  assert.equal(calc([...base, changed]).issues[0].validated, 'unknown');
  const returned = dated(event('returned', 1, 'candidate', {pr:101, head:'a'}), 5);
  assert.equal(calc([...base, changed, returned]).issues[0].validated, 'unknown');
  assert.equal(calc([...base, changed, returned, dated({...ready(1), id:'ready-again'}, 6), dated({...check(1), id:'check-again'}, 7)]).issues[0].validated, 'yes');
});

test('conflicting event facts cannot establish a pass', () => {
  const pass = check(1);
  const fail = {...pass, data: {...pass.data, verdict:'FAIL'}};
  const report = calc([selection(1), ready(1), pass, fail]);
  assert.equal(report.conflicts.length, 1);
  assert.equal(report.issues[0].validated, 'unknown');
  assert.equal(report.transitions.validation.numerator, 0);
});

test('daily start membership uses local calendar boundaries', () => {
  const events = [
    event('before', 1, 'start', {origin:'autopilot'}, {at:'2026-02-02T04:59:59Z'}),
    event('first', 2, 'start', {origin:'manual'}, {at:'2026-02-02T05:00:00Z'}),
    event('last', 3, 'start', {origin:'unknown'}, {at:'2026-02-03T04:59:59Z'}),
    event('after', 4, 'start', {origin:'autopilot'}, {at:'2026-02-03T05:00:00Z'}),
  ];
  const report = calc(events, {scope:{kind:'daily-start', date:'2026-02-02'}, timezone:'America/New_York'});
  assert.deepEqual(report.issues.map(i => i.issue), [2, 3]);
});

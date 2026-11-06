import test from 'node:test';
import assert from 'node:assert/strict';
import { calculateMetrics } from '../src/metrics-model.mjs';

const ev = (id, type, at, data, attempt) => ({schema:'pdd.metrics.event.v1', id, repo:'owner/repo', issue:1, type, at, observedAt:at, source:'machine', data, ...(attempt ? {attempt} : {})});
const day = n => `2026-11-${String(n).padStart(2,'0')}T00:00:00Z`;
const run = (events, observedAt) => calculateMetrics({events, repo:'owner/repo', scope:{kind:'cohort',snapshotId:'s'}, timezone:'UTC', observedAt, sources:['machine']});
const selection = ev('selection','selection',day(1),{snapshotId:'s',inScope:true,state:'ready'});
const delivery = (id, n, pr, attempt) => ev(id,'delivery',day(n),{explicit:true,evidence:'merge',pr},attempt);
const report = (id, n, classification, extra = {}, attempt) => ev(id,'report',day(n),{classification,humanReported:true,evidence:'complaint',...extra},attempt);

test('retry retains earlier human failure and associates later reports with their deliveries', () => {
  const events = [selection,delivery('a',2,10,'a'), report('failure-a',4,'failed-fix',{},'a'),report('admin',5,'administrative'),delivery('b',10,11,'b'),report('failure-b',12,'failed-fix',{},'b'),report('late-a',20,'failed-fix',{pr:10}),report('scope',21,'new-scope'),report('revert',22,'revert'),report('unlinked',23,'failed-fix',{pr:99})];
  const result = run(events,day(25));
  const issue = result.issues[0];
  assert.equal(result.issues.length,1);
  assert.equal(result.transitions.failedFix.numerator,1);
  assert.deepEqual(issue.failedFixReports.map(e => e.id),['failure-a','failure-b','late-a','unlinked']);
  assert.deepEqual(issue.deliveryFollowUps.map(x => x.failedFixReports.map(e => e.id)),[['failure-a','late-a'],['failure-b']]);
  assert.equal(issue.deliveryFollowUps[0].followUp['7'].status,'reported');
  assert.deepEqual(issue.deliveryFollowUps[0].followUp['7'].failedFixReports.map(e => e.id),['failure-a']);
  assert.equal(issue.followUp['7'].status,'reported');
  assert.equal(issue.followUp['30'].mature,false);
});

test('follow-up matures per delivery and an administrative reopen does not count as failure', () => {
  const events = [selection,delivery('a',2,10,'a'),report('admin',3,'administrative'),delivery('b',10,11,'b')];
  const issue = run(events,day(12)).issues[0];
  assert.equal(issue.failedFix,'unknown');
  assert.equal(issue.deliveryFollowUps[0].followUp['7'].status,'no-report-observed');
  assert.equal(issue.deliveryFollowUps[0].followUp['30'].status,'immature');
  assert.equal(issue.followUp['7'].status,'immature');
  assert.deepEqual(issue.failedFixReports,[]);
});

test('a later scope change does not rewrite an earlier prompt-only wait', () => {
  const events = [selection,ev('start','start',day(2),{requiredOutcome:'prompt-only'},'a'),ev('wait','milestone',day(3),{stage:'wait',waitStage:'approval'},'a'),ev('scope','outcome',day(4),{requiredOutcome:'code'},'a')];
  const issue = run(events,day(5)).issues[0];
  assert.equal(issue.requiredOutcome,'code');
  assert.equal(issue.promptOnlyStop,false);
  assert.equal(issue.waits[0].requiredOutcome,'prompt-only');
  assert.equal(issue.waits[0].promptOnlyStop,true);
});
test('issue-level complaint is retained without inventing delivery attribution', () => {
 const issue=run([selection,delivery('a',2,10,'a'),report('known',4,'failed-fix'),report('ambiguous',5,'failed-fix',{humanReported:false})],day(12)).issues[0];
 assert.equal(issue.failedFix,'yes'); assert.deepEqual(issue.failedFixReports.map(e=>e.id),['known']); assert.deepEqual(issue.unassociatedFailedFixReports.map(e=>e.id),['known']); assert.deepEqual(issue.unclassifiedReports.map(e=>e.id),['ambiguous']); assert.deepEqual(issue.deliveryFollowUps[0].failedFixReports,[]); assert.equal(issue.followUp['7'].status,'unknown');
});

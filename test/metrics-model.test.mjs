import test from 'node:test';
import assert from 'node:assert/strict';
import { calculateMetrics } from '../src/metrics-model.mjs';

const event = (id, issue, type, data, at = '2026-11-01T12:00:00Z', source = 'one') => ({ schema: 'pdd.metrics.event.v1', id, repo: 'OWNER/Repo', issue, type, at, observedAt: at, source, data });
const run = (events, scope = { kind: 'cohort', snapshotId: 's' }, observedAt = '2026-12-10T00:00:00Z') => calculateMetrics({events, repo:'owner/repo', scope, timezone:'UTC', observedAt, sources:['one','missing']});

test('fixed membership, retries, stale checks, delivery and follow-up retain independent evidence', () => {
  const rows = [event('sel1',1,'selection',{snapshotId:'s',inScope:true,state:'ready',reasons:[]}),event('sel2',2,'selection',{snapshotId:'s',inScope:true,state:'waiting',reasons:['dependency']}),event('launch',1,'launch',{status:'uncertain',origin:'autopilot'}),event('start',1,'start',{origin:'manual',requiredOutcome:'code'}),event('candidate',1,'milestone',{stage:'implementation-ready',pr:10,head:'new'}),event('old',1,'check',{pr:10,head:'old',verdict:'PASS',reviewer:'checker',evidence:'link',acceptance:'accepted'}),event('delivery',2,'delivery',{pr:10,head:'new',evidence:'link',explicit:true},'2026-11-02T00:00:00Z'),event('report',2,'report',{classification:'failed-fix',humanReported:true,evidence:'complaint'},'2026-11-10T00:00:00Z')];
  const snapshot = structuredClone(rows);
  const report = run([...rows, rows[0]]);
  assert.deepEqual(rows,snapshot);
  assert.equal(report.issues.length,2);
  assert.equal(report.issues[0].started,'yes');
  assert.equal(report.issues[0].validated,'unknown');
  assert.equal(report.issues[1].started,'unknown');
  assert.equal(report.issues[1].delivered,'yes');
  assert.equal(report.issues[1].followUp['7'].status,'no-report-observed');
  assert.equal(report.issues[1].followUp['30'].status,'unknown');
  assert.equal(report.stages.delivered.numerator,1);
  assert.equal(report.stages.delivered.denominator,2);
  assert.deepEqual(report.coverage.missingSources,['missing']);
});

test('conflicting event identity is visible and cannot establish a start', () => {
  const sel = event('sel',1,'selection',{snapshotId:'s',inScope:true,state:'ready'});
  const start = event('same',1,'start',{origin:'manual'});
  const report = run([sel,start,{...start,data:{origin:'autopilot'}}]);
  assert.equal(report.conflicts.length,1);
  assert.equal(report.issues[0].started,'unknown');
});

test('activity uses timezone-local dates and actual starts, zero denominator is null', () => {
  const rows = [event('wake',1,'launch',{status:'confirmed'},'2026-11-02T01:00:00Z'),event('start',1,'start',{origin:'autopilot'},'2026-11-02T02:00:00Z')];
  const report = calculateMetrics({events:rows,repo:'owner/repo',scope:{kind:'activity',date:'2026-11-01'},timezone:'America/New_York',observedAt:'2026-11-03T00:00:00Z',sources:['one']});
  assert.equal(report.activity.starts.count,1);
  assert.equal(run([], {kind:'cohort',snapshotId:'none'}).stages.started.percentage,null);
});

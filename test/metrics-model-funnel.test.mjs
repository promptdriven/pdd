import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { calculateMetrics } from '../src/metrics-model.mjs';
const at = '2026-11-01T00:00:00Z';
const e = (id,issue,type,data,when=at) => ({schema:'pdd.metrics.event.v1',id,repo:'o/r',issue,type,data,at:when,observedAt:when,source:'a'});
const calc = events => calculateMetrics({events,repo:'o/r',scope:{kind:'cohort',snapshotId:'s'},timezone:'UTC',observedAt:'2026-12-10T00:00:00Z',sources:[{source:'a'}, {source:'absent'}]});
test('fixed group transitions use preceding issue membership and retain independent later evidence', () => {
 const events=[e('s1',1,'selection',{snapshotId:'s',inScope:true,state:'ready'}),e('s2',2,'selection',{snapshotId:'s',inScope:false,state:'excluded',reasons:['scope']}),e('start1',1,'start',{origin:'autopilot'}),e('start2',2,'start',{origin:'manual'}),e('ready',1,'milestone',{stage:'implementation-ready',pr:7,head:'a'}),e('pass',1,'check',{pr:7,head:'a',verdict:'PASS',reviewer:'independent',evidence:'link',acceptance:'accepted'}),e('delivery',2,'delivery',{pr:8,explicit:true,evidence:'link'})];
 const r=calc(events); assert.equal(r.transitions.autopilotStarts.numerator,1); assert.equal(r.transitions.autopilotStarts.denominator,1); assert.deepEqual(r.transitions.delivery.denominatorIssues,[1]); assert.equal(r.transitions.delivery.numerator,0); assert.equal(r.stages.delivered.numerator,1); assert.deepEqual(r.coverage.missingSources,['absent']);
});
test('later candidate, duplicate observations, and independent waits preserve evidence', () => {
 const sel=e('s',1,'selection',{snapshotId:'s',inScope:true,state:'ready'}), ready=e('ready',1,'milestone',{stage:'implementation-ready',pr:7,head:'old'});
 const rows=[sel,{...sel,observedAt:'2026-11-02T00:00:00Z'},ready,e('pass',1,'check',{pr:7,head:'old',verdict:'PASS',reviewer:'r',evidence:'link',acceptance:'accepted'}),e('head',1,'milestone',{stage:'head',pr:7,head:'new'},'2026-11-03T00:00:00Z'),e('w1',1,'milestone',{stage:'wait',waitStage:'review',reason:'reviewer'}),e('w2',1,'milestone',{stage:'wait',waitStage:'capacity',reason:'capacity'}),e('resume',1,'milestone',{stage:'resume',waitStage:'review'},'2026-11-04T00:00:00Z')];
 const r=calc(rows); assert.equal(r.conflicts.length,0); assert.equal(r.issues[0].validated,'unknown'); assert.deepEqual(r.waits.map(w=>w.stage),['capacity']);
});
test('readiness uses all eligible Autopilot starts, including those without a PR', () => {
 const rows=[e('s1',1,'selection',{snapshotId:'s',inScope:true,state:'ready'}),e('s2',2,'selection',{snapshotId:'s',inScope:true,state:'ready'}),e('a1',1,'start',{origin:'autopilot'}),e('a2',2,'start',{origin:'autopilot'}),e('r1',1,'milestone',{stage:'implementation-ready',pr:9,head:'abc'})];
 const r=calc(rows); assert.equal(r.transitions.eligibility.numerator,2); assert.equal(r.transitions.eligibility.denominator,2); assert.equal(r.transitions.implementationReady.numerator,1); assert.equal(r.transitions.implementationReady.denominator,2); assert.equal(r.transitions.implementationReady.percentage,50);
});

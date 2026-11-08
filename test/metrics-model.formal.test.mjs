import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { calculateMetrics } from '../src/metrics-model.mjs';

const at = '2026-11-01T00:00:00Z';
const event = (id, issue, type, data, source = 'a', attempt) => ({schema:'pdd.metrics.event.v1', id, repo:'OWNER/Repo', issue, type, at, observedAt:at, source, ...(attempt ? {attempt} : {}), data});
const selection = issue => event(`s${issue}`, issue, 'selection', {snapshotId:'s', inScope:true, state:'ready'});
const run = events => calculateMetrics({events, repo:'owner/repo', scope:{kind:'cohort',snapshotId:'s'}, timezone:'UTC', observedAt:'2026-12-01T00:00:00Z', sources:['a','b']});

test('bounded fixed membership, attempts, machines, PRs and duplicate imports', () => {
  for (let machines=1; machines<=2; machines++) for (let attempts=1; attempts<=2; attempts++) for (let prs=1; prs<=2; prs++) for (let copies=1; copies<=2; copies++) {
    const rows=[selection(1),selection(2)];
    for (let m=0;m<machines;m++) for (let a=0;a<attempts;a++) for (let p=0;p<prs;p++) rows.push(event(`d${m}${a}${p}`,1,'delivery',{pr:10+p,head:`h${p}`,explicit:true,evidence:'proof'},m?'b':'a',`attempt${a}`));
    const report=run(Array.from({length:copies},()=>rows).flat());
    assert.deepEqual(report.issues.map(i=>i.issue),[1,2]);
    assert.equal(report.stages.delivered.numerator,1);
    assert.equal(report.stages.delivered.denominator,2);
    assert.equal(report.issues[1].started,'unknown');
    assert.equal(report.issues[0].deliveries.length,machines*attempts*prs);
  }
});

test('bounded conflicts and stale candidate never establish positive stage', () => {
  for (const type of ['start','delivery','check']) for (const reverse of [false,true]) {
    const candidate=event('candidate',1,'milestone',{stage:'implementation-ready',pr:10,head:'new'});
    const facts = type==='start' ? {origin:'manual'} : type==='delivery' ? {pr:10,head:'new',explicit:true,evidence:'proof'} : {pr:10,head:'new',verdict:'PASS',reviewer:'r',evidence:'proof',acceptance:'accepted'};
    const first=event('conflict',1,type,facts), second={...first,data:{...facts,reason:'different'}};
    const report=run([selection(1),candidate,...(reverse?[second,first]:[first,second])]);
    assert.equal(report.conflicts.length,1);
    assert.equal(report.issues[0][{start:'started',delivery:'delivered',check:'validated'}[type]],'unknown');
  }
  for (const head of ['old','other']) {
    const report=run([selection(1),event('candidate',1,'milestone',{stage:'implementation-ready',pr:10,head:'new'}),event('check',1,'check',{pr:10,head,verdict:'PASS',reviewer:'r',evidence:'proof',acceptance:'accepted'})]);
    assert.equal(report.issues[0].validated,'unknown');
  }
});

test('bounded absent early evidence and empty denominator', () => {
  for (const later of ['none','candidate','delivery']) {
    const rows=[selection(1)];
    if (later==='candidate') rows.push(event('c',1,'milestone',{stage:'implementation-ready',pr:10,head:'h'}));
    if (later==='delivery') rows.push(event('d',1,'delivery',{pr:10,head:'h',explicit:true,evidence:'proof'}));
    const report=run(rows);
    assert.equal(report.issues[0].started,'unknown');
    assert.equal(report.stages.started.numerator,0);
    assert.equal(report.issues[0].delivered,later==='delivery'?'yes':'unknown');
  }
  for (const stage of Object.values(run([]).stages)) {
    assert.equal(stage.denominator,0);
    assert.equal(stage.percentage,null);
  }
});

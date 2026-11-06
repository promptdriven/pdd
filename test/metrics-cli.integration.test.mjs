import {test} from 'node:test';
import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {mkdtempSync,readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join,resolve} from 'node:path';

test('public CLI exports a metrics bundle in a fresh repository', () => {
  const root=mkdtempSync(join(tmpdir(),'pdd-metrics-cli-'));
  const bin=resolve('bin/pdd.mjs');
  execFileSync('git',['init','-q',root]);
  execFileSync('git',['remote','add','origin','https://github.com/example/metrics-test.git'],{cwd:root});
  const output=execFileSync(process.execPath,[bin,'metrics','export','metrics.json','--timezone','UTC'],{cwd:root,encoding:'utf8'});
  assert.match(output,/Exported metrics/);
  const bundle=JSON.parse(readFileSync(join(root,'metrics.json'),'utf8'));
  assert.equal(bundle.repo,'example/metrics-test');
  assert.equal(bundle.timezone,'UTC');
});

test('public terminal and JSON report the same cohort fractions and activity', () => {
  const root=mkdtempSync(join(tmpdir(),'pdd-metrics-report-')), bin=resolve('bin/pdd.mjs');
  execFileSync('git',['init','-q',root]);
  execFileSync('git',['remote','add','origin','https://github.com/example/metrics-test.git'],{cwd:root});
  const at='2026-11-05T00:00:00Z';
  const e=(id,issue,type,data)=>({schema:'pdd.metrics.event.v1',id,repo:'example/metrics-test',issue,type,at,observedAt:at,source:'fixture',data});
  const rows=[e('s1',1,'selection',{snapshotId:'s',inScope:true,state:'ready'}),e('s2',2,'selection',{snapshotId:'s',inScope:true,state:'ready'}),e('a1',1,'start',{origin:'autopilot'}),e('a2',2,'start',{origin:'autopilot'}),e('ready',1,'milestone',{stage:'implementation-ready',pr:9,head:'abc'})];
  const file=join(root,'events.json');
  writeFileSync(file,JSON.stringify(rows));
  execFileSync(process.execPath,[bin,'metrics','record',file],{cwd:root});
  const args=[bin,'metrics','--snapshot','s','--at','2026-11-06T00:00:00Z'];
  const json=JSON.parse(execFileSync(process.execPath,[...args,'--json'],{cwd:root,encoding:'utf8'}));
  const text=execFileSync(process.execPath,args,{cwd:root,encoding:'utf8'});
  assert.equal(json.transitions.implementationReady.numerator,1); assert.equal(json.transitions.implementationReady.denominator,2);
  assert.match(text,/Transition implementationReady: 1\/2 \(50%/); assert.equal(json.activity,null); assert.doesNotMatch(text,/Activity starts:/); assert.match(text,/--date/); assert.match(text,/origins autopilot/);
});

test('public report retains a validated candidate without inventing earlier milestones', () => {
  const root=mkdtempSync(join(tmpdir(),'pdd-metrics-independent-')), bin=resolve('bin/pdd.mjs');
  execFileSync('git',['init','-q',root]);
  execFileSync('git',['remote','add','origin','https://github.com/example/metrics-test.git'],{cwd:root});
  const at='2026-11-05T00:00:00Z';
  const e=(id,type,data)=>({schema:'pdd.metrics.event.v1',id,repo:'example/metrics-test',issue:1,type,data,at,observedAt:at,source:'fixture'});
  const rows=[e('s','selection',{snapshotId:'s',inScope:true,state:'ready'}),e('p','milestone',{stage:'code-pr',pr:9,head:'abc'}),e('c','check',{pr:9,head:'abc',verdict:'PASS',acceptance:'accepted',reviewer:'reviewer',evidence:'https://example.com/check'})];
  const file=join(root,'events.json'); writeFileSync(file,JSON.stringify(rows));
  execFileSync(process.execPath,[bin,'metrics','record',file],{cwd:root});
  const report=JSON.parse(execFileSync(process.execPath,[bin,'metrics','--snapshot','s','--at','2026-11-06T00:00:00Z','--json'],{cwd:root}));
  assert.equal(report.issues[0].validated,'yes');
  assert.equal(report.issues[0].started,'unknown');
  assert.equal(report.issues[0].implementationReady,'unknown');
  assert.equal(report.stages.validated.numerator,1);
  assert.equal(report.transitions.validation.denominator,0);
  assert.equal(report.transitions.validation.percentage,null);
  assert.equal(report.transitions.validation.denominatorUnknown,1);
});


test('historical export backfills only saved completions missing from the run journal', () => {
  const root=mkdtempSync(join(tmpdir(),'pdd-metrics-history-')), bin=resolve('bin/pdd.mjs');
  execFileSync('git',['init','-q',root]);
  execFileSync('git',['remote','add','origin','https://github.com/example/metrics-test.git'],{cwd:root});
  const at='2026-11-05T00:00:00.000Z', other='2026-11-04T00:00:00.000Z';
  const event=(id,step,status,time=at,area='plan')=>({schema:'pdd.metrics.event.v1',id,repo:'example/metrics-test',issue:1,type:'step',at:time,observedAt:time,source:'install:fixture',attempt:'attempt1',data:{step,status,area}});
  const journal=[event('covered','covered','done'),event('changedtime','changedtime','done',other),event('changedstatus','changedstatus','skipped'),event('repeat','covered','skipped')];
  const run={v:1,number:1,repo:'example/metrics-test',runId:'attempt1',done:Object.fromEntries(['covered','partial','changedtime','changedstatus'].map(step=>[step,{at}])),metrics:{events:journal}};
  const dir=join(root,'.git','pdd','runs','1'); mkdirSync(dir,{recursive:true}); writeFileSync(join(dir,'status.json'),JSON.stringify(run));
  const legacyDir=join(root,'.git','pdd','runs','2'); mkdirSync(legacyDir,{recursive:true}); writeFileSync(join(legacyDir,'status.json'),JSON.stringify({v:1,number:2,repo:'example/metrics-test',runId:'attempt2',done:{legacy:{at}}}));
  execFileSync(process.execPath,[bin,'metrics','export','out.json'],{cwd:root});
  const events=JSON.parse(readFileSync(join(root,'out.json'))).events.filter(e=>e.type==='step');
  assert.equal(events.filter(e=>e.source==='install:fixture').length,4);
  assert.deepEqual(events.filter(e=>e.source==='legacy:example/metrics-test').map(e=>e.data.step).sort(),['changedstatus','changedtime','legacy','partial']);
});

test('daily report renders measured activity in terminal and JSON', () => {
  const root=mkdtempSync(join(tmpdir(),'pdd-metrics-day-')), bin=resolve('bin/pdd.mjs');
  execFileSync('git',['init','-q',root]); execFileSync('git',['remote','add','origin','https://github.com/example/metrics-test.git'],{cwd:root});
  const at='2026-11-05T00:00:00Z', file=join(root,'events.json');
  writeFileSync(file,JSON.stringify([{schema:'pdd.metrics.event.v1',id:'start',repo:'example/metrics-test',issue:1,type:'start',at,observedAt:at,source:'fixture',data:{origin:'manual'}}]));
  execFileSync(process.execPath,[bin,'metrics','record',file],{cwd:root});
  const args=[bin,'metrics','--date','2026-11-05','--at','2026-11-06T00:00:00Z'];
  assert.equal(JSON.parse(execFileSync(process.execPath,[...args,'--json'],{cwd:root})).activity.starts.count,1);
  assert.match(execFileSync(process.execPath,args,{cwd:root,encoding:'utf8'}),/Activity starts: 1/);
});

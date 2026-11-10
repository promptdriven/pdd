import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {calculateAutopilotMetrics, parseAutopilotEvidence, renderAutopilotMetrics} from '../src/autopilot-metrics.mjs';

const fixture = JSON.parse(readFileSync(new URL('./fixtures/autopilot-metrics.json', import.meta.url)));
const score = (events=fixture.events, observedAt=fixture.observedAt, timezone='UTC') => calculateAutopilotMetrics({events,observedAt,timezone});
const counts = report => Object.fromEntries(report.rows.map(row=>[row.key,[row.day,row.weekAverage]]));
const line = 'Evidence: runtime=pass (3/3); vectors=pass (2/2); formal=not-run; tests=pass';
const no = {runtime:false,vectors:false,formal:false,tests:false};

test('fixture counts distinct issues across repos, retries, completed days and weekly cohorts',()=>{
  const report=score();
  assert.deepEqual(report.day,{date:'2026-11-10',label:'Tue',start:'2026-11-10T09:00:00.000Z',end:'2026-11-11T09:00:00.000Z'});
  assert.deepEqual(report.week,{label:'Week avg',start:'2026-11-09T09:00:00.000Z',end:'2026-11-11T09:00:00.000Z',finishedDays:2});
  assert.deepEqual(counts(report),{started:[2,1.5],worked:[3,2],runtime:[2,1.5],vectors:[1,1],formal:[1,0.5],validated:[1,0.5],merged:[1,1],regressions:[1,0.5],startedToMerged:[50,2/3*100]});
});

test('evidence allowlist accepts explicit pass only with complete counts when supplied',()=>{
  assert.deepEqual(parseAutopilotEvidence(line),{runtime:true,vectors:true,formal:false,tests:true});
  assert.deepEqual(parseAutopilotEvidence('Evidence: runtime=pass (1/2); vectors=pass (0/0); formal=pass; tests=not-run'),{runtime:false,vectors:false,formal:true,tests:false});
  assert.deepEqual(parseAutopilotEvidence(`Some prose\n${line}\n${line}`),parseAutopilotEvidence(line));
});

test('missing, conflicting, injected or malformed evidence supplies no passes',()=>{
  for(const value of ['', 'Runtime: PASS', line+'; shell=pass', line.replace('runtime=pass','runtime=passed'),line.replace('3/3','4/3'),line.replace('3/3','9007199254740992/9007199254740992'),line.replace('formal=not-run','runtime=pass'),`${line}\n${line.replace('runtime=pass','runtime=fail')}`,'```'+line+'```']) assert.deepEqual(parseAutopilotEvidence(value),no,value);
});

test('validation requires fresh independent review, suite and CI on one exact head',()=>{
  const valid=fixture.events.find(e=>e.kind==='validated');
  for(const change of [e=>{e.validation.review.fresh=false},e=>{e.validation.review.head='b'.repeat(40)},e=>{e.validation.tests.state='fail'},e=>{delete e.validation.ci},e=>{e.validation.ci.head='b'.repeat(40)},e=>{delete e.head}]) {
    const e=structuredClone(valid); change(e); assert.equal(counts(score([e])).validated[0],0);
  }
  assert.equal(counts(score([valid])).validated[0],1);
});

test('only recorded regressions of an earlier Autopilot merge count',()=>{
  const base={repo:'owner/repo',issue:1,at:'2026-11-10T12:00:00Z'};
  const merge={...base,kind:'merged',pr:10}, regression={...base,kind:'regression',at:'2026-11-10T14:00:00Z',pr:10,reason:'reverted'};
  for(const reason of ['reverted','bad-audit','merge-ci-red']) assert.equal(counts(score([merge,{...regression,reason}])).regressions[0],1);
  for(const events of [[regression],[merge,{...regression,pr:11}],[merge,{...regression,reason:'suspected'}],[{...merge,at:'2026-11-10T15:00:00Z'},regression]]) assert.equal(counts(score(events)).regressions[0],0);
});

test('09:00 is inclusive, unfinished days excluded, invalid/future events ignored',()=>{
  const event={repo:'owner/repo',issue:1,kind:'started',at:'2026-11-10T09:00:00Z'};
  const events=[event,{...event,issue:2,at:'2026-11-10T08:59:59.999Z'},{...event,issue:3,at:'2026-11-11T09:00:00Z'},{...event,repo:'../bad'},{...event,issue:0},{...event,issue:4,kind:'manual'},{...event,issue:5,at:'2027-01-01T00:00:00Z'}];
  assert.equal(counts(score(events)).started[0],1);
  assert.equal(counts(score([])).startedToMerged[0],null);
  assert.throws(()=>score([],fixture.observedAt,'invalid/zone'),/Invalid timezone/);
  assert.throws(()=>score([],'bad'),/Invalid cutoff/);
});

test('Monday switches from last week to this week only after the first finished day',()=>{
  const before=score([],'2026-11-09T08:59:59Z'); assert.equal(before.day.label,'Sat'); assert.equal(before.week.label,'Week avg'); assert.equal(before.week.finishedDays,6);
  for(const at of ['2026-11-09T09:00:00Z','2026-11-10T08:59:59Z']) {
    const report=score([],at); assert.equal(report.week.label,'Last week'); assert.equal(report.week.finishedDays,7);
  }
  const monday=score([],'2026-11-09T09:30:00Z'); assert.equal(monday.day.label,'Sun'); assert.equal(monday.week.start,'2026-11-02T09:00:00.000Z');
  assert.equal(score([],'2026-11-10T09:00:00Z').week.finishedDays,1);
});

test('DST and non-hour offsets use calendar 09:00 rather than 24-hour windows',()=>{
  const fall=score([],'2026-11-01T18:00:00Z','America/Los_Angeles');
  assert.equal(fall.day.start,'2026-10-31T16:00:00.000Z'); assert.equal(fall.day.end,'2026-11-01T17:00:00.000Z');
  const spring=score([],'2026-03-08T17:00:00Z','America/Los_Angeles');
  assert.equal(spring.day.start,'2026-03-07T17:00:00.000Z'); assert.equal(spring.day.end,'2026-03-08T16:00:00.000Z');
  const offset=score([],'2026-11-11T04:00:00Z','Asia/Kathmandu'); assert.equal(offset.day.start,'2026-11-10T03:15:00.000Z');
});

test('text table uses the same rows, weekday and week labels as JSON',()=>{
  const text=renderAutopilotMetrics(score());
  assert.match(text,/Tue\s+Week avg/); assert.match(text,/Issues started\s+2\s+1\.5/); assert.match(text,/Started-to-merged %\s+50%\s+66\.67%/);
  assert.match(renderAutopilotMetrics(score([])),/n\/a/);
});

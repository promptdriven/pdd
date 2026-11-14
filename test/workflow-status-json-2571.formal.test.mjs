import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {runStatus} from '../src/workflow-runner.mjs';
import {fixture} from './helpers/workflow-runner-fixture.mjs';

test('bounded status wait precedence and private links', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const initial = f.record(), area = initial.areas[initial.area].name;
  const path = join(f.source, '.git/pdd/runs/17/status.json');
  const ports = {...f.ports, herdr: async () => { throw Error('unavailable'); }};
  const read = async run => {
    writeFileSync(path, JSON.stringify(run));
    const result = await runStatus({cwd:f.source, all:true, json:true}, ports);
    assert.equal(result.exitCode, 0);
    return result.message;
  };
  for (const failure of [false,true]) for (const question of [false,true]) for (const gate of [false,true]) {
    const run = structuredClone(initial);
    run.gate = gate ? {id:'approval',kind:'approve-pr',area,at:1} : null;
    run.question = question ? {text:'Question?',at:2} : null;
    run.chatFailure = failure ? {area,phase:'open',code:'failed',message:'failure',at:3} : null;
    const waiting = JSON.parse(await read(run)).runs[0].waiting;
    const kind = failure ? 'startup_failed' : question ? 'question' : gate ? 'gate' : null;
    assert.deepEqual(waiting, kind === null ? null : {kind, gate:kind === 'gate' ? 'approval' : null, question:kind === 'question' ? 'Question?' : null, reason:null}, `failure=${failure} question=${question} gate=${gate}`);
  }
  const placements = [
    (r,s) => {r.issue.title = s;},
    (r,s) => {r.question = {text:s,at:2};},
    (r,s) => {r.gate = {id:s,kind:'approve-pr',area,at:1};},
    (r,s) => {r.pr = [{number:23,url:s}];},
    (r,s) => {r.chats.at(-1).herdrAgentName = s;},
  ];
  for (const put of placements) for (const prefix of ['', 'context ']) {
    const run = structuredClone(initial), secret = 'https://runtime.example/s/private-token/';
    put(run, prefix + secret);
    const output = await read(run);
    assert.ok(!output.includes(secret), `private link leaked from placement ${placements.indexOf(put)} prefix ${JSON.stringify(prefix)}`);
  }
});

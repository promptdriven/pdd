import test from 'node:test';
import assert from 'node:assert/strict';
import {uptakeFixture,hostname} from './helpers/workflow-uptake-fixture.mjs';
import {writeRun} from '../src/workflow-runs.mjs';
import {renderHelp} from '../src/pdd-cli.mjs';

test('hint uses the running package command',async t=>{const f=await uptakeFixture(t);f.ports.pdd="'/private/running-node' '/private/running-package/bin/pdd.mjs'";assert.equal((await f.change()).exitCode,0);assert.ok(f.sent().at(-1)[3].includes(f.ports.pdd+' workflow ack '));});
for(const state of ['pending','uncertain'])test(`status shows ${state} on a separate line`,async t=>{const f=await uptakeFixture(t);f.save([f.entry('request-'+state,{state})]);for(const options of [{},{ref:undefined},{ref:undefined,all:true}])assert.match((await f.status(options)).message,new RegExp('\\n[^\\n]*request-'+state));});
test('blocked new request stays saved and advice says wait',async t=>{const f=await uptakeFixture(t);f.save([f.entry('blocked-X',{state:'pending',inFlight:true,owner:{pid:654321,hostname:'other-host.invalid',token:'protected'}})]);const result=await f.change('Saved Y');assert.ok(f.read().some(e=>e.text==='Saved Y'&&e.state==='pending'));assert.match(result.message,/your request is (?:kept|saved)/i);assert.match(result.message,/wait/i);assert.doesNotMatch(result.message,/type.*if absent/i);});
test('person receipt formats time while JSON keeps milliseconds',async t=>{const f=await uptakeFixture(t);f.ports.timeZone='America/Los_Angeles';f.save([f.entry('local-clock',{deliveredAt:1793401174126})]);assert.equal((await f.row()).requests[0].deliveredAt,1793401174126);const message=(await f.status()).message;assert.doesNotMatch(message,/1793401174126/);const expected=new Intl.DateTimeFormat('en-US',{month:'short',day:'numeric',hour:'2-digit',minute:'2-digit',hourCycle:'h23',timeZone:'America/Los_Angeles'}).format(new Date(1793401174126));assert.ok(message.includes(expected));});
test('done prefixes every warning line and gives agent appropriate advice',async t=>{const f=await uptakeFixture(t);f.save([f.entry('open-one'),f.entry('open-two')]);const message=(await f.done('reproduce')).message;const lines=message.slice(message.indexOf('warning:')).split('\n');assert.ok(lines.length>=2);assert.ok(lines.every(s=>s.startsWith('warning:')),message);});
test('ack summary is capped at 500 characters',async t=>{const f=await uptakeFixture(t);f.save([f.entry()]);assert.equal((await f.ack('r1','x'.repeat(501))).exitCode,0);assert.equal(f.read()[0].ackSummary.length,500);});
test('ended run list has no permanent unacknowledged warning',async t=>{const f=await uptakeFixture(t);f.save([f.entry()]);const run=f.record();run.state='cancelled';writeRun(run,f.ports);assert.doesNotMatch((await f.status({ref:undefined,cancelled:true})).message,/not yet acknowledged/i);});
test('root help places ack beside done and ask',()=>{const help=renderHelp();const ack=help.indexOf('pdd workflow ack'),done=help.indexOf('pdd workflow done'),ask=help.indexOf('pdd workflow ask');assert.ok(done<ask&&ask<ack);const following=help.slice(ask).split('\n').filter(line=>line.includes('pdd workflow '));assert.ok(following.slice(1,3).some(line=>line.includes('pdd workflow ack ')),'ack stays beside ask among workflow routes');});
test('acknowledged request is quiet in done and text list views',async t=>{const f=await uptakeFixture(t);f.save([f.entry('ACKED-ONLY')]);assert.equal((await f.ack('ACKED-ONLY')).exitCode,0);assert.doesNotMatch((await f.done('unknown')).message,/ACKED-ONLY/);for(const options of [{ref:undefined},{ref:undefined,all:true}])assert.doesNotMatch((await f.status(options)).message,/ACKED-ONLY/);});

test('foreign id belongs to an actual second run and changes neither journal',async t=>{
 const first=await uptakeFixture(t),second=await uptakeFixture(t);
 first.save([first.entry('first-id')]);second.save([second.entry('second-id')]);
 const beforeFirst=first.bytes(),beforeSecond=second.bytes();
 assert.notEqual(first.record().runDir,second.record().runDir);
 assert.notEqual((await first.ack('second-id')).exitCode,0);
 assert.equal(first.bytes(),beforeFirst);assert.equal(second.bytes(),beforeSecond);
 assert.equal((await second.ack('second-id')).exitCode,0);
});

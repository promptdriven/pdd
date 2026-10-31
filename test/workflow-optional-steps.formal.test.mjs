import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {pathToFileURL} from 'node:url';
import {fixture,seedFor,clone,packageRoot,DEFECT} from './workflow-optional-steps.fixture.mjs';
// Bounded oracles authored from workflow-optional-steps.md "Rules to check" before implementation.
// Scope: 64 visual evidence combinations; 361 recorded/native current-answer pairs;
// exact relay with and without current receipt; 256 chooser capability combinations and quote witnesses.
// These assertions call the production runner/helper; no test adapter implements runner policy.
const DECLINE=/^(?:no|skip|skip try|skip it)[.!]?$/i;
function expectedAuthority(recorded,native){
 const eligible=[recorded,native].filter(row=>row&&row.at>1);
 if(!eligible.length)return false;
 const newest=Math.max(...eligible.map(row=>row.at)),latest=eligible.filter(row=>row.at===newest);
 return latest.every(row=>DECLINE.test(row.text.trim()));
}
function alterNote(snapshot,fn){const copy=clone(snapshot);copy.note=copy.note.replace(/```pdd-optional-facts\n([\s\S]*?)\n```/,(_,text)=>'```pdd-optional-facts\n'+JSON.stringify(fn(JSON.parse(text)))+'\n```');return copy;}
test('2756 formal: only current exhaustive complete consistent evidence automatically skips visual (64 assignments)',async t=>{
 const seed=seedFor('server-no-screen'),f=fixture(t,seed.run,{fastStore:true});
 for(const bits of [63,...Array.from({length:63},(_,i)=>i)]){
  const present=Boolean(bits&1),currentBase=Boolean(bits&2),currentRevision=Boolean(bits&4),exhaustive=Boolean(bits&8),complete=Boolean(bits&16),consistent=Boolean(bits&32);
  const snapshot=alterNote(seed.snapshot,x=>({...x,base_sha:currentBase?seed.run.baseSha:'stale-base',revision:currentRevision?0:9,screens:exhaustive?[]:null}));
  if(!present)snapshot.note='';snapshot.complete=complete;
  if(!consistent)snapshot.files.push({path:'unclassifiable.json',text:'{',error:''});
  f.seed(seed.run);f.snapshot=snapshot;const out=await f.done('understand','understood');
  const expected=present&&currentBase&&currentRevision&&exhaustive&&complete&&consistent;
  assert.equal(f.record().done.visual?.summary==='skipped: no screen',expected,`${DEFECT} Formal visual bits=${bits}`);
  assert.equal(out.exitCode,0,DEFECT);assert.equal(f.record().gate,null,DEFECT);assert.deepEqual(f.record().decisions,[],DEFECT);assert.deepEqual(f.record().pr,[],DEFECT);
 }
});
test('2756 formal: newest cross-route current answer governs autonomous try skips; conflicts refuse (361 pairs)',async t=>{
 const seed=seedFor('native-person-no'),f=fixture(t,seed.run,{fastStore:true});
 const replies=[null,...[0,2,3].flatMap(at=>['no','skip','skip it!','skip try.','yes','no thanks'].map(text=>({at,text})))];
 let checked=0;
 for(const recorded of replies)for(const native of replies){
  const run=clone(seed.run);run.changes=recorded?[{stage:'prompt-pr',round:1,answer:true,text:recorded.text,at:recorded.at}]:[];
  f.seed(run);const before=readFileSync(f.statusPath,'utf8'),saves=f.saves;
  f.reply=native?{ok:true,decision:'changes',agent:'codex',sessionId:run.chats[0].session.id,userMessage:native.text,userMessageAt:native.at}:{ok:false,code:'none',message:'none'};
  const out=await f.done('try','skipped: agent proposed'),expected=expectedAuthority(recorded,native);
  const label=`${DEFECT} Formal authority ${JSON.stringify({recorded,native})}`;
  assert.equal(out.exitCode,expected?0:1,label);
  if(expected){assert.equal(f.record().done.try.summary,'skipped by the person',label);assert.equal(f.record().gate,null,label);assert.deepEqual(f.record().decisions,[],label);}
  else {assert.equal(out.message,'Only the person can skip try. Record their answer; do not skip it for them.',label);assert.equal(readFileSync(f.statusPath,'utf8'),before,label);assert.equal(f.saves,saves,label);}
  checked++;
 }
 assert.equal(checked,361);
});
test('2756 formal: explicit current own-chat relay is sufficient without native evidence; no receipt refuses',async t=>{
 const seed=seedFor('own-chat-no-without-herdr'),f=fixture(t,seed.run,{fastStore:true});
 for(const receipt of [true,false]){const run=clone(seed.run);if(!receipt)run.optionalDecisions={};f.seed(run);const reads=f.personReads,before=readFileSync(f.statusPath,'utf8');
  const out=await f.done('try','skipped by the person');assert.equal(out.exitCode,receipt?0:1,DEFECT);assert.equal(f.personReads,reads,DEFECT);
  if(receipt){assert.equal(f.record().done.try.summary,'skipped by the person',DEFECT);assert.equal(f.record().done.try.personAnswer?.via,'relay',DEFECT);assert.deepEqual(f.record().chats,[],DEFECT);}
  else assert.equal(readFileSync(f.statusPath,'utf8'),before,DEFECT);
 }
});
test('2756 formal: command selection, priority, unknowns and one-word Story quoting',async t=>{
 // Production runner witness comes first, so alpha fails by recommendation assertion, never missing import.
 const seed=seedFor('cli-command-and-time'),f=fixture(t,seed.run,{snapshot:seed.snapshot});
 const out=await f.done('check','checked');assert.ok(out.message.includes('Command: `pdd simulate user_stories/cli.md --cli --shell`; time: about 2 minutes.'),DEFECT);
 const {chooseSimulationCommand}=await import(pathToFileURL(join(packageRoot,'src/simulate-command.mjs')));
 let checked=0;
 for(const complete of [false,true])for(const hasDoor of [false,true])for(const cliEntries of [null,0,1,2])for(const httpRoutes of [null,0,1,2])for(const screens of [null,0,1,2]){
  const input={story:'user_stories/example.md',complete,hasDoor,cliEntries,httpRoutes,screens};
  const known=complete&&hasDoor&&[cliEntries,httpRoutes,screens].every(v=>v!==null);
  const kind=!known?'unknown':screens>0?'screen':cliEntries===1?'cli':cliEntries>1?'unknown':httpRoutes>0?'http':'call';
  const actual=chooseSimulationCommand(input),command=kind==='unknown'?'':`pdd simulate user_stories/example.md${kind==='cli'?' --cli --shell':kind==='http'?' --serve':''}`;
  assert.deepEqual(actual,{kind,command,timeHint:kind==='unknown'?'':'about 2 minutes',reason:kind==='unknown'?"PDD cannot determine this Story's runnable interface from current local evidence.":'Story user_stories/example.md has a Simulator door.'},`${DEFECT} Formal chooser ${JSON.stringify(input)}`);checked++;
 }
 assert.equal(checked,256);
 const base={complete:true,hasDoor:true,cliEntries:1,httpRoutes:0,screens:0};
 for(const [story,word] of [["user_stories/a b.md","'user_stories/a b.md'"],["user_stories/a'b.md","'user_stories/a'\\''b.md'"],['user_stories/$(touch nope)`x`.md',"'user_stories/$(touch nope)`x`.md'"]])assert.equal(chooseSimulationCommand({...base,story}).command,`pdd simulate ${word} --cli --shell`,DEFECT);
 for(const story of ['',"bad\npath","bad\rpath","bad\0path"])assert.equal(chooseSimulationCommand({...base,story}).kind,'unknown',DEFECT);
});

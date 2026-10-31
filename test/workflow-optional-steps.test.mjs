import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdirSync,symlinkSync} from 'node:fs';
import {join} from 'node:path';
import {fixture,seedFor,clone,materializeSnapshot,runner,packageRoot,DEFECT} from './workflow-optional-steps.fixture.mjs';
import {integrationFixture} from './workflow-optional-steps.lifecycle-fixture.mjs';
const unknownVisual="PDD cannot determine this change's screens from current scoped facts.";
function facts(snapshot,change){return {...snapshot,note:snapshot.note.replace(/```pdd-optional-facts\n([\s\S]*?)\n```/,(_,json)=>'```pdd-optional-facts\n'+JSON.stringify(change(JSON.parse(json)))+'\n```')};}
for(const id of ['server-no-screen','server-unrelated-map','two-affected-screens-alternate-map','planned-screen-before-files','backend-door-no-app-map','cli-command-and-time','http-command-and-time','screen-only-command-and-time','screen-before-http-command','cli-before-http-command','missing-note','unknown-surfaces','malformed-note','duplicate-fact-blocks','stale-base','stale-revision','stale-source-bytes','missing-existing-scoped-prompt','unreadable-source','conflicting-affected-screen','duplicate-screen-map-row','malformed-enumerated-json','declared-unrelated-screen-not-scoped','drawing-contradicts-no-screen','malformed-scenario','unresolved-scenario-entry','door-refutes-exhaustive-no-simulation'])test(`2756: native default evidence reader ${id}`,async t=>{
 const {run,snapshot,step}=seedFor(id),f=fixture(t,run,{defaultReader:true});materializeSnapshot(f,snapshot,step.input.step==='understand'?'understand.md':'prompt-story.md');
 const out=await f.done(step.input.step,step.input.summary),expected=step.checks.find(c=>c.target==='result'&&c.path==='/message').value;
 assert.equal(out.message,expected,`${DEFECT} Default Git/file evidence must reach the same approved behavior`);
 assert.deepEqual(f.external,[],`${DEFECT} Advice must not execute simulations or open gates`);
});
for(const [name,mutate] of [
 ['unsafe scope parent',s=>facts(s,x=>({...x,scope:[{path:'../outside.prompt.md',planned:true}]}))],
 ['absolute scope',s=>facts(s,x=>({...x,scope:[{path:'/tmp/outside.prompt.md',planned:true}]}))],
 ['secret scope',s=>facts(s,x=>({...x,scope:[{path:'.env',planned:true}]}))],
 ['extra field',s=>facts(s,x=>({...x,unexpected:true}))],
 ['nonboolean planned',s=>facts(s,x=>({...x,scope:x.scope.map(v=>({...v,planned:'true'}))}))],
 ['duplicate scope',s=>facts(s,x=>({...x,scope:[...x.scope,...x.scope]}))],
 ['bad hash',s=>facts(s,x=>({...x,evidence:x.evidence.map(v=>({...v,sha256:'A'.repeat(64)}))}))],
 ['incomplete snapshot',s=>({...s,complete:false})],
 ['read error',s=>({...s,error:'unreadable'})],
 ['malformed JSON inventory',s=>({...s,files:[...s.files,{path:'unclassified.json',text:'{',error:''}]})]
])test(`2756: boundary remains unknown: ${name}`,async t=>{
 const {run,snapshot}=seedFor('server-no-screen'),f=fixture(t,run,{snapshot:mutate(snapshot)});
 const out=await f.done('understand','understood');assert.match(out.message,/Recommended: yes\./,DEFECT);assert.ok(out.message.includes(unknownVisual),`${DEFECT} ${name}`);assert.equal(f.record().done.visual,undefined,DEFECT);
});
for(const kind of ['scope symlink','scope ancestor symlink','note symlink','failed Git enumeration'])test(`2756: default reader refuses ${kind}`,async t=>{
 const {run,snapshot}=seedFor('server-no-screen'),f=fixture(t,run,{defaultReader:true});materializeSnapshot(f,snapshot);
 if(kind==='scope symlink'){const outside=join(f.base,'outside.prompt.md');writeFileSync(outside,snapshot.files.find(x=>x.path==='prompts/api.prompt.md').text);await import('node:fs').then(fs=>fs.unlinkSync(join(f.root,'prompts/api.prompt.md')));symlinkSync(outside,join(f.root,'prompts/api.prompt.md'));}
 if(kind==='scope ancestor symlink'){const outside=join(f.base,'outside');mkdirSync(outside);writeFileSync(join(outside,'api.prompt.md'),snapshot.files.find(x=>x.path==='prompts/api.prompt.md').text);await import('node:fs').then(fs=>fs.rmSync(join(f.root,'prompts'),{recursive:true}));symlinkSync(outside,join(f.root,'prompts'));}
 if(kind==='note symlink'){const outside=join(f.base,'outside.md');writeFileSync(outside,snapshot.note);await import('node:fs').then(fs=>fs.unlinkSync(join(f.runDir,'understand.md')));symlinkSync(outside,join(f.runDir,'understand.md'));}
 if(kind==='failed Git enumeration'){const original=f.ports.execFile;f.ports.execFile=(file,args,opts)=>{if(file==='git'&&args[0]==='ls-files')throw Error('synthetic listing failure');return original(file,args,opts);};}
 const out=await f.done('understand','understood');assert.ok(out.message.includes(unknownVisual),`${DEFECT} ${kind}`);assert.equal(f.record().done.visual,undefined,DEFECT);
});
test('2756: bundled startup guidance, waiting visibility, revision refresh and no-nag gate',async t=>{
 const f=await integrationFixture(t,{name:'feature',agent:'codex'});f.ports.readApprovalEvidence=async()=>({ok:false,code:'none',message:'No synthetic native reply'});assert.equal((await f.run()).exitCode,0);let run=f.record();
 assert.equal(run.optionalPolicy,'pdd.optional-facts.v1',DEFECT);
 const guidance=readFileSync(join(run.runDir,'story-start.md'),'utf8');
 for(const text of ['pdd-optional-facts','base_sha','revision','scope','planned',join(packageRoot,'prompts/cli/workflow-runner.prompt.md')+'#optional-step-decisions',join(run.runDir,'understand.md')])assert.ok(guidance.includes(text),`${DEFECT} Missing author guidance ${text}`);
 assert.doesNotMatch(guidance,/optional: ask the person/,DEFECT);
 const {snapshot}=seedFor('server-no-screen');writeFileSync(join(run.runDir,'understand.md'),snapshot.note.replaceAll('base-2756',run.baseSha));
 for(const file of snapshot.files){mkdirSync(join(run.root,file.path,'..'),{recursive:true});writeFileSync(join(run.root,file.path),file.text);}
 const first=await runner.stepDone({step:'understand',summary:'understood',cwd:run.root,packageRoot},f.agentPorts());assert.ok(first.message.includes('Skipped visual: no screen.'),DEFECT);
 // Ask try through the real runner, with no known facts. Do not cross a real approval or publication boundary.
 run=f.record();run.area=1;run.done={check:{at:1,area:'prompt-pr',summary:'Proactive result https://example.invalid/s/private/'}};run.question=null;run.gate=null;run.state='running';writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
 const question=await runner.stepDone({step:'check',summary:run.done.check.summary,cwd:run.root,packageRoot},f.agentPorts());assert.match(question.message,/Do you want to try it now\? yes\/no Recommended: yes\./,DEFECT);
 const before=f.record(),receipt=clone(before.optionalDecisions.try);f.herdr.idle();
 await runner.openRun({ref:'17',cwd:run.root,packageRoot},f.agentPorts());
 const status=await runner.runStatus({ref:'17',cwd:run.root},f.agentPorts());assert.match(status.message,/Do you want to try it now/,DEFECT);
 assert.deepEqual(f.record().optionalDecisions.try,receipt,DEFECT);assert.equal(f.record().question.text,before.question.text,DEFECT);
 const repeated=await runner.stepDone({step:'check',summary:run.done.check.summary,cwd:run.root,packageRoot},f.agentPorts());assert.equal(repeated.message,'pdd recorded check.\nOptional step try is waiting for your answer.',DEFECT);
 f.tick();const answer=await runner.changeRun({ref:'17',text:'no',cwd:run.root},f.agentPorts());assert.equal(answer.exitCode,0);assert.equal(f.record().optionalRevision??0,0,DEFECT);
 const afterAnswer=await runner.stepDone({step:'check',summary:run.done.check.summary,cwd:run.root,packageRoot},f.agentPorts());assert.doesNotMatch(afterAnswer.message,/Do you want to try it now/,DEFECT);assert.equal(f.record().question,null,DEFECT);
 f.tick();const declined=await runner.stepDone({step:'try',summary:'skipped',cwd:run.root,packageRoot},f.agentPorts());assert.equal(declined.exitCode,0,declined.message);assert.equal(f.record().done.try.summary,'skipped by the person',DEFECT);
 assert.ok(declined.message.includes('The person skipped trying it. Ask them to approve or ask for changes.'),DEFECT);assert.doesNotMatch(declined.message,/Ask them to try it|nothing to try/i,DEFECT);
 assert.ok(f.record().done.check.summary.includes('/s/private/'),DEFECT);assert.deepEqual(f.record().decisions,[],DEFECT);assert.equal(f.prs.length,0,DEFECT);assert.equal(f.record().gate.kind,'approve-pr',DEFECT);
 assert.equal(f.record().waitingFor.what,'The person skipped trying it. Ask them to approve or ask for changes.',`${DEFECT} Saved C3 status must not nag after a decline`);assert.deepEqual(f.record().waitingFor.decisions,['approve','changes'],DEFECT);assert.deepEqual(f.record().resumeDecisions,['approve','changes'],DEFECT);
 f.herdr.idle();const noNag=await runner.runStatus({ref:'17',cwd:run.root},f.agentPorts());assert.doesNotMatch(noNag.message,/try it, then/i,DEFECT);
 f.tick();const changed=await runner.changeRun({ref:'17',text:'add another response',cwd:run.root},f.agentPorts());assert.equal(changed.exitCode,0);assert.equal(f.record().optionalRevision,1,DEFECT);assert.deepEqual(f.record().optionalDecisions,{},DEFECT);
 const refreshed=f.herdr.paneOf(f.record().chats.at(-1)).agent.prompts.at(-1);assert.ok(refreshed.includes('"revision":1'),`${DEFECT} Changed brief guidance must carry the new revision`);
 f.tick();const revised=await runner.stepDone({step:'check',summary:'revised check',cwd:run.root,packageRoot},f.agentPorts());assert.match(revised.message,/Do you want to try it now/,DEFECT);assert.equal(f.record().optionalDecisions.try.revision,1,DEFECT);assert.equal(f.record().done.try,undefined,DEFECT);
});
for(const h1 of ['pdd','NODE','gh','git','0invalid','a'.repeat(65),'unsafe name'])test(`2756: CLI advice does not invent a shell for unsafe H1 ${h1}`,async t=>{
 const {run,snapshot}=seedFor('cli-command-and-time');snapshot.files.find(file=>file.path==='prompts/cli-app.prompt.md').text=snapshot.files.find(file=>file.path==='prompts/cli-app.prompt.md').text.replace(/^# fixture-cli/,`# ${h1}`);
 const f=fixture(t,run,{snapshot});const out=await f.done('check','checked');assert.match(out.message,/Recommended: yes\./,DEFECT);assert.doesNotMatch(out.message,/--cli|--shell/,DEFECT);
});
test('2756: alternate map informs visual but does not select unflagged screen command',async t=>{
 const {run,snapshot}=seedFor('screen-only-command-and-time');const map=snapshot.files.find(file=>file.path==='app-map.json');map.path='maps/alternate.json';
 const changed=facts(snapshot,x=>({...x,screens:x.screens.map(screen=>({...screen,app_map_path:'maps/alternate.json'}))}));
 const f=fixture(t,run,{snapshot:changed}),out=await f.done('check','checked');assert.match(out.message,/Recommended: yes\./,DEFECT);assert.equal(f.lastChooser?.screens,0,`${DEFECT} An alternate map cannot silently select a screen`);
});
test('2756: Story shell metacharacters stay data and adaptive inline command is one line',async t=>{
 const {run,snapshot}=seedFor('cli-command-and-time'),story="user_stories/it' s `story` $(never).md";
 const changed=facts(snapshot,x=>({...x,simulation:x.simulation.map(row=>({...row,story_path:story}))}));
 const old='user_stories/cli.md';changed.files.find(file=>file.path===old).path=story;
 const scenario=changed.files.find(file=>file.path==='test/runtime/cli.json');const doc=JSON.parse(scenario.text);doc.story_path=story;scenario.text=JSON.stringify(doc);
 const f=fixture(t,run,{snapshot:changed}),out=await f.done('check','checked');
 const question=f.record().question?.text;assert.ok(question,DEFECT);assert.equal(question.split('\n').length,1,DEFECT);assert.ok(question.includes("Command: ``pdd simulate 'user_stories/it'\\'' s `story` $(never).md' --cli --shell``; time: about 2 minutes."),`${DEFECT} ${question}`);assert.deepEqual(f.external,[],DEFECT);
});
test('2756: project override stays conservative without policy retrofit',async t=>{
 const f=await integrationFixture(t,{name:'feature',agent:'codex'}),dir=join(f.source,'.agents','skills','pdd-feature');mkdirSync(dir,{recursive:true});
 writeFileSync(join(dir,'workflow.json'),readFileSync(join(packageRoot,'skills/pdd-feature/workflow.json')));
 writeFileSync(join(dir,'SKILL.md'),'# Synthetic project workflow\n');
 assert.equal((await f.run()).exitCode,0);const run=f.record();assert.equal(run.optionalPolicy,undefined,DEFECT);
 const out=await runner.stepDone({step:'understand',summary:'understood',cwd:run.root,packageRoot},f.agentPorts());assert.ok(out.message.includes('Recommended: yes. PDD has no applicability rule for this optional step.'),DEFECT);assert.equal(f.record().done.visual,undefined,DEFECT);
});
for(const limit of ['file-count','byte-count'])test(`2756: oversized evidence snapshot is unknown (${limit})`,async t=>{
 const {run,snapshot}=seedFor('server-no-screen');
 if(limit==='file-count')snapshot.files.push(...Array.from({length:10001},(_,i)=>({path:`data/${i}.json`,text:'{}',error:''})));
 else snapshot.files.push({path:'docs/oversized.txt',text:'x'.repeat(10*1024*1024+1),error:''});
 const f=fixture(t,run,{snapshot}),out=await f.done('understand','understood');assert.ok(out.message.includes(unknownVisual),`${DEFECT} ${limit}`);assert.equal(f.record().done.visual,undefined,DEFECT);
});
for(const shape of ['malformed selected map','scenario criteria mismatch','scenario empty checks','missing prompt interface'])test(`2756: locally invalid evidence stays unknown: ${shape}`,async t=>{
 const {run,snapshot}=seedFor(shape==='malformed selected map'?'server-no-screen':'backend-door-no-app-map');
 if(shape==='malformed selected map')snapshot.files.push({path:'app-map.json',text:'{}',error:''});
 if(shape==='scenario criteria mismatch'){const file=snapshot.files.find(file=>file.path==='test/runtime/api.json'),doc=JSON.parse(file.text);doc.criteria[0].text='Different requirement';file.text=JSON.stringify(doc);}
 if(shape==='scenario empty checks'){const file=snapshot.files.find(file=>file.path==='test/runtime/api.json'),doc=JSON.parse(file.text);doc.steps[0].checks=[];file.text=JSON.stringify(doc);}
 if(shape==='missing prompt interface')snapshot.files.find(file=>file.path==='prompts/api.prompt.md').text='# Missing interface\n';
 const f=fixture(t,run,{snapshot}),step=shape==='malformed selected map'?'understand':'check',out=await f.done(step,step==='understand'?'understood':'checked');assert.match(out.message,/Recommended: yes\./,DEFECT);assert.ok(out.message.includes(shape==='malformed selected map'?unknownVisual:"PDD cannot determine this change's runnable interface from current scoped facts."),`${DEFECT} ${shape}`);assert.equal(f.record().done.visual,undefined,DEFECT);
});

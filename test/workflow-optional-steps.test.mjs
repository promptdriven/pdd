import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdirSync,symlinkSync,chmodSync,existsSync,unlinkSync,truncateSync,lstatSync} from 'node:fs';
import {join,dirname} from 'node:path';
import {spawnSync} from 'node:child_process';
import {pathToFileURL} from 'node:url';
import {fixture,seedFor,clone,materializeSnapshot,runner,packageRoot,DEFECT} from './workflow-optional-steps.fixture.mjs';
import {integrationFixture} from './workflow-optional-steps.lifecycle-fixture.mjs';
const unknownVisual="PDD cannot determine this change's screens from current scoped facts.";
const unknownSimulation="PDD cannot determine this change's runnable interface from current scoped facts.";
const {findTests,preflight,interfaceBlocks,proseSha256,promptRefusal,readPrompt}=await import(pathToFileURL(join(packageRoot,'src/runtime-preflight.mjs')));
// AC4: a real local refusal cannot establish a runnable door. Expected advice is
// specified by the approved unknown-evidence rule, independently of CLI output.
for(const [shape,mutate,refusal] of [
 ['unsupported scenario key',doc=>{doc.unrecognized=true;},'invalid-document'],
 ['another unsupported scenario key',doc=>{doc.future_entry={};},'invalid-document'],
 ['unsupported step key',doc=>{doc.steps[0].unrecognized=true;},'invalid-step'],
 ['blank step model',doc=>{doc.steps[0].model='  ';},'invalid-step-model'],
 ['nonstring step model',doc=>{doc.steps[0].model=3;},'invalid-step-model'],
 ['partial criteria scope',doc=>{doc.criteria_scope=[];},'pdd-partial-test'],
 ['nonempty check exemptions',doc=>{doc.check_exemptions=['AC1'];},'pdd-partial-test'],
 ['malformed check exemptions',doc=>{doc.check_exemptions={};},'pdd-partial-test'],
 ['unsupported criterion key',doc=>{doc.criteria[0].unrecognized=true;},'invalid-criterion'],
 ['missing check path',doc=>{delete doc.steps[0].checks[0].path;},'invalid-check'],
 ['nonlist checks',doc=>{doc.steps[0].checks={};},'invalid-check']
])test(`2756: native CLI rejects door advice for ${shape}`,t=>{
 const {run,snapshot}=seedFor('cli-command-and-time'),f=fixture(t,run,{defaultReader:true});
 const bin=join(f.base,'bin'),tmp=join(f.base,'tmp');mkdirSync(bin);mkdirSync(tmp);
 for(const name of ['gh','herdr','codex','claude','curl','wget']){const path=join(bin,name);writeFileSync(path,'#!/bin/sh\nprintf "%s\\n" "$0 $*" >> "$HOME/blocked-transports"\nexit 91\n');chmodSync(path,0o755);}
 const env={HOME:f.home,TMPDIR:tmp,PATH:bin+':'+dirname(process.execPath)+':/usr/bin:/bin',GIT_CONFIG_NOSYSTEM:'1',GIT_CONFIG_GLOBAL:'/dev/null',PDD_AGENT_SESSION:'1'};
 const cli=()=>{const out=spawnSync(process.execPath,[join(packageRoot,'bin/pdd.mjs'),'workflow','done','check','--summary','checked'],{cwd:f.root,env,encoding:'utf8',timeout:15000});assert.equal(out.error,undefined);assert.equal(out.signal,null);assert.equal(out.status,0,out.stderr);return out.stdout;};
 const local=()=>{const found=findTests({root:f.root});return preflight({root:f.root,found,selected:found.tests}).rows[0].refusals;};
 // Keep supported optional keys and per-check metadata usable. Canonical local
 // preflight deliberately permits additional check fields; this repair does too.
 const file=snapshot.files.find(row=>row.path==='test/runtime/cli.json'),doc=JSON.parse(file.text);
 Object.assign(doc,{entry_paths:['prompts/cli-app.prompt.md'],simulation:{},check_exemptions:[],context:[],context_byte_budget:1024,prompt_mappings:{}});
 doc.steps[0].model='fixture-model';doc.steps[0].checks[0].annotation='allowed check metadata';
 file.text=JSON.stringify(doc);materializeSnapshot(f,snapshot,'prompt-story.md');
 assert.deepEqual(local(),[],`${shape}: valid control must pass canonical preflight`);
 const valid=cli();assert.match(valid,/Recommended: yes\./,DEFECT);
 assert.match(valid,/Command: `pdd simulate user_stories\/cli.md --cli --shell`; time: about 2 minutes\./,DEFECT);
 f.seed(run);mutate(doc);f.put(file.path,JSON.stringify(doc));
 assert.equal(local()[0]?.code,refusal,`${shape}: the same native fixture must be refused locally`);
 const invalid=cli();assert.match(invalid,/Recommended: yes\./,DEFECT);
 assert.doesNotMatch(invalid,/Command:|time:|has a Simulator door/,`${DEFECT} ${shape}: malformed local evidence must not invent a runnable command`);
 assert.ok(invalid.includes(unknownSimulation),`${DEFECT} ${shape}: explain uncertainty`);
 assert.equal(f.record().question.text,`Do you want to try it now? yes/no Recommended: yes. ${unknownSimulation}`,DEFECT);
 assert.equal(f.record().done.try,undefined,DEFECT);assert.equal(f.record().gate,null,DEFECT);
 assert.deepEqual(f.record().chats,[],DEFECT);assert.deepEqual(f.record().decisions,[],DEFECT);assert.deepEqual(f.record().pr,[],DEFECT);
 assert.equal(existsSync(join(f.home,'blocked-transports')),false,'No external transport may be attempted');
});
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

// Repair 2: source-authorized AC4/9 consequences, derived before implementation.
// Calls are repository-root paths, not inferred Markdown dependencies. These
// fixtures intentionally supply no navigation link that could hide a reader gap.
function editOptionalPrompt(file,change) {
 const [block]=interfaceBlocks(file.text),doc=JSON.parse(block[1]);change(doc);
 file.text=file.text.replace(block[1],JSON.stringify(doc));return doc;
}
function calledSnapshot(snapshot,{cycle=false}={}) {
 const parent=snapshot.files.find(row=>row.path==='prompts/cli-app.prompt.md');
 const child={path:'prompts/child.prompt.md',text:parent.text,error:''},leaf={path:'prompts/leaf.prompt.md',text:parent.text,error:''};
 const call=target=>({operation:'dependency',target,target_operation:'main',max_calls:1});
 editOptionalPrompt(parent,doc=>{doc.calls=[call(child.path)];});
 editOptionalPrompt(child,doc=>{doc.conventions=[];doc.calls=[call(leaf.path)];});
 editOptionalPrompt(leaf,doc=>{doc.conventions=[];doc.calls=cycle?[call(parent.path)]:[];});
 snapshot.files.push(child,leaf);return {parent,child,leaf};
}
function nativeOptionalCli(f) {
 const bin=join(f.base,'bin'),tmp=join(f.base,'tmp');mkdirSync(bin);mkdirSync(tmp);
 for(const name of ['gh','herdr','codex','claude','curl','wget']){const path=join(bin,name);writeFileSync(path,'#!/bin/sh\nprintf "%s\\n" "$0 $*" >> "$HOME/blocked-transports"\nexit 91\n');chmodSync(path,0o755);}
 const env={HOME:f.home,TMPDIR:tmp,PATH:bin+':'+dirname(process.execPath)+':/usr/bin:/bin',GIT_CONFIG_NOSYSTEM:'1',GIT_CONFIG_GLOBAL:'/dev/null',PDD_AGENT_SESSION:'1'};
 return ()=>{const out=spawnSync(process.execPath,[join(packageRoot,'bin/pdd.mjs'),'workflow','done','check','--summary','checked'],{cwd:f.root,env,encoding:'utf8',timeout:15000});assert.equal(out.error,undefined);assert.equal(out.signal,null);assert.equal(out.status,0,out.stderr);assert.equal(existsSync(join(f.home,'blocked-transports')),false,'No external transport may be attempted');return out.stdout;};
}
function assertOptionalCli(message) {
 assert.match(message,/Recommended: yes\./,DEFECT);
 assert.match(message,/Command: `pdd simulate user_stories\/cli.md --cli --shell`; time: about 2 minutes\./,DEFECT);
}
function assertOptionalUnknown(f,message) {
 assert.match(message,/Recommended: yes\./,DEFECT);
 assert.doesNotMatch(message,/Command:|time:|has a Simulator door/,`${DEFECT} Incomplete or ambiguous evidence must not advertise a command`);
 assert.match(message,/PDD cannot determine this (?:change|Story)'s runnable interface from current (?:scoped facts|local evidence)\./,DEFECT);
 assert.equal(f.record().question.text,`Do you want to try it now? yes/no Recommended: yes. ${message.includes(unknownSimulation)?unknownSimulation:"PDD cannot determine this Story's runnable interface from current local evidence."}`,DEFECT);
 assert.equal(f.record().done.try,undefined,DEFECT);assert.equal(f.record().gate,null,DEFECT);
 assert.deepEqual(f.record().chats,[],DEFECT);assert.deepEqual(f.record().decisions,[],DEFECT);assert.deepEqual(f.record().pr,[],DEFECT);assert.deepEqual(f.external,[],DEFECT);
}
for(const shape of ['direct input schema','transitive result schema','transitive resource schema','stale child prose','invalid child status','missing child','unresolved called operation','malformed called interface','cycle reaches invalid leaf'])test(`2756: repair2 native CLI checks complete called graph: ${shape}`,t=>{
 const {run,snapshot}=seedFor('cli-command-and-time'),f=fixture(t,run,{defaultReader:true});
 const graph=calledSnapshot(snapshot,{cycle:shape==='cycle reaches invalid leaf'}),cli=nativeOptionalCli(f);
 materializeSnapshot(f,snapshot,'prompt-story.md');
 const found=findTests({root:f.root});assert.deepEqual(preflight({root:f.root,found,selected:found.tests}).rows[0].refusals,[],'Valid transitive/cyclic graph retains native local admission');
 assertOptionalCli(cli());f.seed(run);
 if(shape==='direct input schema')editOptionalPrompt(graph.child,doc=>{doc.entries[0].input_schema.type=['object'];});
 if(['transitive result schema','cycle reaches invalid leaf'].includes(shape))editOptionalPrompt(graph.leaf,doc=>{doc.entries[0].result_schema.type=['object'];});
 if(shape==='transitive resource schema')editOptionalPrompt(graph.leaf,doc=>{doc.resources=[{name:'store',kind:'port',access:'read',operations:[{name:'read',access:'read',arguments_schema:{type:['object']},result_schema:{type:'object',properties:{},required:[],additionalProperties:false}}]}];});
 if(shape==='stale child prose')graph.child.text+='\nChanged required behavior.\n';
 if(shape==='invalid child status')editOptionalPrompt(graph.child,doc=>{doc.status='unknown';});
 if(shape==='unresolved called operation')editOptionalPrompt(graph.child,doc=>{doc.calls[0].target_operation='absent';});
 if(shape==='malformed called interface')graph.child.text='# Missing required interface\n';
 for(const file of [graph.parent,graph.child,graph.leaf])f.put(file.path,file.text);
 if(shape==='missing child')unlinkSync(join(f.root,graph.child.path));
 if(shape.includes('schema') || shape==='cycle reaches invalid leaf') {
  const current=findTests({root:f.root}),refusals=preflight({root:f.root,found:current,selected:current.tests}).rows[0].refusals;
  assert.ok(refusals.some(row=>row.code==='graph-schema-type-list'),'Canonical schema preflight must identify the reachable invalid schema');
 }
 if(['stale child prose','invalid child status','malformed called interface'].includes(shape))assert.ok(promptRefusal(readPrompt(f.root,findTests({root:f.root}).visible,graph.child.path),'dependency'),'Canonical prompt admission rejects the same child');
 assertOptionalUnknown(f,cli());
});
for(const shape of ['parent traversal','secret target','symlink child','ignored child','unreadable child','oversized child'])test(`2756: repair2 default reader retains call read boundary: ${shape}`,async t=>{
 const {run,snapshot}=seedFor('cli-command-and-time'),f=fixture(t,run,{defaultReader:true}),graph=calledSnapshot(snapshot);
 materializeSnapshot(f,snapshot,'prompt-story.md');assertOptionalCli((await f.done('check','checked')).message);f.seed(run);
 let forbidden;
 if(shape==='parent traversal'){forbidden=join(f.root,'..','outside.prompt.md');writeFileSync(forbidden,graph.child.text);editOptionalPrompt(graph.parent,doc=>{doc.calls[0].target='../outside.prompt.md';});}
 if(shape==='secret target'){forbidden=join(f.root,'secrets/private.prompt.md');f.put('secrets/private.prompt.md',graph.child.text);editOptionalPrompt(graph.parent,doc=>{doc.calls[0].target='secrets/private.prompt.md';});}
 if(shape==='symlink child'){forbidden=join(f.root,graph.child.path);const outside=join(f.base,'outside.prompt.md');writeFileSync(outside,graph.child.text);unlinkSync(forbidden);symlinkSync(outside,forbidden);}
 if(shape==='ignored child'){forbidden=join(f.root,graph.child.path);f.put('.gitignore','prompts/child.prompt.md\n');}
 if(shape==='unreadable child')forbidden=join(f.root,graph.child.path);
 if(shape==='oversized child'){forbidden=join(f.root,graph.child.path);truncateSync(forbidden,10*1024*1024+1);}
 f.put(graph.parent.path,graph.parent.text);
 const reads=[];f.ports.optionalFiles={lstatSync,readFileSync:(path,...args)=>{reads.push(path);if(path===forbidden)throw Error('Blocked forbidden dependency read');return readFileSync(path,...args);}};
 assertOptionalUnknown(f,(await f.done('check','checked')).message);
 assert.equal(reads.filter(path=>path===forbidden).length,shape==='unreadable child'?1:0,'Unsafe, invisible and oversized dependencies must be rejected before read');
});
for(const shape of ['safe plus reserved','safe plus malformed','two safe','sole reserved with HTTP','sole malformed with Call'])test(`2756: repair2 CLI candidate selection matches actual adapter: ${shape}`,async t=>{
 const {run,snapshot}=seedFor('cli-command-and-time'),f=fixture(t,run,{defaultReader:true}),parent=snapshot.files.find(row=>row.path==='prompts/cli-app.prompt.md');
 // A repeated step of one entry is one candidate, as in the actual adapter.
 const scenario=snapshot.files.find(row=>row.path==='test/runtime/cli.json'),doc=JSON.parse(scenario.text);doc.steps.push({...clone(doc.steps[0]),step_id:'repeat'});scenario.text=JSON.stringify(doc);
 materializeSnapshot(f,snapshot,'prompt-story.md');assertOptionalCli((await f.done('check','checked')).message);f.seed(run);
 const name=shape.includes('reserved')?'git':shape.includes('malformed')?'unsafe name':'fixture-other';
 const second={path:'prompts/second.prompt.md',text:parent.text.replace('# fixture-cli',`# ${name}`),error:''};
 editOptionalPrompt(second,iface=>{iface.prose_sha256=proseSha256(second.text);});
 if(shape.startsWith('sole')) {
  f.put(parent.path,second.text);
  if(shape==='sole reserved with HTTP') {
   const http=seedFor('http-command-and-time').snapshot.files.find(row=>row.path==='prompts/http-app.prompt.md');
   assert.ok(http,'HTTP preservation fixture');f.put(http.path,http.text);
   const httpScenario=JSON.parse(seedFor('http-command-and-time').snapshot.files.find(row=>row.path==='test/runtime/http.json').text);
   doc.steps.push({...clone(httpScenario.steps[0]),step_id:'http'});scenario.text=JSON.stringify(doc);f.put(scenario.path,scenario.text);
  }
 } else {f.put(second.path,second.text);doc.steps.push({...clone(doc.steps[0]),step_id:'second',entry_path:second.path});f.put(scenario.path,JSON.stringify(doc));}
 const found=findTests({root:f.root});assert.deepEqual(preflight({root:f.root,found,selected:found.tests}).rows[0].refusals,[],'All schemas and source hashes are locally valid');
 const {openCli}=await import(pathToFileURL(join(packageRoot,'src/try-doors.mjs')));let external=0;
 const canary=()=>{external++;assert.fail('CLI selection must refuse before transport, store or shell');};
 await assert.rejects(()=>openCli({root:f.root,visible:found.visible,ports:{shell:canary},runtime:{send:canary},store:{repo:canary}},found.tests[0],'private',{}),shape.startsWith('sole')?/Name the program/:/several CLI entries/);
 assert.equal(external,0,'The actual invalid CLI selection has no external effects');assert.equal(existsSync(join(f.root,'.pdd/try')),false);
 assertOptionalUnknown(f,(await f.done('check','checked')).message);
});

for(const literal of ['1.0','1e0','1.00000000000000001'])test(`2756: repair2 called limits preserve canonical JSON tokens: ${literal}`,t=>{
 const {run,snapshot}=seedFor('cli-command-and-time'),f=fixture(t,run,{defaultReader:true}),graph=calledSnapshot(snapshot),cli=nativeOptionalCli(f);
 materializeSnapshot(f,snapshot,'prompt-story.md');assertOptionalCli(cli());f.seed(run);
 // Positive integer JSON literals have no upper cap in the canonical contract.
 const [block]=interfaceBlocks(graph.child.text),doc=JSON.parse(block[1]);doc.limits.max_steps=1;
 const ordinary=graph.child.text.replace(block[1],JSON.stringify(doc));
 f.put(graph.child.path,ordinary.replace('"max_steps":1',`"max_steps":${literal}`));
 let found=findTests({root:f.root});assert.equal(preflight({root:f.root,found,selected:found.tests}).rows[0].refusals[0]?.code,'invalid-limits','Canonical preflight rejects decimal/exponent tokens even when JSON.parse rounds them to an integer');
 assertOptionalUnknown(f,cli());f.seed(run);
 const huge=ordinary.replace('"max_steps":1','"max_steps":'+'9'.repeat(400));f.put(graph.child.path,huge);
 found=findTests({root:f.root});assert.deepEqual(preflight({root:f.root,found,selected:found.tests}).rows[0].refusals,[],'A large integer literal remains admitted without a new upper bound');
 assertOptionalCli(cli());
});

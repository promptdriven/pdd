import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync, mkdirSync} from 'node:fs';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
import {runPdd} from '../src/pdd-cli.mjs';
import {runCheck} from '../src/runtime-seam.mjs';
import {interfaceBlocks, proseSha256, interfaceSchemaProblems, checkInput} from '../src/runtime/runtime-preflight.mjs';
import {harbor, PLACE, sink, fakeRuntime, portsFor} from './runtime-fake.mjs';

const fixture = name => readFileSync(new URL(`./fixtures/interface-drafting/${name}.prompt.md`,import.meta.url),'utf8');
const parse = text => JSON.parse(interfaceBlocks(text)[0][1]);
const prompt = setup => readFileSync(join(setup.repo,PLACE),'utf8');
const save = (repo, value) => {
  mkdirSync(join(repo,'contracts'),{recursive:true});
  writeFileSync(join(repo,'contracts/draft.json'),JSON.stringify(value));
};
const object = properties => ({type:'object',properties,required:Object.keys(properties),additionalProperties:false});
const entry = operation => ({operation,input_schema:object({value:{type:'number'}}),result_schema:object({text:{type:'string'}}),errors:[]});
const contract = operation => ({entries:[entry(operation)],calls:[],resources:[],limits:{max_steps:4,max_model_calls:2},conventions:[]});
async function draft(setup, args=[]) {
  const stdout=sink(),stderr=sink();
  const code=await runPdd(['interface','draft',PLACE,...args,'--json'],{cwd:setup.repo,stdout,stderr,env:{HOME:setup.home,XDG_CONFIG_HOME:join(setup.home,'.config')},pathDiagnostic:()=>[]});
  return {code,stderr:stderr.text,report:stdout.text ? JSON.parse(stdout.text) : null};
}
function formatter(t,name) {
  const raw=fixture(name),prose=raw.replace(interfaceBlocks(raw)[0][0],'');
  return {prose,setup:harbor(t,repo=>writeFileSync(join(repo,PLACE),prose))};
}
async function admit(t,setup,operation,input,inspect) {
  // Admission exercises the real archive and HTTP boundary. The fake does not prove hosted admission.
  const fake=await fakeRuntime(t,(e,f)=>{
    if(e.command==='lint') {
      const unpack=spawnSync('tar',['-xOf','-',PLACE],{input:e.tar,encoding:'utf8'});
      assert.equal(unpack.status,0);const iface=parse(unpack.stdout);
      assert.equal(iface.status,'draft');assert.equal(Object.hasOwn(iface,'kind'),false);assert.deepEqual(interfaceSchemaProblems(iface),[]);inspect(iface);
    }
    return f.normal(e);
  });
  for(const name of ['place-order','unknown-item']) {
    const file=join(setup.repo,`tests/${name}.json`),doc=JSON.parse(readFileSync(file,'utf8'));
    doc.steps=[{step_id:'draft-admission',entry_path:PLACE,operation,input,checks:doc.criteria.map(c=>({criterion_id:c.id,target:'result',path:operation==='readNote'?'/content':'/text',op:'equals',value:operation==='formatPercent'?'12.50%':operation==='formatBytes'?'1 KiB':'sample'}))}];
    writeFileSync(file,JSON.stringify(doc));
  }
  const {ports}=portsFor({HOME:setup.home,XDG_CONFIG_HOME:join(setup.home,'.config'),PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
  const code=await runCheck({cwd:setup.repo,words:['place-order'],options:{'--lint':true,'--json':true}},ports);
  assert.equal(code,0,ports.stdout.text+ports.stderr.text);
  assert.equal(fake.posts.filter(p=>p.command==='lint').length,1);
  assert.equal(fake.posts.filter(p=>p.command==='check').length,0);
}

test('3130 prose percent drafts an executable number transport and reaches Runtime lint',async t=>{
  const {setup,prose}=formatter(t,'percent'),result=await draft(setup);
  assert.equal(result.code,0,'PROSE_PERCENT_DRAFT_INCOMPLETE');
  const text=prompt(setup),iface=parse(text);
  assert.equal(text.replace(interfaceBlocks(text)[0][0],''),prose);
  assert.equal(iface.prose_sha256,proseSha256(text));assert.equal(Object.hasOwn(iface,'kind'),false);
  const {description:inputDescription,...inputSchema}=iface.entries[0].input_schema;
  const {description:resultDescription,...resultSchema}=iface.entries[0].result_schema;
  assert.deepEqual({...iface.entries[0],input_schema:inputSchema,result_schema:resultSchema},{operation:'formatPercent',input_schema:object({basisPoints:{type:'number'}}),result_schema:object({text:{type:'string'}}),errors:['invalid-basis-points']});
  assert.equal(typeof inputDescription,'string');assert.equal(typeof resultDescription,'string');
  const coverage=result.report.rows[0].prose_coverage;
  assert.ok(coverage.length>0);assert.ok(coverage.every(row=>row.pointers.length>0));
  for(const row of coverage) {
    if(row.pointers.includes('/entries/0/input_schema')) assert.ok(inputDescription.includes(row.sentence));
    if(row.pointers.includes('/entries/0/result_schema')) assert.ok(resultDescription.includes(row.sentence));
  }
  assert.deepEqual(iface.limits,{max_steps:4,max_model_calls:2});
  assert.deepEqual(result.report.rows[0].draft_budget,{source:'command-default',limits:{max_steps:4,max_model_calls:2}});
  assert.equal(JSON.parse(readFileSync(join(setup.repo,'.pdd/interface-drafts.json'),'utf8'))[PLACE].mode,'prose');
  await admit(t,setup,'formatPercent',{basisPoints:1250},i=>assert.equal(i.entries[0].input_schema.properties.basisPoints.type,'number'));
});

test('3130 prose bytes preserves all six rejection transport shapes through Runtime lint',async t=>{
  const {setup,prose}=formatter(t,'bytes'),result=await draft(setup);
  assert.equal(result.code,0,'PROSE_BYTES_DRAFT_INCOMPLETE');
  const text=prompt(setup),iface=parse(text),input=iface.entries[0].input_schema;
  assert.equal(text.replace(interfaceBlocks(text)[0][0],''),prose);
  assert.deepEqual(input.properties.bytes.oneOf.map(s=>s.type),['number','string','boolean','null','array','object']);
  for(const bytes of [0,1536,1.5,-1,'1024',true,null,[1],{}]) assert.deepEqual(checkInput({bytes},input,0).refusals,[]);
  assert.deepEqual(iface.entries[0].errors,['invalid-bytes']);
  await admit(t,setup,'formatBytes',{bytes:1536},i=>assert.equal(i.entries[0].input_schema.properties.bytes.oneOf.length,6));
});

test('3130 missing facts have field questions and a complete contract recovery command',async t=>{
  const setup=harbor(t,repo=>{
    writeFileSync(join(repo,PLACE),'# Unclear\n\nExport `measure(value)`.\n');save(repo,contract('measure'));
  });
  const first=await draft(setup);assert.equal(first.code,4);
  const row=first.report.rows[0];assert.ok(row.questions?.length,'MISSING_FIELD_QUESTIONS');
  for(const field of ['input_schema','result_schema','errors']) assert.ok(row.questions.some(q=>q.pointer===`/entries/0/${field}`));
  for(const field of ['calls','resources','limits']) assert.ok(row.questions.some(q=>q.pointer===`/${field}`));
  assert.ok(row.next_step.includes('--contract'));
  const recovery=row.next_step.split(' ').slice(4).map(word=>word==='FILE'?'contracts/draft.json':word);
  const second=await draft(setup,recovery);
  assert.equal(second.code,0,second.stderr);assert.equal(Object.hasOwn(parse(prompt(setup)),'kind'),false);
  assert.equal(Object.hasOwn(parse(prompt(setup)),'draft_gaps'),false);
});

test('3130 explicit effect ports retain resource schemas and reach Runtime lint',async t=>{
  const raw=readFileSync(new URL('../examples/fakes/files.prompt.md',import.meta.url),'utf8'),source=parse(raw);
  const setup=harbor(t,repo=>{writeFileSync(join(repo,PLACE),raw.replace(interfaceBlocks(raw)[0][0],''));save(repo,source);});
  const result=await draft(setup,['--contract','contracts/draft.json']);
  assert.equal(result.code,0,'EFFECT_CONTRACT_ROUTE_UNAVAILABLE');
  assert.deepEqual(parse(prompt(setup)).resources,source.resources);
  await admit(t,setup,'readNote',{path:'/notes/a.txt'},i=>assert.deepEqual(i.resources,source.resources));
});

test('3130 extend adds an operation and preserves every approved declaration',async t=>{
  const setup=harbor(t,repo=>save(repo,{entries:[entry('second')]})),before=parse(prompt(setup));
  const result=await draft(setup,['--extend','--contract','contracts/draft.json']);
  assert.equal(result.code,0,'APPROVED_EXTENSION_ROUTE_UNAVAILABLE');
  const after=parse(prompt(setup));assert.equal(after.status,'draft');
  assert.deepEqual(after.entries,[...before.entries,entry('second')]);
  for(const field of ['calls','resources','limits','conventions']) assert.deepEqual(after[field],before[field]);
  const saved=prompt(setup),conflict={...before.entries[0],errors:['changed']};
  save(setup.repo,{entries:[conflict]});
  const refused=await draft(setup,['--extend','--contract','contracts/draft.json']);
  assert.equal(refused.code,4);assert.equal(refused.report.rows[0].problems[0].section,'/entries/0');
  assert.equal(prompt(setup),saved);
  const provenance=JSON.parse(readFileSync(join(setup.repo,'.pdd/interface-drafts.json'),'utf8'))[PLACE];
  assert.equal(provenance.mode,'extend');
});

test('3130 extension retains call and effect bindings and refuses limit changes atomically',async t=>{
  const setup=harbor(t,repo=>save(repo,{entries:[entry('network')],resources:[{name:'http',kind:'port',access:'read',operations:[{name:'get',access:'read',arguments_schema:object({url:{type:'string'}}),result_schema:object({body:{type:'string'}})}]}]}));
  const result=await draft(setup,['--extend','--contract','contracts/draft.json']);
  assert.equal(result.code,0,'EFFECT_EXTENSION_ROUTE_UNAVAILABLE');
  const saved=prompt(setup);assert.equal(parse(saved).resources[0].name,'http');
  save(setup.repo,{entries:[entry('third')],limits:{max_steps:99,max_model_calls:2}});
  const refusal=await draft(setup,['--extend','--contract','contracts/draft.json']);
  assert.equal(refusal.code,4);assert.equal(refusal.report.rows[0].problems[0].section,'/limits');assert.equal(prompt(setup),saved);
});

test('3130 refresh explicitly reopens a stale approved block without changing its declarations',async t=>{
  const setup=harbor(t),before=parse(prompt(setup));
  writeFileSync(join(setup.repo,PLACE),'# Changed prose\n'+prompt(setup));
  const prose=prompt(setup).replace(interfaceBlocks(prompt(setup))[0][0],'');
  const result=await draft(setup,['--refresh']);assert.equal(result.code,0,'STALE_REFRESH_ROUTE_UNAVAILABLE');
  const after=parse(prompt(setup));assert.equal(after.status,'draft');assert.equal(after.prose_sha256,proseSha256(prompt(setup)));
  assert.deepEqual({...after,status:before.status,prose_sha256:before.prose_sha256},before);
  assert.equal(prompt(setup).replace(interfaceBlocks(prompt(setup))[0][0],''),prose);
});

test('3130 complete replacement updates a changed interface only on explicit refresh',async t=>{
  const setup=harbor(t,repo=>save(repo,contract('replacement'))),before=prompt(setup);
  const noRefresh=await draft(setup,['--contract','contracts/draft.json']);
  assert.equal(noRefresh.code,4,'EXISTING_CONTRACT_MUST_REQUIRE_EXPLICIT_ROUTE');assert.equal(prompt(setup),before);
  const replaced=await draft(setup,['--refresh','--contract','contracts/draft.json']);assert.equal(replaced.code,0);
  assert.equal(parse(prompt(setup)).entries[0].operation,'replacement');assert.equal(parse(prompt(setup)).status,'draft');
});

test('3130 rejected contract identifies the field rule before any prompt mutation',async t=>{
  const invalid=contract('bad');invalid.entries[0].input_schema.properties.value={type:['number','string']};
  const setup=harbor(t,repo=>{writeFileSync(join(repo,PLACE),'# Draft\n');save(repo,invalid);}),before=prompt(setup);
  const result=await draft(setup,['--contract','contracts/draft.json']);
  assert.equal(result.code,4,'CONTRACT_FIELD_DIAGNOSTIC_UNAVAILABLE');
  assert.equal(result.report.rows[0].problems[0].section,'/entries/0/input_schema/properties/value');
  assert.ok(result.report.rows[0].problems[0].rule);assert.equal(prompt(setup),before);
});

for(const [extra,pointer] of [
  ['It also writes an audit log to disk.','/resources'],
  ['The result also has required boolean `ok`.','/entries/0/result_schema'],
  ['The input has required string `locale`.','/entries/0/input_schema'],
  ['The operation sends telemetry to a remote service.','/resources'],
  ['An `ok` flag is included in the result.','/entries/0/result_schema'],
]) test(`3130 extra prose declarations require an explicit answer at ${pointer}`,async t=>{
  const raw=fixture('percent'),prose=raw.replace(interfaceBlocks(raw)[0][0],'');
  const setup=harbor(t,repo=>writeFileSync(join(repo,PLACE),prose.replace('## Percentage format',extra+'\n\n## Percentage format')));
  const result=await draft(setup);
  assert.equal(result.code,4,'EXTRA_PROSE_FACTS_MUST_NOT_BE_DROPPED');
  assert.ok(result.report.rows[0].questions?.some(q=>q.pointer===pointer),'UNRESOLVED_PROSE_FIELD_QUESTION_MISSING');
});

for(const [field,value,pointer] of [
  ['resources',[{name:'disk'}],'/resources/0/kind'],
  ['resources',[{name:'disk',kind:'blob',access:'read',operations:[{name:'read',access:'read'}]}],'/resources/0/operations/0/arguments_schema'],
  ['resources',[{name:'disk',kind:'blob',access:'read',operations:[{name:'write',access:'write',arguments_schema:object({}),result_schema:object({})}]}],'/resources/0/operations/0/access'],
  ['calls',[{operation:'quote'}],'/calls/0/target'],
  ['calls',[{operation:'quote',target:'prompts/pricing.prompt.md'}],'/calls/0/target_operation'],
  ['calls',[{operation:'quote',target:'prompts/pricing.prompt.md',target_operation:'quote'}],'/calls/0/max_calls'],
]) test(`3130 incomplete effect binding fails before writes at ${pointer}`,async t=>{
  const supplied=contract('effect');supplied[field]=value;
  const setup=harbor(t,repo=>{writeFileSync(join(repo,PLACE),'# Effect\n');save(repo,supplied);}),before=prompt(setup);
  const result=await draft(setup,['--contract','contracts/draft.json']);
  assert.equal(result.code,4,'INCOMPLETE_BINDING_ADMITTED');
  assert.equal(result.report.rows[0].problems[0].section,pointer);assert.equal(prompt(setup),before);
});

test('3130 prompt call extension uses the public operation binding and preserves existing entries',async t=>{
  const call={operation:'quote',target:'prompts/pricing.prompt.md',target_operation:'quote',max_calls:1};
  const setup=harbor(t,repo=>save(repo,{entries:[entry('caller')],calls:[call]})),before=parse(prompt(setup));
  const result=await draft(setup,['--extend','--contract','contracts/draft.json']);
  assert.equal(result.code,0,'PROMPT_CALL_EXTENSION_UNAVAILABLE');
  const after=parse(prompt(setup));assert.deepEqual(after.entries[0],before.entries[0]);assert.deepEqual(after.calls,[call]);
});


test('3130 contract route preserves factory and method handle bindings',async t=>{
  const raw=readFileSync(new URL('../examples/fakes/factory.prompt.md',import.meta.url),'utf8'),supplied=parse(raw);
  const setup=harbor(t,repo=>{writeFileSync(join(repo,PLACE),raw.replace(interfaceBlocks(raw)[0][0],''));save(repo,supplied);});
  const result=await draft(setup,['--contract','contracts/draft.json']);
  assert.equal(result.code,0,'INSTANCE_BINDING_DRAFT_UNAVAILABLE');
  const iface=parse(prompt(setup));assert.deepEqual(iface.entries,supplied.entries);assert.deepEqual(iface.resources,supplied.resources);
});

for(const [convention,pointer] of [[42,'/conventions/0'],[{},'/conventions/0/path'],[{path:'/entries/9',convention:'cli'},'/conventions/0/path']])
  test(`3130 malformed convention is rejected before writes at ${pointer}`,async t=>{
    const supplied=contract('typed');supplied.conventions=[convention];
    const setup=harbor(t,repo=>{writeFileSync(join(repo,PLACE),'# Typed\n');save(repo,supplied);}),before=prompt(setup);
    const result=await draft(setup,['--contract','contracts/draft.json']);
    assert.equal(result.code,4,'MALFORMED_CONVENTION_ADMITTED');assert.equal(result.report.rows[0].problems[0].section,pointer);assert.equal(prompt(setup),before);
  });

test('3130 resource ports retain unions of closed object variants',async t=>{
  const schema={oneOf:[object({url:{type:'string'}}),object({id:{type:'integer'}})]};
  const supplied=contract('lookup');supplied.resources=[{name:'service',kind:'port',access:'read',operations:[{name:'lookup',access:'read',arguments_schema:schema,result_schema:object({text:{type:'string'}})}]}];
  const setup=harbor(t,repo=>{writeFileSync(join(repo,PLACE),'# Lookup\n');save(repo,supplied);});
  const result=await draft(setup,['--contract','contracts/draft.json']);assert.equal(result.code,0,'CLOSED_OBJECT_UNION_REFUSED');assert.deepEqual(parse(prompt(setup)).resources,supplied.resources);
});

test('3130 printed recovery command works from a subdirectory',async t=>{
  const setup=harbor(t,repo=>{writeFileSync(join(repo,PLACE),'# Unclear\n\nExport `measure(value)`.\n');save(repo,contract('measure'));});
  const invoke=async args=>{
    const stdout=sink(),stderr=sink();
    const code=await runPdd(args,{cwd:join(setup.repo,'prompts'),stdout,stderr,env:{HOME:setup.home,XDG_CONFIG_HOME:join(setup.home,'.config')}});
    return {code,out:stdout.text,err:stderr.text};
  };
  const first=await invoke(['interface','draft','place_order.prompt.md','--json']);assert.equal(first.code,4);
  const row=JSON.parse(first.out).rows[0];assert.ok(row.next_step,'SUBDIRECTORY_RECOVERY_MISSING');
  const args=row.next_step.split(' ').slice(1).map(word=>word==='FILE'?'../contracts/draft.json':word);
  const recovered=await invoke([...args,'--json']);assert.equal(recovered.code,0,'PRINTED_SUBDIRECTORY_RECOVERY_FAILED');
  assert.equal(parse(prompt(setup)).entries[0].operation,'measure');
});

for (const extra of [
  'The input object must contain a string `locale`.',
  'A file audit record is created on disk.',
  'Compliance records persist after each invocation.',
]) test(`3130 repair 1: unmapped prose stays partial: ${extra}`, async t => {
  const {setup,prose}=formatter(t,'percent');
  writeFileSync(join(setup.repo,PLACE),prose.replace('## Percentage format',extra+'\n\n## Percentage format'));
  const first=await draft(setup), row=first.report.rows[0];
  assert.equal(first.code,4,'UNMAPPED_SENTENCE_ACCEPTED_AS_COMPLETE');
  assert.equal(parse(prompt(setup)).kind,'partial');
  assert.ok(Array.isArray(row.prose_coverage),'SENTENCE_COVERAGE_MISSING');
  assert.deepEqual(row.prose_coverage.find(c=>c.sentence===extra)?.pointers,[]);
  assert.equal(row.questions.filter(q=>q.question.includes(extra)).length,1,'UNMAPPED_SENTENCE_QUESTION_COUNT');
  assert.ok(row.next_step?.includes('--refresh --contract'));
  const saved=prompt(setup), second=await draft(setup);
  assert.equal(second.code,4);assert.equal(prompt(setup),saved);
  assert.deepEqual(second.report.rows[0].questions,row.questions,'REPEATED_DRAFT_QUESTIONS_CHANGED');
});

test('3130 repair 1: authored gaps have recovery on the first and repeated draft',async t=>{
  const value={...contract('measure'),kind:'partial',draft_gaps:['Choose whether locale is required.']};
  const setup=harbor(t,repo=>writeFileSync(join(repo,PLACE),'# Contract\n\n```json\n'+JSON.stringify(value)+'\n```\n'));
  const first=await draft(setup),row=first.report.rows[0],saved=prompt(setup);
  assert.equal(first.code,4);assert.ok(row.questions?.some(q=>q.question.includes(value.draft_gaps[0])),'AUTHORED_GAP_QUESTION_MISSING');
  assert.ok(row.next_step?.includes('--refresh --contract'));
  const second=await draft(setup);assert.equal(second.code,4);assert.equal(prompt(setup),saved);
  assert.deepEqual(second.report.rows[0].questions,row.questions,'AUTHORED_GAP_DID_NOT_CONVERGE');
});

for(const schema of [{type:['number','string']},{type:'object',properties:[],required:[],additionalProperties:false}])
  test(`3130 repair 1: invalid inferred schema has actionable recovery ${JSON.stringify(schema)}`,async t=>{
    const value=contract('measure');value.entries[0].input_schema=schema;
    const setup=harbor(t,repo=>writeFileSync(join(repo,PLACE),'# Contract\n\n```json\n'+JSON.stringify(value)+'\n```\n'));
    const first=await draft(setup),row=first.report.rows[0];
    assert.equal(first.code,4);assert.ok(row.questions?.length,'INVALID_INFERRED_SCHEMA_HAS_NO_QUESTIONS');
    assert.ok(row.next_step?.includes('--contract'),'INVALID_INFERRED_SCHEMA_HAS_NO_RECOVERY');
    const saved=prompt(setup), second=await draft(setup);
    assert.equal(second.code,4);assert.equal(prompt(setup),saved);
    assert.deepEqual(second.report.rows[0].questions,row.questions);
  });

test('3130 repair 1: compact approved extension keeps bytes and discloses full reapproval with a diff',async t=>{
  for(const committed of [true,false]) {
  const setup=harbor(t,repo=>{
    const file=join(repo,PLACE),raw=readFileSync(file,'utf8'),block=interfaceBlocks(raw)[0],value=JSON.parse(block[1]);
    if(!committed) value.status='draft';
    writeFileSync(file,raw.replace(block[1],JSON.stringify(value)));
    save(repo,{entries:[entry('second')]});
  });
  if(!committed) writeFileSync(join(setup.repo,PLACE),prompt(setup).replace('"status":"draft"','"status":"approved"'));
  const before=prompt(setup),oldBody=interfaceBlocks(before)[0][1],old=parse(before),oldEntryBytes=JSON.stringify(old.entries[0]);
  const result=await draft(setup,['--extend','--contract','contracts/draft.json']),row=result.report.rows[0];
  assert.equal(result.code,0);assert.ok(prompt(setup).includes(oldEntryBytes),'APPROVED_ENTRY_BYTES_CHANGED');
  assert.equal(row.approval_scope,'whole-interface','GLOBAL_STATUS_SCOPE_NOT_DISCLOSED');
  assert.equal(row.interface_diff?.before,oldBody);
  assert.equal(row.interface_diff?.after,interfaceBlocks(prompt(setup))[0][1]);
  assert.ok(row.interface_diff.unchanged.includes('/entries/0'));
  const {runApprove}=await import('../src/prompt-approve.mjs');
  const {Readable}=await import('node:stream');
  const stdout=sink(),stderr=sink();
  const code=await runApprove({words:[PLACE],cwd:setup.repo},{stdout,stderr,stdin:Readable.from(['n\n']),interactive:true});
  assert.equal(code,1,stderr.text);
  assert.match(stdout.text,/whole interface.*re-approv/i);
  assert.ok(stdout.text.includes(oldEntryBytes),'APPROVAL_DIFF_LOST_OLD_BYTES');
  assert.ok(stdout.text.includes('second'),'APPROVAL_DIFF_LOST_ADDITION');
  assert.match(stdout.text,/unchanged.*\/entries\/0/i);
  assert.equal(parse(prompt(setup)).status,'draft');
  if(!committed) assert.match(stdout.text,/before extension/i);
  }
});

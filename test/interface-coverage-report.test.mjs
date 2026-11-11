import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdirSync,existsSync} from 'node:fs';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
import {Readable} from 'node:stream';
import {runApprove} from '../src/prompt-approve.mjs';
import {interfaceBlocks} from '../src/runtime/runtime-preflight.mjs';
import {harbor,PLACE,sink,root} from './runtime-fake.mjs';

const raw=readFileSync(new URL('./fixtures/interface-drafting/percent.prompt.md',import.meta.url),'utf8');
const original=JSON.parse(interfaceBlocks(raw)[0][1]);
const prose=raw.replace(interfaceBlocks(raw)[0][0],'');
const formatting='Show the exact rate with two decimal digits and a trailing `%`, without spaces or grouping separators.';
const numberClaims=['It takes a Number of basis points and returns a string.','Accept a Number only if it is a safe integer.'];
const block=value=>'<details><summary>Runtime interface</summary>\n\n```json\n'+JSON.stringify(value)+'\n```\n</details>';
const fence=value=>'\n## Public schema\n\n```json\n'+JSON.stringify(value)+'\n```\n';
const extra={...original.entries[0],operation:'second'};
function setup(t,text,files={}) {
  return harbor(t,repo=>{
    writeFileSync(join(repo,PLACE),text);mkdirSync(join(repo,'contracts'),{recursive:true});
    for(const [path,value] of Object.entries(files)) writeFileSync(join(repo,path),typeof value==='string'?value:JSON.stringify(value));
  });
}
function draft(f,args=[],timeout) {
  const r=spawnSync(process.execPath,[join(root,'bin/pdd.mjs'),'interface','draft',PLACE,...args,'--json'],{
    cwd:f.repo,encoding:'utf8',timeout,killSignal:'SIGKILL',env:{...process.env,HOME:f.home,PDD_STATE_DIR:f.state}
  });
  assert.equal(r.signal,null);assert.ok(r.stdout,r.stderr);
  const report=JSON.parse(r.stdout),text=readFileSync(join(f.repo,PLACE),'utf8');
  return {code:r.status,row:report.rows[0],text,iface:JSON.parse(interfaceBlocks(text)[0][1])};
}
function at(value,pointer) {
  return pointer.split('/').slice(1).reduce((value,key)=>value?.[key.replaceAll('~1','/').replaceAll('~0','~')],value);
}
function retained(result,row) {
  assert.equal(row.status,'mapped','RETAINED_MEANING_NOT_REPORTED');
  assert.ok(row.mappings.length);
  assert.deepEqual(row.pointers,row.mappings.map(item=>item.pointer));
  for(const mapping of row.mappings) assert.deepEqual(at(result.iface,mapping.pointer),mapping.meaning,'MAPPING_POINTS_AT_DIFFERENT_MEANING');
}
for(const route of ['embedded','dependency','import','refresh','extend']) {
  test('3130 integration: JSON formatting needs review without changing authored fields: '+route,t=>{
    let text=prose,args=[];
    if(route==='embedded') text+=fence(original);
    if(route==='dependency') text=text.replace('## Dependencies\n\nNone.','## Dependencies\n\n[Interface](../contracts/interface.json).');
    if(route==='import') args=['--contract','contracts/interface.json'];
    if(route==='refresh'||route==='extend') {text+=block(original);args=['--'+route];if(route==='extend') args.push('--contract','contracts/add.json');}
    const f=setup(t,text,{'contracts/interface.json':original,'contracts/add.json':{entries:[extra]}}),r=draft(f,args);
    assert.equal(r.code,0,'AUTHORED_CONTRACT_REJECTED_BY_SENTENCE_LEDGER');
    assert.equal(r.row.lint_clean,true);assert.equal(r.iface.kind,undefined);assert.equal(r.iface.draft_gaps,undefined);
    assert.deepEqual(r.iface.entries[0],original.entries[0]);
    const row=r.row.prose_coverage.find(row=>row.sentence===formatting);
    assert.deepEqual(row.pointers,[],'MISSING_FORMATTING_MEANING_FABRICATED_AS_MAPPING');
    assert.equal(row.status,'unmapped');assert.deepEqual(row.mappings,[]);
    assert.equal(r.row.questions.filter(q=>q.sentence===formatting).length,1);assert.ok(r.row.next_step);
    if(route==='extend') assert.ok(r.text.includes(JSON.stringify(original.entries[0])),'APPROVED_ENTRY_BYTES_CHANGED');
    const again=draft(f);assert.equal(again.code,0);assert.equal(again.text,r.text);
    assert.deepEqual(again.row.prose_coverage,r.row.prose_coverage);assert.deepEqual(again.row.questions,r.row.questions);
  });
}
for(const route of ['prose','embedded','import']) {
  test('3130 integration: Number requirements conflict with string transport: '+route,t=>{
    const value=structuredClone(original);value.entries[0].input_schema.properties.basisPoints.type='string';
    let text=prose.replace('required numeric `basisPoints`','required string `basisPoints`'),args=[];
    if(route==='embedded') text+=fence(value);
    if(route==='import') args=['--contract','contracts/interface.json'];
    const r=draft(setup(t,text,{'contracts/interface.json':value}),args);
    assert.equal(r.code,route==='prose'?4:0);
    assert.equal(r.iface.entries[0].input_schema.properties.basisPoints.type,'string');
    for(const sentence of numberClaims) {
      const row=r.row.prose_coverage.find(row=>row.sentence===sentence);
      assert.deepEqual(row.pointers,[],'NUMBER_REQUIREMENT_MAPPED_TO_STRING');
      assert.equal(row.status,'conflicting');assert.deepEqual(row.mappings,[]);
      assert.equal(r.row.questions.filter(q=>q.sentence===sentence).length,1);
    }
  });
}
test('3130 integration: inferred formatting maps to a field that retains its whole meaning',t=>{
  const r=draft(setup(t,prose));assert.equal(r.code,0);
  const row=r.row.prose_coverage.find(row=>row.sentence===formatting);
  assert.ok(row.pointers.length);
  for(const pointer of row.pointers) assert.ok(at(r.iface,pointer)?.description?.includes(formatting),'FORMATTING_MEANING_MISSING_AT_POINTER');
});
test('3130 integration: authored description retains a mapping but cannot override a type conflict',t=>{
  const value=structuredClone(original);
  value.entries[0].result_schema.description=formatting;
  value.entries[0].input_schema.description=numberClaims.join(' ');
  value.entries[0].input_schema.properties.basisPoints.type='string';
  const r=draft(setup(t,prose.replace('required numeric `basisPoints`','required string `basisPoints`')+fence(value)));
  assert.equal(r.code,0);
  for(const sentence of numberClaims) {
    const row=r.row.prose_coverage.find(row=>row.sentence===sentence);
    assert.deepEqual(row.pointers,[],'DESCRIPTION_OVERRIDES_STRUCTURED_TYPE');
    assert.equal(row.status,'conflicting');
  }
  retained(r,r.row.prose_coverage.find(row=>row.sentence===formatting));
});
test('3130 integration: a complete file contract imports and refreshes with evidence rather than a dead end',t=>{
  const text=readFileSync(new URL('../examples/fakes/files.prompt.md',import.meta.url),'utf8');
  const value=JSON.parse(interfaceBlocks(text)[0][1]);
  const f=setup(t,text.replace(interfaceBlocks(text)[0][0],''),{'contracts/interface.json':value});
  for(const args of [['--contract','contracts/interface.json'],['--refresh','--contract','contracts/interface.json']]) {
    const r=draft(f,args);assert.equal(r.code,0,'COMPLETE_FILE_CONTRACT_RECOVERY_BLOCKED');
    assert.equal(r.row.lint_clean,true);assert.deepEqual(r.iface.resources,value.resources);
    assert.ok(r.row.prose_coverage.some(row=>row.status==='unmapped'));assert.ok(r.row.questions.length);
  }
});
for(const conflict of [false,true]) test('3130 integration: automatic approval groups coverage before any checks: '+(conflict?'conflicting':'unmapped'),async t=>{
  const value=structuredClone(original);
  if(conflict) value.entries[0].input_schema.properties.basisPoints.type='string';
  const f=setup(t,(conflict?prose.replace('required numeric `basisPoints`','required string `basisPoints`'):prose)+fence(value),{'tests/coverage.test.mjs':'export {};\n'});const r=draft(f);assert.equal(r.code,0);
  let nativeCalls=0,runtimeCalls=0;
  const stdout=sink(),stderr=sink();
  const code=await runApprove({cwd:f.repo,words:[PLACE],automatic:true,tests:'node --test tests/coverage.test.mjs'},
    {stdout,stderr,interactive:false,runNativeTests(){nativeCalls++;return {code:0,stdout:'# tests 1\n# pass 1\n# fail 0\n'};},gh(){runtimeCalls++;throw Error('unexpected sign-in');}});
  assert.equal(code,4);assert.equal(nativeCalls,0,'COVERAGE_QUESTION_RAN_NATIVE_TESTS');assert.equal(runtimeCalls,0,'COVERAGE_QUESTION_CONTACTED_RUNTIME');assert.equal(readFileSync(join(f.repo,PLACE),'utf8'),r.text);
  assert.ok(stdout.text.includes(formatting),'AUTOMATIC_GATE_OMITTED_REPORT');
  for(const row of r.row.prose_coverage.filter(row=>row.status!=='mapped')) assert.ok(stderr.text.includes(JSON.stringify(row.sentence)),'GROUPED_DECISION_OMITTED_SENTENCE');
  assert.equal(existsSync(join(f.repo,'.git/pdd/approvals.json')),false);
});
test('3130 integration: person gate shows every coverage question before one decision and can decline',async t=>{
  const f=setup(t,prose+fence(original));const r=draft(f);assert.equal(r.code,0);
  const stdout=sink(),stderr=sink();
  const code=await runApprove({cwd:f.repo,words:[PLACE]},
    {stdout,stderr,interactive:true,stdin:Readable.from(['n\n'])});
  assert.equal(code,1);assert.equal(readFileSync(join(f.repo,PLACE),'utf8'),r.text);
  for(const row of r.row.prose_coverage) assert.ok(stdout.text.includes(JSON.stringify(row.sentence)),'PERSON_GATE_OMITTED_COVERAGE');
  assert.equal((stdout.text.match(/\? y\/n /g)??[]).length,1,'MULTIPLE_CONTRACT_QUESTIONS');
  assert.equal(existsSync(join(f.repo,'.git/pdd/approvals.json')),false);
});
for(const sentence of ['The input must be a Number.','A Number is required as input.','It accepts a Number.'])
  test('3130 integration: description wording cannot hide a numeric type conflict: '+sentence,t=>{
    const value=structuredClone(original);
    value.entries[0].input_schema.properties.basisPoints.type='string';
    value.entries[0].input_schema.description=sentence;
    const r=draft(setup(t,'# Contract\n\n'+sentence+'\n'+fence(value)));
    assert.equal(r.code,0);
    const row=r.row.prose_coverage.find(row=>row.sentence===sentence);
    assert.deepEqual(row.pointers,[],'DESCRIPTION_HIDES_NUMBER_STRING_CONFLICT');
    assert.equal(row.status,'conflicting');assert.ok(r.row.questions.some(q=>q.sentence===sentence));
  });
test('3130 integration: a type requirement with no unique field stays unmapped despite its description',t=>{
  const sentence='The value must be a Number.';
  const value=structuredClone(original);value.entries[0].input_schema.description=sentence;
  const r=draft(setup(t,'# Contract\n\n'+sentence+'\n'+fence(value)));
  assert.equal(r.code,0);const row=r.row.prose_coverage.find(row=>row.sentence===sentence);
  assert.deepEqual(row.pointers,[],'UNBOUND_TYPE_REQUIREMENT_BORROWS_DESCRIPTION');assert.equal(row.status,'unmapped');
});
test('3130 integration: each transport sentence maps to its own operation',t=>{
  const value=structuredClone(original);value.entries.push({...extra,input_schema:{...extra.input_schema,properties:{basisPoints:{type:'string'}}}});
  const claims=['In the Runtime interface, operation `formatPercent` takes an object with required numeric `basisPoints` and returns an object with required string `text`, the returned string; neither object has additional properties.','In the Runtime interface, operation `second` takes an object with required numeric `basisPoints` and returns an object with required string `text`, the returned string; neither object has additional properties.'];
  const r=draft(setup(t,'# Contract\n\n'+claims.join(' ')+'\n'+fence(value)));
  assert.equal(r.code,0);
  const first=r.row.prose_coverage.find(row=>row.sentence===claims[0]);retained(r,first);
  assert.ok(first.pointers.every(pointer=>pointer.startsWith('/entries/0/')));
  const second=r.row.prose_coverage.find(row=>row.sentence===claims[1]);
  assert.deepEqual(second.pointers,[],'SECOND_TRANSPORT_BORROWS_FIRST_SCHEMA');assert.equal(second.status,'conflicting');
});
test('3130 integration: a scalar type requirement cannot borrow the first of several transports',t=>{
  const claim='It takes a Number.';
  const value=structuredClone(original);value.entries[0].input_schema.description=claim;value.entries.push(extra);
  const first='In the Runtime interface, operation `formatPercent` takes an object with required numeric `basisPoints` and returns an object with required string `text`, the returned string; neither object has additional properties.';
  const second=first.replace('formatPercent','second');
  const r=draft(setup(t,'# Contract\n\n'+first+' '+second+' '+claim+'\n'+fence(value)));
  assert.equal(r.code,0);const row=r.row.prose_coverage.find(row=>row.sentence===claim);
  assert.deepEqual(row.pointers,[],'AMBIGUOUS_TYPE_REQUIREMENT_BORROWS_FIRST_TRANSPORT');assert.equal(row.status,'unmapped');
});


for (const context of ['fragment', 'cycle']) test('integration 013: person approval exposes unavailable coverage context: '+context, async t => {
  const dependency='[Meaning](../contracts/meaning.md'+(context==='fragment'?'#rules':'')+').';
  const value={...original,status:'draft',prose_sha256:''};
  const text=prose.replace('## Dependencies\n\nNone.','## Dependencies\n\n'+dependency)+block(value);
  const meaning='# Meaning\n\n## Rules\n\nRetain the exact formatter contract.\n'
    +(context==='cycle'?'\n## Dependencies\n\n[Formatter](../'+PLACE+').\n':'');
  const f=setup(t,text,{'contracts/meaning.md':meaning});
  const stdout=sink(),stderr=sink();
  const code=await runApprove({cwd:f.repo,words:[PLACE],said:'Accept the authored contract with the shown coverage gap.'},
    {stdout,stderr,interactive:false});
  assert.equal(code,0,stderr.text);
  assert.ok(stdout.text.includes('coverage-context-unavailable'));
  assert.ok(stdout.text.includes('/dependencies'));
  const after=JSON.parse(interfaceBlocks(readFileSync(join(f.repo,PLACE),'utf8'))[0][1]);
  assert.equal(after.status,'approved');
  assert.deepEqual(after.entries,value.entries);
  assert.equal(JSON.parse(readFileSync(join(f.repo,'.git/pdd/approvals.json'),'utf8')).approvals.length,1);
});

for(const malformed of [false,true]) test('example list coverage completes and preserves supported sentences: '+(malformed?'malformed':'valid'),t=>{
  const sentence='For example, 0 produces `0 B`'+', 1 produces `1 B`'.repeat(80)+(malformed?' unexpected.':'.');
  const bytes=readFileSync(new URL('./fixtures/interface-drafting/bytes.prompt.md',import.meta.url),'utf8');
  const source=bytes.replace(interfaceBlocks(bytes)[0][0],'').replace(/For example,[^\n]+/,sentence);
  assert.ok(source.includes(sentence));
  const r=draft(setup(t,source),[],5000);
  const row=r.row.prose_coverage.find(row=>row.sentence===sentence);
  assert.equal(row.status,malformed?'unmapped':'mapped');
  if(malformed) {assert.deepEqual(row.pointers,[]);assert.equal(r.code,4);}
  else {retained(r,row);assert.ok(r.iface.entries[0].result_schema.description.includes(sentence));assert.equal(r.code,0);}
});

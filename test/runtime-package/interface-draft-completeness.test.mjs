import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {join} from 'node:path';
import {runPdd} from '../../src/pdd-cli.mjs';
import {interfaceBlocks,proseSha256} from '../../src/runtime-seam.mjs';
import {harbor,PLACE,sink} from './runtime-fake.mjs';

const raw=readFileSync(new URL('../fixtures/interface-drafting/percent.prompt.md',import.meta.url),'utf8');
const original=JSON.parse(interfaceBlocks(raw)[0][1]);
const prose=raw.replace(interfaceBlocks(raw)[0][0],'');
const sentence='A file audit record is created on disk.';
const object=properties=>({type:'object',properties,required:Object.keys(properties),additionalProperties:false});
const extra={operation:'second',input_schema:object({value:{type:'number'}}),result_schema:object({text:{type:'string'}}),errors:[]};
const fence=value=>'\n## Public schema\n\n```json\n'+JSON.stringify(value)+'\n```\n';
const block=value=>'<details><summary>Runtime interface</summary>\n\n```json\n'+JSON.stringify(value)+'\n```\n</details>';
function setup(t,text,files={}) {
  return harbor(t,repo=>{
    writeFileSync(join(repo,PLACE),text);
    mkdirSync(join(repo,'contracts'),{recursive:true});
    for(const [path,value] of Object.entries(files)) writeFileSync(join(repo,path),typeof value==='string'?value:JSON.stringify(value));
  });
}
const read=f=>readFileSync(join(f.repo,PLACE),'utf8');
const iface=f=>JSON.parse(interfaceBlocks(read(f))[0][1]);
async function draft(f,args=[]) {
  const stdout=sink(),stderr=sink();
  const code=await runPdd(['interface','draft',PLACE,...args,'--json'],{cwd:f.repo,stdout,stderr,env:{HOME:f.home,XDG_CONFIG_HOME:join(f.home,'.config')},pathDiagnostic:()=>[]});
  assert.ok(stdout.text,stderr.text);
  return {code,row:JSON.parse(stdout.text).rows[0]};
}
function review(f,result,sentence,{inferred=false}={}) {
  assert.equal(result.code,inferred?4:0,'AUTHORED_CONTRACT_BLOCKED_BY_COVERAGE');
  assert.equal(result.row.state,'drafted');
  assert.equal(iface(f).kind,inferred?'partial':undefined);
  assert.equal(result.row.lint_clean,!inferred);
  assert.deepEqual(result.row.prose_coverage?.find(row=>row.sentence===sentence)?.pointers,[],'UNMAPPED_SENTENCE_LEDGER_MISSING');
  assert.equal(result.row.questions.filter(q=>q.question.includes('"'+sentence+'"')).length,1,'UNMAPPED_SENTENCE_QUESTION_COUNT');
  assert.ok(result.row.next_step?.includes('--refresh --contract'));
  assert.equal(iface(f).prose_sha256,proseSha256(read(f)));
}
for(const claim of ['The input object must contain a string `locale`.',sentence])
  test('3130 repair 2: embedded JSON reconciles supplementary prose: '+claim,async t=>{
    const text=prose.replace('## Percentage format',claim+'\n\n## Percentage format')+fence(original);
    const f=setup(t,text),result=await draft(f);
    review(f,result,claim);
    const saved=read(f),again=await draft(f);
    assert.equal(again.code,0);assert.equal(read(f),saved);assert.deepEqual(again.row.questions,result.row.questions);
  });

test('3130 repair 2: dependency JSON cannot suppress prompt effects',async t=>{
  const text=prose.replace('## Percentage format',sentence+'\n\n## Percentage format').replace('## Dependencies\n\nNone.','## Dependencies\n\n[Interface](../contracts/interface.json).');
  const f=setup(t,text,{'contracts/interface.json':original});
  review(f,await draft(f),sentence);
});

test('3130 repair 2: declared context prose is covered on contract import',async t=>{
  const claim='Compliance records persist after each invocation.';
  const f=setup(t,'# Contract\n\n## Dependencies\n\n[Policy](../contracts/policy.md).\n',{'contracts/policy.md':'# Policy\n\n'+claim+'\n','contracts/interface.json':original});
  const result=await draft(f,['--contract','contracts/interface.json']);
  review(f,result,claim);
  assert.equal(result.row.prose_coverage.find(row=>row.sentence===claim).source,'contracts/policy.md');
});

for(const route of ['import','refresh','extend']) {
  test('3130 repair 2: '+route+' validates expanded schemas and preserves authored references',async t=>{
    const value=structuredClone(original);
    value.entries[0].input_schema={$contract:'contracts/shapes.json#/input'};
    const before=route==='import' ? prose : prose+block(value);
    const f=setup(t,before,{'contracts/interface.json':value,'contracts/shapes.json':{input:original.entries[0].input_schema},'contracts/add.json':{entries:[{...extra,input_schema:{$contract:'contracts/shapes.json#/input'}}]}});
    const args=route==='import'?['--contract','contracts/interface.json']:route==='refresh'?['--refresh']:['--extend','--contract','contracts/add.json'];
    const result=await draft(f,args);
    assert.equal(result.code,0,'SHARED_SCHEMA_REJECTED_BEFORE_EXPANSION');
    assert.equal(result.row.state,'drafted');assert.equal(result.row.lint_clean,true);
    assert.ok(result.row.prose_coverage.length);assert.ok(result.row.prose_coverage.some(row=>row.status==='unmapped'));
    for(const row of result.row.prose_coverage) assert.equal(row.status==='mapped',row.pointers.length>0);
    assert.deepEqual(iface(f).entries[0].input_schema,value.entries[0].input_schema);
    assert.equal(Object.hasOwn(iface(f),'kind'),false);
    if(route==='extend') {
      assert.ok(read(f).includes(JSON.stringify(value.entries[0])),'APPROVED_ENTRY_BYTES_CHANGED');
      assert.equal(result.row.interface_diff.before,JSON.stringify(value));
      assert.equal(iface(f).entries.length,2);
      assert.deepEqual(iface(f).entries[1].input_schema,value.entries[0].input_schema);
    }
  });
  test('3130 repair 2: '+route+' rejects an invalid expanded field before writing',async t=>{
    const value=structuredClone(original);value.entries[0].input_schema={$contract:'contracts/shapes.json#/input'};
    const bad=structuredClone(original.entries[0].input_schema);bad.properties.basisPoints.type=['number','string'];
    const f=setup(t,route==='import'?prose:prose+block(value),{'contracts/interface.json':value,'contracts/shapes.json':{input:bad},'contracts/add.json':{entries:[extra]}});
    const before=read(f),args=route==='import'?['--contract','contracts/interface.json']:route==='refresh'?['--refresh']:['--extend','--contract','contracts/add.json'];
    const result=await draft(f,args);
    assert.equal(result.code,4);assert.equal(result.row.state,'refused');assert.equal(read(f),before);
    assert.equal(result.row.problems[0].section,'/entries/0/input_schema/properties/basisPoints','RAW_REFERENCE_VALIDATION_HID_EXPANDED_FIELD');
    assert.ok(result.row.problems[0].rule);
  });
}

test('3130 repair 2: every draft route reports unresolved sentence coverage',async t=>{
  const rows=[];
  for(const route of ['prose','embedded','dependency','import','refresh','extend']) {
    let text=prose.replace('## Percentage format',sentence+'\n\n## Percentage format');
    const files={'contracts/interface.json':original,'contracts/add.json':{entries:[extra]}};
    const args=[];
    if(route==='embedded') text+=fence(original);
    if(route==='dependency') text=text.replace('## Dependencies\n\nNone.','## Dependencies\n\n[Interface](../contracts/interface.json).');
    if(route==='import') args.push('--contract','contracts/interface.json');
    if(route==='refresh' || route==='extend') {
      text+=block(original);args.push('--'+route);
      if(route==='extend') args.push('--contract','contracts/add.json');
    }
    const f=setup(t,text,files),result=await draft(f,args),ledger=result.row.prose_coverage;
    rows.push({route,code:result.code,kind:iface(f).kind,unmapped:ledger?.find(row=>row.sentence===sentence)?.status==='unmapped',questions:result.row.questions?.filter(q=>q.question.includes('"'+sentence+'"')).length,recovery:result.row.next_step?.includes('--refresh --contract')===true});
  }
  assert.deepEqual(rows,rows.map(({route})=>({route,code:route==='prose'?4:0,kind:route==='prose'?'partial':undefined,unmapped:true,questions:1,recovery:true})),'DRAFT_ROUTE_BYPASSED_COMMON_GATE');
});

for(const mismatch of ['input','result','operation'])
  test('3130 repair 2: coverage reconciles the final '+mismatch+' declaration',async t=>{
    const value=structuredClone(original);
    if(mismatch==='input') value.entries[0].input_schema.properties.basisPoints={type:'string'};
    if(mismatch==='result') value.entries[0].result_schema.properties.text={type:'boolean'};
    if(mismatch==='operation') value.entries[0].operation='other';
    const f=setup(t,prose+fence(value)),result=await draft(f);
    assert.equal(result.code,0,'AUTHORED_CONTRACT_BLOCKED_BY_COVERAGE');
    assert.equal(iface(f).kind,undefined);
    const transport=result.row.prose_coverage?.find(row=>row.sentence.includes('In the Runtime interface'));
    assert.ok(transport);assert.deepEqual(transport.pointers,[]);
    assert.ok(result.row.questions.some(q=>q.question.includes(transport.sentence)));
  });

test('3130 repair 2: coverage uses the expanded referenced schema',async t=>{
  const value=structuredClone(original);value.entries[0].input_schema={$contract:'contracts/shapes.json#/input'};
  const wrong=object({locale:{type:'string'}});
  const f=setup(t,prose+fence(value),{'contracts/shapes.json':{input:wrong}}),result=await draft(f);
  assert.equal(result.code,0,'AUTHORED_CONTRACT_BLOCKED_BY_COVERAGE');assert.equal(iface(f).kind,undefined);
  const transport=result.row.prose_coverage?.find(row=>row.sentence.includes('In the Runtime interface'));
  assert.ok(transport);assert.deepEqual(transport.pointers,[]);
});

for(const route of ['prose','embedded'])
  test('3130 repair 2: '+route+' cannot map another public binding to the first operation',async t=>{
    const claim='Public binding: module function `other(x)` in `src/other.js`, exported from `other`.';
    const text=prose.replace('## Percentage format',claim+'\n\n## Percentage format')+(route==='embedded'?fence(original):'');
    const f=setup(t,text),result=await draft(f);
    review(f,result,claim,{inferred:route==='prose'});
    assert.deepEqual(iface(f).entries.map(entry=>entry.operation),['formatPercent']);
  });

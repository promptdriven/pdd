import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';

// Story: local-contract-check, Rules to check. Complete finite domains were
// approved before implementation: 84+42+24+9+54+12+25+16+4 = 270 configurations.
// Expected membership is computed from these synthetic domains, never code output.
async function verdict(schema, value, expected, label) {
  const { validateContract } = await import('../src/runtime-preflight.mjs');
  const result = validateContract({ schema_json: schema, value_json: value });
  assert.deepEqual(result.schema_problems, [], `${label}: schema`);
  assert.equal(result.value_problems.length > 0, expected === 'miss', `${label}: definite mismatch`);
  assert.equal(result.unproved.length > 0, expected === 'unknown', `${label}: unavailable`);
  for (const problem of result.value_problems) {
    assert.equal(problem.code, 'invalid-input');
    assert.equal(typeof problem.pointer, 'string');
    assert.ok(typeof problem.rule === 'string' && problem.rule.length > 0);
  }
  for (const problem of result.unproved) {
    assert.equal(problem.code, 'contract-validation-unavailable');
    assert.equal(typeof problem.pointer, 'string');
    assert.ok(typeof problem.rule === 'string' && problem.rule.length > 0);
  }
}
const j = JSON.stringify;
const values = [null, false, true, '', 'A', 0, 1, 0.5, [], [0], {}, {x: 0}];
const schemas = [
  [{type:'null'}, v => v === null],
  [{type:'boolean'}, v => typeof v === 'boolean'],
  [{type:'string'}, v => typeof v === 'string'],
  [{type:'integer'}, v => Number.isInteger(v)],
  [{type:'number'}, v => typeof v === 'number'],
  [{type:'array',items:{type:'integer'}}, v => Array.isArray(v) && v.every(Number.isInteger)],
  [{type:'object',properties:{x:{type:'integer'}},required:['x'],additionalProperties:false},
    v => v !== null && !Array.isArray(v) && typeof v === 'object' && Object.keys(v).length === 1 && Object.hasOwn(v,'x') && Number.isInteger(v.x)],
];
test('formal A: all 84 root type/shape memberships', async () => {
  for (const [schema, fits] of schemas) for (const value of values)
    await verdict(j(schema),j(value),fits(value)?'match':'miss',`${j(schema)} / ${j(value)}`);
});
test('formal B: all 42 bounded integer predicates', async () => {
  const predicates = [
    ['minimum',0,v=>v>=0], ['maximum',0,v=>v<=0],
    ['exclusiveMinimum',0,v=>v>0], ['exclusiveMaximum',0,v=>v<0],
    ['multipleOf',2,v=>v%2===0], ['const',0,v=>v===0],
  ];
  for (const [key,bound,fits] of predicates) for (let value=-3;value<=3;value++)
    await verdict(j({type:'integer',[key]:bound}),j(value),fits(value)?'match':'miss',`${key}/${value}`);
});
test('formal C: all 24 decimal comparisons from exact hundredths', async () => {
  const inputs = [['0.05',5],['0.10',10],['0.25',25],['0.5',50],['0.9',90],['0.95',95]];
  const rules = [
    ['{"type":"number","minimum":0.1}',n=>n>=10],
    ['{"type":"number","maximum":0.9}',n=>n<=90],
    ['{"type":"number","enum":[0.25,0.5]}',n=>n===25||n===50],
    ['{"type":"number","enum":[1e-1]}',n=>n===10],
  ];
  for (const [schema,fits] of rules) for (const [text,hundredths] of inputs)
    await verdict(schema,text,fits(hundredths)?'match':'miss',`${schema}/${text}`);
});
test('formal D: all nine three-way oneOf state pairs', async () => {
  const left = [{type:'string',enum:['A']},{type:'string',enum:['B']},{type:'string',pattern:'\\p{L}+'}];
  const right = [{type:'string',const:'A'},{type:'string',const:'B'},{type:'string',pattern:'[]'}];
  for (let a=0;a<3;a++) for (let b=0;b<3;b++) {
    const expected = a===2||b===2 ? 'unknown' : (a===0)+(b===0)===1 ? 'match' : 'miss';
    await verdict(j({oneOf:[left[a],right[b]]}),'"A"',expected,`states ${a},${b}`);
  }
});
const record = (name,schema) => `### ${name}\n\`\`\`json\n${schema}\n\`\`\`\n`;
const table = rows => '# World\n| Key | Writer | Schema |\n|---|---|---|\n'+rows.map(([writer,target])=>`| item | ${writer} | contracts/shapes.md#${target} |\n`).join('');
async function checkFiles(files, expected, diagnostic) {
  const { runContracts } = await import('../src/contracts.mjs');
  const cwd=fs.mkdtempSync(join(tmpdir(),'pdd-formal-contract-'));
  try {
    for (const [path,text] of Object.entries(files)) {
      fs.mkdirSync(dirname(join(cwd,path)),{recursive:true}); fs.writeFileSync(join(cwd,path),text);
    }
    assert.equal(spawnSync('git',['init','-q'],{cwd}).status,0);
    assert.equal(spawnSync('git',['add','.'],{cwd}).status,0);
    let output='';
    const stream={write:text=>{output+=text;}};
    const result=await runContracts({words:[],options:{'--check':true},cwd},
      {env:{...process.env,PDD_STATE_DIR:join(cwd,'.private-state')},stdout:stream,stderr:stream});
    assert.equal(result,expected,`${j(files)}\n${output}`);
    if (diagnostic) assert.ok(output.split(/\r?\n/).some(line=>diagnostic.every(part=>line.includes(part))),`${j(diagnostic)}\n${output}`);
    for (const [path,text] of Object.entries(files)) assert.equal(fs.readFileSync(join(cwd,path),'utf8'),text,`source changed: ${path}`);
  } finally { fs.rmSync(cwd,{recursive:true,force:true}); }
}
test('formal E: all 54 ownership, mapping, presence and unused-schema configurations', async () => {
  const bases=[[],[['owner','A']],[['owner','A'],['owner','A']]];
  const extras=[[],[['second','A']],[['owner','B']]];
  for (const seed of ['absent','null','0']) for (const base of bases) for (const extra of extras) for (const valid of [false,true]) {
    const rows=[...base,...extra];
    const pairs=new Set(rows.map(([writer,schema])=>`${writer}/${schema}`));
    const target=rows[0]?.[1];
    const mismatch=seed!=='absent' && (pairs.size===0 || target==='B' || seed==='null');
    const expected=!valid||pairs.size>1||mismatch?4:0;
    let diagnostic;
    if (!valid) diagnostic=['contracts/shapes.md','contracts/shapes.md#A'];
    else if (pairs.size>1) diagnostic=['contracts/world.md','item',extra[0][0]==='second'?'Writer':'Schema'];
    else if (mismatch) diagnostic=['contracts/seed-world.json','item','/item'];
    await checkFiles({
      'contracts/world.md':table(rows),
      'contracts/seed-world.json':seed==='absent'?'{}':`{"item":${seed}}`,
      'contracts/shapes.md':record('A',valid?' {"type":"integer"}':'{"type":"array"}')+record('B','{"type":"string"}'),
    },expected,diagnostic);
  }
});
test('formal F: 11 active definite/unavailable configurations; one superseded', async () => {
  const states=[['{"type":"integer"}','0',0],['{"type":"integer"}','null',4],['{"type":"string","pattern":"[]"}','"A"',5]];
  for (const [schema,value,state] of states) for (let extra=0;extra<4;extra++) {
    if (state===0 && extra===2) continue; // Lead 13:59: one superseded configuration; frozen replacement covers skip/pass.
    const files={
      'contracts/world.md':table([['owner','A']]),
      'contracts/seed-world.json':`{"item":${value}}`,
      'contracts/shapes.md':record('A',schema),
    };
    if (extra===1||extra===3) files['contracts/bad.md']=record('bad','{"type":"array"}');
    if (extra===2||extra===3) files['contracts/unknown.json']='{"note":"hello"}';
    const expected=state===4||extra===1||extra===3?4:state===5||extra===2?5:0;
    const diagnostic=extra===1||extra===3?['contracts/bad.md','contracts/bad.md#bad']:
      state===4?['contracts/seed-world.json','item','/item']:
      state===5?['contracts/seed-world.json','item','/item','unavailable']:
      extra===2?['contracts/unknown.json','/note','unavailable']:undefined;
    await checkFiles(files,expected,diagnostic);
  }
});
test('formal G: all 25 exact numeric and 16 ordered literal equalities', async () => {
  const {parseJsonValue,jsonValuesEqual}=await import('../src/contract-refs.mjs');
  const numbers=['1','1.0','1e0','9007199254740992','9007199254740993'];
  for (let a=0;a<5;a++) for (let b=0;b<5;b++)
    assert.equal(jsonValuesEqual(parseJsonValue(numbers[a]),parseJsonValue(numbers[b])),a===b||(a<3&&b<3),`${numbers[a]} / ${numbers[b]}`);
  const literals=['["a","b"]','["b","a"]','{"required":["a","b"]}','{"required":["b","a"]}'];
  for (let a=0;a<4;a++) for (let b=0;b<4;b++)
    assert.equal(jsonValuesEqual(parseJsonValue(literals[a]),parseJsonValue(literals[b])),a===b,`${literals[a]} / ${literals[b]}`);
});
test('formal G: four precision availability boundaries', async () => {
  await verdict('{"type":"integer","const":9007199254740993}','9007199254740992','unknown','adjacent large const');
  await verdict('{"type":"number","minimum":0.1}','0.10000000000000001','unknown','precision-changing decimal');
  await verdict('{"type":"integer"}','9007199254740993','match','large integer type only');
  await verdict('{"type":"number"}','9007199254740993','match','large number type only');
});

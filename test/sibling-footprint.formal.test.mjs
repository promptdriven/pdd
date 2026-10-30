import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { captureSource, findTests, sourceFilePort } from '../src/runtime-preflight.mjs';
import { expandSource, catalogRecords } from '../src/contract-refs.mjs';
import { runContracts } from '../src/contracts.mjs';

// Independent bounded oracles from shared-contract-status/shared-source-limits
// Rules to check and their owner prompts. These are not Runtime/native replays.
const LIMIT = 10_485_760;
const A = 'user_stories/a.md', B = 'user_stories/b.md';
const GOOD = 'tests/good.json', SIBLING = 'tests/sibling.json', OTHER = 'tests/other.json';
const SP = 'prompts/sibling.prompt.md';
const leaf = '{ "type" : "number", "default" : 9007199254740993 }';
const sink = () => ({ text:'', write(value) { this.text += value; } });
function write(root, path, value) {
  fs.mkdirSync(join(root,path,'..'), {recursive:true});
  fs.writeFileSync(join(root,path), typeof value === 'string' ? value : JSON.stringify(value));
}
function prompt(schema = '{"type":"object","properties":{},"required":[],"additionalProperties":false}', dependency = '') {
  return '# Synthetic formal program\n\n' + (dependency ? `## Dependencies\n- [Required](${dependency})\n\n` : '')
    + '<details><summary>Runtime interface</summary>\n```json\n'
    + `{"status":"draft","prose_sha256":"","entries":[{"operation":"run","input_schema":${schema},"result_schema":{"type":"object","properties":{},"required":[],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[]}`
    + '\n```\n</details>\n';
}
const scenario = (story, entry) => ({schema_version:'prompt-runtime.program-scenario.v1',story_path:story,
  criteria:[{id:'AC1',text:'I can run the synthetic program.'}],initial_world:{},simulation:{},context:[],
  steps:[{step_id:'run',entry_path:entry,operation:'run',input:{},checks:[{criterion_id:'AC1',target:'result',path:'',op:'equals',value:{}}]}]});
function fixture(t, refs = false) {
  const root = fs.mkdtempSync(join(tmpdir(),'pdd-formal-sibling-'));
  t.after(() => fs.rmSync(root,{recursive:true,force:true}));
  assert.equal(spawnSync('git',['init','-q'],{cwd:root}).status,0);
  for (const story of [A,B]) write(root,story,'# Synthetic Story\n\n## Acceptance criteria\n\n1. I can run the synthetic program.\n');
  write(root,GOOD,scenario(A,'prompts/good.prompt.md'));
  write(root,SIBLING,scenario(A,SP));
  write(root,OTHER,scenario(B,'prompts/other.prompt.md'));
  write(root,'prompts/good.prompt.md',prompt(refs ? '{"$contract":"contracts/input.json#"}' : undefined));
  write(root,'contracts/input.json','{"type":"object","properties":{},"required":[],"additionalProperties":false}');
  write(root,SP,prompt(undefined,'../docs/sibling.txt'));
  write(root,'docs/sibling.txt','original sibling dependency');
  write(root,'prompts/other.prompt.md',prompt(undefined,'../docs/other.txt'));
  write(root,'docs/other.txt','independent Story B');
  return root;
}
const footprint = (capture, story) => capture.stories.find(row => row.story_path === story);
const paths = capture => capture.files.map(file => file.path);
const refusal = fn => assert.throws(fn, error => error.exitCode === 4 && error.message.length < 5000);

function fakeSizes(t, root, sizes) {
  const originals = {lstatSync:fs.lstatSync,openSync:fs.openSync,readFileSync:fs.readFileSync};
  const reads = [];
  const name = path => typeof path === 'string' && Object.keys(sizes).find(key => join(root,key) === path);
  fs.lstatSync = (path,...args) => {
    const stat = originals.lstatSync(path,...args), key = name(path);
    if (!key) return stat;
    return new Proxy(stat,{get(target,property) {
      if (property === 'size') return typeof target.size === 'bigint' ? BigInt(sizes[key]) : sizes[key];
      const value = Reflect.get(target,property); return typeof value === 'function' ? value.bind(target) : value;
    }});
  };
  for (const method of ['openSync','readFileSync']) fs[method] = (path,...args) => {
    const key = name(path); if (key) reads.push({method,path:key});
    return originals[method](path,...args);
  };
  syncBuiltinESMExports();
  const restore = () => { Object.assign(fs,originals); syncBuiltinESMExports(); };
  t.after(restore);
  return {reads,restore};
}

test('FORMAL sibling: complete 2 x 6 x 2 selection/error/reference domain, isolation and canonical repair', t => {
  let contexts = 0, repairs = 0;
  for (const refs of [false,true]) for (const kind of ['prompt','seed','dependency','unsafe','cycle','oversize']) {
    const root = fixture(t,refs), original = captureSource(root,{tests:[GOOD,SIBLING,OTHER]});
    const originalPrompt = fs.readFileSync(join(root,SP),'utf8');
    const originalScenario = fs.readFileSync(join(root,SIBLING),'utf8');
    let cause;
    if (kind === 'prompt') { fs.rmSync(join(root,SP)); cause = /sibling\.prompt\.md/; }
    if (kind === 'seed') {
      const doc = scenario(A,SP); doc.initial_world = {$seed:'contracts/missing.json'}; write(root,SIBLING,doc); cause = /missing\.json/;
    }
    if (kind === 'dependency') { fs.rmSync(join(root,'docs/sibling.txt')); cause = /sibling\.txt/; }
    if (kind === 'unsafe') { write(root,SP,prompt(undefined,'../secrets/private.txt')); write(root,'secrets/private.txt','must remain unread'); cause = /secret|unsafe/i; }
    if (kind === 'cycle') {
      write(root,'contracts/cycle.json',{$contract:'contracts/cycle.json#'});
      write(root,SP,prompt('{"$contract":"contracts/cycle.json#"}')); cause = /contract-cycle/;
    }
    let spy;
    if (kind === 'oversize') { spy = fakeSizes(t,root,{'docs/sibling.txt':LIMIT+1}); cause = /too big/; }
    for (const selected of [false,true]) {
      const invoke = () => captureSource(root,{tests:selected ? [SIBLING,OTHER] : [GOOD,OTHER]});
      if (selected) refusal(invoke);
      else {
        let got; assert.doesNotThrow(() => { got = invoke(); },`${refs}/${kind}: good selection survives`);
        const a = footprint(got,A);
        assert.ok(a.unavailable?.some(item => cause.test(item.cause)),`${kind}: finite unavailable cause`);
        assert.equal(Object.hasOwn(a,'files'),false,'partial closure cannot be a complete footprint');
        assert.equal(Object.hasOwn(a,'references'),false);
        assert.deepEqual(a.tests,[GOOD,SIBLING]);
        assert.deepEqual(footprint(got,B),footprint(original,B),'Story B remains complete and unchanged');
        assert.deepEqual(paths(got),['docs/other.txt','prompts/good.prompt.md','prompts/other.prompt.md',GOOD,OTHER,A,B].sort());
        const expectedGood = refs ? prompt('{"type":"object","properties":{},"required":[],"additionalProperties":false}') : prompt();
        assert.equal(got.sources.find(file => file.path === 'prompts/good.prompt.md').bytes.toString(),expectedGood);
        assert.equal(got.references.length,refs ? 1 : 0);
        assert.ok(got.warnings.some(warning => warning.includes(A) && /unavailable/.test(warning)));
      }
      contexts++;
    }
    if (spy) { assert.deepEqual(spy.reads,[],'oversized sibling never opens or reads'); spy.restore(); }
    write(root,SP,originalPrompt); write(root,SIBLING,originalScenario); write(root,'docs/sibling.txt','original sibling dependency');
    for (const tests of [[GOOD],[GOOD,SIBLING],[GOOD,SIBLING,OTHER]]) {
      const restored = captureSource(root,{tests});
      assert.deepEqual(footprint(restored,A),footprint(original,A),'exact repair restores canonical complete footprint');
      assert.equal(footprint(restored,A).files.some(file => file.path === 'docs/other.txt'),false);
      repairs++;
    }
    write(root,'docs/sibling.txt','changed sibling dependency');
    assert.notDeepEqual(footprint(captureSource(root,{tests:[GOOD]}),A),footprint(original,A));
  }
  assert.equal(contexts,24); assert.equal(repairs,36);
});

// Each Cartesian member is a separate test so a counterexample cannot hide the
// other roles/sizes. Source355 preserves unread small replacements; raw prompt
// hashing still requires an independently bounded read of the original prompt.
for (const size of [12_582_912,2_147_483_649]) for (const path of ['user_stories/transcript.md','contracts/ignored.md','prompts/ignored.prompt.md']) {
  test(`FORMAL discovery: ${size} bytes in ${path}, ignored skip and selected refusal`, t => {
    const root = fixture(t), before = captureSource(root,{tests:[GOOD]});
    write(root,path,'synthetic ignored document');
    const spy = fakeSizes(t,root,{[path]:size});
    const found = findTests({root}); assert.equal(found.tests.length,3);
    const captured = captureSource(root,{tests:[GOOD]});
    assert.deepEqual(paths(captured),paths(before)); assert.equal(captured.sha256,before.sha256);
    const port = sourceFilePort(root); assert.equal(port.stat({path}).size,size);
    refusal(() => port.read({path}));
    let replacementError, replacement;
    try { replacement = captureSource(root,{tests:[GOOD],prepareSource:() => [{path,bytes:'small replacement'}]}); }
    catch (error) { replacementError = error; }
    for (const words of [[],['sync']]) {
      const stdout = sink(), stderr = sink();
      assert.equal(runContracts({cwd:root,words},{env:{HOME:join(root,'home'),PDD_STATE_DIR:join(root,'state')},stdout,stderr}),0,stderr.text);
      assert.ok(stderr.text.includes(path) && /unavailable|too big/.test(stderr.text));
      assert.equal(stdout.text.includes(`${path}#`),false,'skipped catalog content cannot invent a record');
    }
    assert.deepEqual(spy.reads,[],'all ignored and selected huge variants stop before open/read');
    spy.restore();
    if (path.endsWith('.prompt.md')) {
      assert.equal(replacementError?.exitCode,4,'required raw prompt hashing must stat-refuse before reading');
    } else {
      assert.equal(replacementError,undefined,'safe unread original size does not refuse supplied replacement bytes');
      assert.deepEqual(replacement.files,[...before.files,{path,size:17}].sort((a,b)=>a.path.localeCompare(b.path)));
      assert.deepEqual(replacement.sources,[...before.sources,{path,bytes:Buffer.from('small replacement')}].sort((a,b)=>a.path.localeCompare(b.path)));
      assert.equal(replacement.bytes,before.bytes+17,'only effective replacement bytes enter the selected total');
    }
  });
}

test('FORMAL user evidence: complete 2 known-user modes x 5 consumer states never claim completeness from unavailable discovery', t => {
  let cases = 0;
  for (const known of [false,true]) for (const state of ['complete','12MiB','2GiB','unresolved','sibling']) {
    const root = fixture(t,known), ignored = 'prompts/unavailable.prompt.md';
    let spy;
    if (state === '12MiB' || state === '2GiB') {
      write(root,ignored,'synthetic unread consumer');
      spy = fakeSizes(t,root,{[ignored]:state === '12MiB' ? 12_582_912 : 2_147_483_649});
    }
    if (state === 'unresolved') write(root,ignored,prompt('{"$contract":"contracts/missing.json#"}'));
    if (state === 'sibling') fs.rmSync(join(root,SP));
    const stdout = sink(), stderr = sink();
    assert.equal(runContracts({cwd:root},{env:{HOME:join(root,'home'),PDD_STATE_DIR:join(root,'state')},stdout,stderr}),0,stderr.text);
    const record = stdout.text.split('\n').find(line => line.startsWith('contracts/input.json#  '));
    assert.ok(record,'an independent available record remains listed');
    const users = /  users: (.*?)  Stories:/.exec(record)?.[1];
    assert.equal(users.includes('prompts/good.prompt.md'),known,'preserve verified consumers without inventing one');
    if (state === 'complete') assert.equal(users,known ? 'prompts/good.prompt.md' : 'none');
    else {
      assert.match(users,/unavailable|incomplete/,'unknown consumers cannot prove an exhaustive users list');
      assert.doesNotMatch(users,/\bnone\b/,'unavailable discovery cannot prove no users');
    }
    if (spy) { assert.deepEqual(spy.reads,[],'oversized consumer remains unread'); spy.restore(); }
    cases++;
  }
  assert.equal(cases,10);
});

test('FORMAL accounting: complete 6 depths x 2 cached annotation modes preserve exact layout with linear marker work', () => {
  let cases = 0;
  for (const depth of [0,1,8,32,128,400]) for (const descriptions of [false,true]) {
    let tail = '{"type":"string","description":"formal-node-0"}';
    for (let i=1;i<=depth;i++) tail = `{"type":"object","description":"formal-node-${i}","properties":{"child":${tail}},"required":[],"additionalProperties":false}`;
    const selectors = ['first','second'].map(title => `{"$contract":"contracts/value.json#","title":"${title}"${descriptions ? ',"description":"local"' : ''}}`);
    const authored = ` \n{"type":"object","properties":{"reasoning":${selectors[0]},"answer":${selectors[1]},"tail":${tail}}}\n`;
    const expected = selectors.reduce((text,selector,i) => text.replace(selector,leaf.replace(' }',`, "title" : "${['first','second'][i]}"${descriptions ? ', "description" : "local"' : ''} }`)),authored);
    const byteLength = Buffer.byteLength; let markerWork = 0, reads = 0;
    Buffer.byteLength = function(value,...args) {
      if (typeof value === 'string') markerWork += [...value.matchAll(/formal-node-\d+/g)].length;
      return byteLength.call(this,value,...args);
    };
    let got;
    try {
      got = expandSource({path:'formal.json',text:authored,format:'json-schema'}, {
        stat:() => ({exists:true,is_symlink:false,size:byteLength(leaf)}),
        read:() => { reads++; return {content:leaf}; },
      });
    } finally { Buffer.byteLength = byteLength; }
    assert.equal(got.text,expected); assert.equal(reads,1);
    assert.equal(got.references.length,2);
    assert.ok(got.references.every(ref => ref.value_json === '{"default":9007199254740993,"type":"number"}'));
    // Count every ordinary-node marker charged across byte-size operations,
    // including substrings/full values; a subtree walk per ancestor is quadratic.
    assert.ok(markerWork <= 8*(depth+1),`depth ${depth}: ${markerWork} marker charges exceeds linear budget`);
    cases++;
  }
  assert.equal(cases,12);
});

test('FORMAL expansion: complete 2 widths x 5 depths x 2 leaf sizes uses independent expanded-byte recurrence', () => {
  let cases = 0, refused = 0;
  for (const width of [2,4]) for (let depth=0;depth<=4;depth++) for (const padding of [0,65_535]) {
    const leafText = `{"type":"string","description":"${'x'.repeat(padding)}"}`;
    const sources = {'contracts/0.json':leafText};
    let bytes = Buffer.byteLength(leafText), expected = leafText;
    for (let level=1;level<=depth;level++) {
      const names = Array.from({length:width},(_,i) => `f${i}`);
      sources[`contracts/${level}.json`] = '{"type":"object","properties":{' + names.map(name => `"${name}":{"$contract":"contracts/${level-1}.json#"}`).join(',') + '}}';
      bytes = Buffer.byteLength('{"type":"object","properties":{}}') + width*bytes + names.reduce((sum,name) => sum+Buffer.byteLength(`"${name}":`),0) + width-1;
      if (bytes <= LIMIT) expected = '{"type":"object","properties":{' + names.map(name => `"${name}":${expected}`).join(',') + '}}';
    }
    const invoke = () => expandSource({path:'formal.json',text:`{"$contract":"contracts/${depth}.json#"}`,format:'json-schema'}, {
      stat:({path}) => ({exists:true,is_symlink:false,size:Buffer.byteLength(sources[path])}),read:({path}) => ({content:sources[path]}),
    });
    if (bytes > LIMIT) { assert.throws(invoke,error => error.code === 'contract-invalid' && /too big/.test(error.message) && error.message.includes('formal.json') && error.message.length <= 4000); refused++; }
    else { const got = invoke(); assert.equal(got.text,expected); assert.equal(Buffer.byteLength(got.text),bytes); assert.equal(got.references.length,depth+1); }
    cases++;
  }
  assert.equal(cases,20); assert.equal(refused,1);
});

test('FORMAL catalog: all 2 record counts x 2 annotation modes reuse a parsed document without cross-record mutation', () => {
  let cases = 0;
  for (const count of [2,8]) for (const annotated of [false,true]) {
    const raw = '{' + Array.from({length:count},(_,i) => `"r${i}":{"type":"object","properties":{"n":{"type":"number","default":9007199254740993}},"description":"record-${i}"}`).join(',') + '}';
    const parse = JSON.parse; let parses = 0;
    JSON.parse = function(text,...args) { if (text === raw) parses++; return parse.call(this,text,...args); };
    let catalog;
    try { catalog = catalogRecords([{path:'contracts/many.json',text:raw}],Array.from({length:count},(_,i) => `contracts/many.json#/r${i}/properties/n`)); }
    finally { JSON.parse = parse; }
    assert.equal(parses,1); assert.deepEqual(catalog.warnings,[]); assert.equal(catalog.records.length,1+2*count);
    for (let i=0;i<count;i++) {
      const target = `contracts/many.json#/r${i}`, selector = `{"$contract":"${target}"${annotated ? ',"description":"local"' : ''}}`;
      const result = expandSource({path:'formal.json',text:selector,format:'json-schema'}, {
        stat:() => ({exists:true,is_symlink:false,size:Buffer.byteLength(raw)}),read:() => ({content:raw}),
      });
      assert.ok(result.text.includes(`"description":"${annotated ? 'local' : `record-${i}`}"`));
      assert.match(result.text,/9007199254740993/);
      assert.ok(catalog.records.find(row => row.target === target).value_json.includes(`"description":"record-${i}"`));
    }
    cases++;
  }
  assert.equal(cases,4);
});

import test from 'node:test';
import assert from 'node:assert/strict';
import fs, { mkdirSync, readFileSync, writeFileSync, truncateSync, readdirSync, renameSync, symlinkSync } from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { join } from 'node:path';
import { expandSource, catalogRecords, compareCopies, planSync } from '../src/contract-refs.mjs';
import { captureSource, sourceFilePort, readPrompt, gitFiles, interfaceBlocks, LIMITS } from '../src/runtime-preflight.mjs';
import { runContracts } from '../src/contracts.mjs';
import { harbor, PLACE, sink } from './runtime-fake.mjs';

const input = properties => ({type:'object',properties,required:[],additionalProperties:false});
const shape = count => input(Object.fromEntries(Array.from({length:count},(_,i)=>[`f${i}`,{type:'string'}])));
const prompt = value => `# Exact prose\r\n<details><summary>Runtime interface</summary>\r\n\x60\x60\x60json\r\n${typeof value==='string'?value:JSON.stringify({status:'approved',prose_sha256:'retained',entries:[{input_schema:value}]})}\r\n\x60\x60\x60\r\n</details>\r\nTail.\r\n`;
const sources = value => [{path:'p.prompt.md',text:prompt(value)}];
const record = value => [{path:'contracts/x.json',target:'contracts/x.json#',value_json:JSON.stringify(value)}];
const port = values => ({stat:({path})=>({exists:Object.hasOwn(values,path),is_symlink:false,size:Buffer.byteLength(values[path]??'')}),read:({path})=>({content:values[path]})});
const expand = (text,values,format='json-schema') => expandSource({path:'consumer.prompt.md',text,format},port(values));
const write = (root,path,content) => {mkdirSync(join(root,path,'..'),{recursive:true});writeFileSync(join(root,path),typeof content==='string'?content:JSON.stringify(content));};

// These cases implement the reviewed native drift/sync criteria and provide
// independent assertions for each lead defect. Runtime JSON is never rewritten.
test('LEAD matching skips 0/1/2 fields, permits exact 3 and bounds near by canonical size',()=>{
  for(let copy=0;copy<=5;copy++) for(let canonical=0;canonical<=5;canonical++) {
    const got=compareCopies(sources(shape(copy)),record(shape(canonical)));
    const eligible=copy>=3 && (copy===canonical || canonical>=4 && Math.abs(copy-canonical)<=1);
    assert.equal(got.matches.length,eligible?1:0,`${copy} versus ${canonical}`);
    if(eligible)assert.equal(got.matches[0].kind,copy===canonical?'exact':'near');
  }
  const original=shape(3),changed=structuredClone(original);changed.properties.f0.minLength=1;
  assert.deepEqual(compareCopies(sources(changed),record(original)).matches,[]);
});

test('LEAD required/enum permutations preserve multiplicity and literal array ordering',()=>{
  const canonical=shape(4);canonical.required=['f0','f1','f0'];
  canonical.properties.f0={type:'array',items:{type:'number'},enum:[[1,2],[3,4],[1,2]]};
  const equal=structuredClone(canonical);equal.required=['f0','f0','f1'];equal.properties.f0.enum=[[1,2],[1,2],[3,4]];
  assert.equal(compareCopies(sources(equal),record(canonical)).matches[0].kind,'exact');
  const changed=structuredClone(equal);changed.properties.f0.enum[0]=[2,1];
  assert.equal(compareCopies(sources(changed),record(canonical)).matches[0].kind,'near');
  changed.properties.f0.enum=equal.properties.f0.enum;changed.required=['f0','f1','f1'];
  assert.equal(compareCopies(sources(changed),record(canonical)).matches[0].kind,'near');
  for(const keyword of ['default','const','examples']) {
    const a=structuredClone(canonical),b=structuredClone(canonical);
    a.properties.f1[keyword]={required:['a','b'],enum:[1,2]};b.properties.f1[keyword]={required:['b','a'],enum:[2,1]};
    assert.equal(compareCopies(sources(b),record(a)).matches[0].kind,'near',keyword);
  }
});

test('LEAD expansion preserves every consumer span and target layout including numeric keys',()=>{
  const target='{\n  "type" : "object",\n  "title" : "canonical",\n  "properties" : {"reasoning":{"type":"string"}, "answer":{"type":"string"}, "10":{"type":"number","default":1e400}, "2":{"type":"number","default":-0}},\n  "required" : [], "additionalProperties" : false\n}';
  const reference='{"$contract":"contracts/x.json#", "title":"local", "description":"new"}';
  const text=prompt(`{ "status" : "draft", "entries": [ { "input_schema" : ${reference}, "result_schema": {"default":9007199254740993,"enum":[3,2,1]} } ], "literal": {"$contract":"absent"} }`);
  const result=expand(text,{'contracts/x.json':target},'prompt');
  const insertion=target.replace('"canonical"','"local"').replace('\n}',',\n  "description" : "new"\n}');
  assert.equal(result.text,text.replace(reference,insertion));
  assert.ok(result.text.indexOf('"reasoning"')<result.text.indexOf('"answer"'));
  assert.ok(result.text.indexOf('"10"')<result.text.indexOf('"2"'));
  assert.ok(result.references[0].value_json.startsWith('{"additionalProperties":false,"properties":'));
  assert.match(result.references[0].value_json,/"default":1e400/);
});

test('LEAD substitutions preserve duplicate-key source spans and escaped key spellings',()=>{
  const text=' {"entries":[{"input_schema":0,"input_schema":{"$contract":"contracts/x.json#"}}],"literal":{"a":0,"a":{}}} ';
  const target='{"type":"object","properties":{"\\u0061":{"type":"string"}},"required":[],"additionalProperties":false}';
  const result=expand(prompt(text),{'contracts/x.json':target},'prompt');
  assert.equal(result.text,prompt(text).replace('{"$contract":"contracts/x.json#"}',target));
});

test('LEAD sync changes only copied schema and approved status value with the copied object layout',()=>{
  const schema=shape(3);schema.description='desc';schema.title='title';
  const inline=JSON.stringify(schema,null,2).replace(/\n/g,'\r\n');
  const text=prompt(`{ "status" : "approved", "prose_sha256":"retained", "entries" : [{"input_schema" : ${inline},"result_schema":{"enum":[3,1,2]}}] }`);
  const source={path:'p.prompt.md',text};
  const got=planSync([source],compareCopies([source],record(schema)).matches);
  const replacement='{\r\n  "$contract": "contracts/x.json#",\r\n  "description": "desc",\r\n  "title": "title"\r\n}';
  assert.equal(got.edits[0].after,text.replace(inline,replacement).replace('"approved"','"draft"'));
  assert.deepEqual(planSync([{path:source.path,text:got.edits[0].after}],compareCopies([{path:source.path,text:got.edits[0].after}],record(schema)).matches).edits,[]);
});

test('LEAD seeds preserve authored containers, numeric override order and independent scenarios',()=>{
  const seed='{\n "10": {"n":0},\n "2": {"n":1},\n "tail": true\n}';
  const text=' { "initial_world" : {"$seed":"contracts/world.json","set":{"/10":{"n":3},"/10/n":4,"/added":{"z":1,"a":2}}}, "literal":1.0 }\n';
  const got=expand(text,{'contracts/world.json':seed},'scenario');
  const expected=seed.replace('{"n":0}','{"n":4}').replace('"tail": true','"tail": true,\n "added": {"z":1,"a":2}');
  assert.equal(got.text,text.replace(text.slice(text.indexOf('{"$seed"'),text.indexOf(', "literal"')),expected));
  assert.equal(expand('{"initial_world":{"$seed":"contracts/world.json"}}',{'contracts/world.json':seed},'scenario').text,`{"initial_world":${seed}}`);
});

test('LEAD direct resolver stats before read and accepts exact UTF-8 byte boundaries',()=>{
  let reads=0;
  assert.throws(()=>expandSource({path:'origin',text:'{"$contract":"contracts/huge.json#"}',format:'json-schema'},{stat:()=>({exists:true,is_symlink:false,size:LIMITS.bytes+1}),read(){reads++;return{content:'{}'};}}),error=>error.code==='contract-invalid'&&/too big/.test(error.message)&&error.message.includes('origin')&&error.message.includes('contracts/huge.json#'));
  assert.equal(reads,0);
  for(const bytes of [LIMITS.bytes-1,LIMITS.bytes,LIMITS.bytes+1]) for(const unit of ['x','é']) {
    const overhead=Buffer.byteLength('{"value":""}'),count=Math.floor((bytes-overhead)/Buffer.byteLength(unit));
    const value='{"value":"'+unit.repeat(count)+'x'.repeat(bytes-overhead-count*Buffer.byteLength(unit))+'"}';
    assert.equal(Buffer.byteLength(value),bytes);
    if(bytes>LIMITS.bytes)assert.throws(()=>expand('{"$contract":"contracts/x.json#"}',{'contracts/x.json':value}),e=>e.code==='contract-invalid');
    else assert.equal(expand('{"$contract":"contracts/x.json#"}',{'contracts/x.json':value}).text,value);
  }
});

test('LEAD eight-way seven-level expansion halts with a finite diagnostic',t=>{
  const files={'contracts/0.json':JSON.stringify({type:'string',description:'x'.repeat(100)})};
  for(let level=1;level<=7;level++)files[`contracts/${level}.json`]=JSON.stringify(input(Object.fromEntries(Array.from({length:8},(_,i)=>[`f${i}`,{$contract:`contracts/${level-1}.json#`}]))));
  assert.ok(Object.values(files).reduce((sum,value)=>sum+Buffer.byteLength(value),0)<5000);
  assert.throws(()=>expand('{"$contract":"contracts/7.json#"}',files),error=>error.code==='contract-invalid'&&/too big/.test(error.message)&&error.message.includes('consumer.prompt.md')&&error.message.length<=4000);
  const {repo}=harbor(t);for(const [path,text] of Object.entries(files))write(repo,path,text);
  write(repo,'prompts/fanout.prompt.md',prompt({$contract:'contracts/7.json#'}));
  assert.throws(()=>captureSource(repo,{tests:['prompts/fanout.prompt.md']}),error=>error.exitCode===4&&/contract-invalid.*too big/.test(error.message)&&error.message.length<=4100);
});

test('LEAD expansion refuses a shallow two-branch oversized value before returning text',()=>{
  const leaf=JSON.stringify({type:'string',description:'x'.repeat(5_300_000)});
  const files={'contracts/a.json':leaf,'contracts/b.json':leaf};
  assert.throws(()=>expand(JSON.stringify(input({a:{$contract:'contracts/a.json#'},b:{$contract:'contracts/b.json#'}})),files),e=>e.code==='contract-invalid'&&/too big/.test(e.message));
});

test('LEAD catalog parses each complete JSON contract once and keeps selections immutable',()=>{
  for(const count of [256,512]) {
    const file=JSON.stringify({leaf:{type:'number',default:7},records:Object.fromEntries(Array.from({length:count},(_,i)=>[`r${i}`,input({a:{$contract:'contracts/list.json#/leaf'},b:{type:'string'},c:{type:'boolean'}})]))});
    const original=JSON.parse;let parses=0;
    try {
      JSON.parse=function(text,...args){if(text===file)parses++;return original(text,...args);};
      const catalog=catalogRecords([{path:'contracts/list.json',text:file}],['contracts/list.json#/leaf']);
      assert.deepEqual(catalog.warnings,[]);assert.equal(catalog.records.length,count+2);assert.equal(parses,1);
      assert.equal(JSON.parse(catalog.records.find(row=>row.target==='contracts/list.json#/records/r0').value_json).properties.a.default,7);
    } finally {JSON.parse=original;}
    let reads=0;const files=port({'contracts/list.json':file}),originalRead=files.read;
    files.read=args=>{reads++;return originalRead(args);};
    const text=JSON.stringify(input({first:{$contract:'contracts/list.json#/records/r0',title:'first'},second:{$contract:'contracts/list.json#/records/r0',title:'second'}}));
    const result=expandSource({path:'p',text,format:'json-schema'},files);
    assert.equal(reads,1);assert.equal(JSON.parse(result.text).properties.first.title,'first');assert.equal(JSON.parse(result.text).properties.second.title,'second');
    assert.equal(file.includes('"title"'),false);
    assert.equal(result.references.filter(ref=>ref.target==='contracts/list.json#/leaf').length,2);
  }
});

test('LEAD Markdown ATX C# title retains a literal hash',()=>{
  for(const heading of ['C#','C# ###']) {
    const value=`### ${heading}\n\x60\x60\x60json\n{"type":"string"}\n\x60\x60\x60\n`;
    let result;
    assert.doesNotThrow(()=>{result=expand('{"$contract":"contracts/x.md#C#"}',{'contracts/x.md':value});});
    assert.equal(result.references[0].target,'contracts/x.md#C#');
    assert.deepEqual(catalogRecords([{path:'contracts/x.md',text:value}]).records.map(row=>row.target),['contracts/x.md#C#']);
  }
});

test('LEAD native ports refuse sparse oversized raw files before any open including preparation replacement',t=>{
  const {repo}=harbor(t),path='large.txt';write(repo,path,'x');truncateSync(join(repo,path),2_147_483_649);
  const largePrompt='prompts/large.prompt.md';write(repo,largePrompt,'x');truncateSync(join(repo,largePrompt),LIMITS.bytes+1);
  const original=fs.openSync;let opens=0;
  t.after(()=>{fs.openSync=original;syncBuiltinESMExports();});
  fs.openSync=(file,...args)=>{if([join(repo,path),join(repo,largePrompt)].includes(file))opens++;return original(file,...args);};syncBuiltinESMExports();
  const tooBig=error=>error.exitCode===4&&/too big/.test(error.message)&&!(error instanceof RangeError);
  assert.throws(()=>sourceFilePort(repo).read({path}),tooBig);
  assert.throws(()=>readPrompt(repo,new Set(gitFiles(repo)),largePrompt),tooBig);
  assert.throws(()=>captureSource(repo,{tests:[path]}),tooBig);
  assert.throws(()=>captureSource(repo,{tests:[],prepareSource({readFile}){readFile(path);return[{path,bytes:'small'}];}}),tooBig);
  assert.equal(opens,0);
  // A replacement which never reads raw bytes may replace a large safe path.
  assert.equal(captureSource(repo,{tests:[],prepareSource:()=>[{path,bytes:'small'}]}).sources[0].bytes.toString(),'small');
});

test('LEAD native selected aggregate refuses before reads and unselected raw reference totals do not gate',t=>{
  const {repo}=harbor(t);write(repo,'a.txt','');write(repo,'b.txt','');truncateSync(join(repo,'a.txt'),6_291_456);truncateSync(join(repo,'b.txt'),4_194_305);
  const original=fs.openSync;let reads=0;
  t.after(()=>{fs.openSync=original;syncBuiltinESMExports();});
  fs.openSync=(file,...args)=>{if([join(repo,'a.txt'),join(repo,'b.txt')].includes(file))reads++;return original(file,...args);};syncBuiltinESMExports();
  assert.throws(()=>captureSource(repo,{tests:['a.txt','b.txt']}),e=>e.exitCode===4&&/too big/.test(e.message));assert.equal(reads,0);
  fs.openSync=original;syncBuiltinESMExports();
  const padding='x'.repeat(5_300_000);
  for(const name of ['a','b'])write(repo,`contracts/${name}.json`,JSON.stringify({leaf:{type:'string'},unused:padding}));
  const text=prompt(input({a:{$contract:'contracts/a.json#/leaf'},b:{$contract:'contracts/b.json#/leaf'}}));write(repo,'prompts/refs.prompt.md',text);
  const captured=captureSource(repo,{tests:['prompts/refs.prompt.md']});
  assert.ok(captured.bytes<1000);assert.equal(captured.files.length,1);assert.equal(captured.references.length,2);
});

test('LEAD native read and selected count boundaries allow equality and deduplicate paths',t=>{
  const {repo}=harbor(t),path='boundary.txt';write(repo,path,'');
  for(const size of [LIMITS.bytes-1,LIMITS.bytes,LIMITS.bytes+1]) {
    truncateSync(join(repo,path),size);
    if(size>LIMITS.bytes)assert.throws(()=>sourceFilePort(repo).read({path}),e=>e.exitCode===4&&/too big/.test(e.message));
    else assert.equal(Buffer.byteLength(sourceFilePort(repo).read({path}).content),size);
  }
  const paths=Array.from({length:10_001},(_,i)=>`count/${i}.txt`);
  for(const path of paths)write(repo,path,'');
  for(const count of [9_999,10_000]) {
    const tests=paths.slice(0,count);tests.push(paths[0]);
    const result=captureSource(repo,{tests});
    assert.equal(result.files.length,count);assert.equal(result.sources.length,count);assert.equal(result.bytes,0);assert.ok(result.tar.length<=LIMITS.bytes);
  }
  const original=fs.openSync;let reads=0;
  t.after(()=>{fs.openSync=original;syncBuiltinESMExports();});
  fs.openSync=(file,...args)=>{if(typeof file==='string'&&file.startsWith(join(repo,'count/')))reads++;return original(file,...args);};syncBuiltinESMExports();
  assert.throws(()=>captureSource(repo,{tests:paths}),e=>e.exitCode===4&&/10001 files/.test(e.message));assert.equal(reads,0);
});

test('LEAD Story footprints are independent of selected sibling tests without uploading them',t=>{
  const {repo}=harbor(t),one='tests/place-order.json',two='tests/sibling.json',story='user_stories/place-order.md';
  const sibling=JSON.parse(readFileSync(join(repo,one),'utf8'));
  sibling.steps.forEach(step=>step.entry_path='prompts/sibling.prompt.md');
  write(repo,two,sibling);write(repo,'docs/sibling.txt','original');
  write(repo,'prompts/sibling.prompt.md',readFileSync(join(repo,PLACE),'utf8').replace('## Dependencies','## Dependencies\n- [Sibling](../docs/sibling.txt)'));
  const single=captureSource(repo,{tests:[one]}),both=captureSource(repo,{tests:[one,two]}),all=captureSource(repo);
  const footprint=capture=>capture.stories.find(row=>row.story_path===story);
  assert.deepEqual(footprint(single),footprint(both));assert.deepEqual(footprint(single),footprint(all));
  assert.equal(single.files.some(file=>file.path===two),false);assert.equal(single.files.some(file=>file.path==='docs/sibling.txt'),false);
  assert.ok(footprint(single).files.some(file=>file.path==='docs/sibling.txt'));
  assert.equal(footprint(single).files.some(file=>file.path==='user_stories/unknown-item.md'),false);
  write(repo,'docs/sibling.txt','changed');
  assert.notDeepEqual(footprint(single).files,footprint(captureSource(repo,{tests:[one]})).files);
});

function syncSetup(t) {
  const setup=harbor(t),text=readFileSync(join(setup.repo,PLACE),'utf8'),block=interfaceBlocks(text)[0],value=JSON.parse(block[1]);
  write(setup.repo,'contracts/order.json',value.entries[0].input_schema);
  return {...setup,before:text,path:join(setup.repo,PLACE)};
}
const sync = setup => {const stdout=sink(),stderr=sink();return {code:runContracts({cwd:setup.repo,words:['sync'],options:{'--write':true}},{env:{HOME:setup.home},stdout,stderr}),stdout:stdout.text,stderr:stderr.text};};

test('LEAD atomic sync exposes only complete original until rename and cleans failed temporary writes',t=>{
  const setup=syncSetup(t),originalWrite=fs.writeSync,originalRename=fs.renameSync;let observed=0,renamed=0;
  t.after(()=>{fs.writeSync=originalWrite;fs.renameSync=originalRename;syncBuiltinESMExports();});
  fs.chmodSync(setup.path,0o764);const mask=process.umask(0o077);t.after(()=>process.umask(mask));
  fs.writeSync=(...args)=>{observed++;assert.equal(readFileSync(setup.path,'utf8'),setup.before);return originalWrite(...args);};
  fs.renameSync=(from,to)=>{if(to===setup.path){renamed++;assert.equal(readFileSync(setup.path,'utf8'),setup.before);assert.match(readFileSync(from,'utf8'),/"\$contract"/);}return originalRename(from,to);};syncBuiltinESMExports();
  assert.equal(sync(setup).code,0);assert.ok(observed>0);assert.equal(renamed,1);assert.match(readFileSync(setup.path,'utf8'),/"\$contract"/);assert.equal(fs.statSync(setup.path).mode&0o777,0o764);process.umask(mask);
  fs.renameSync=originalRename;
  const failure=syncSetup(t);
  fs.writeSync=(fd,...args)=>{originalWrite(fd,...args);throw new Error('synthetic temporary write failure');};syncBuiltinESMExports();
  const got=sync(failure);assert.equal(got.code,4);assert.match(got.stderr,/synthetic temporary write failure/);assert.equal(readFileSync(failure.path,'utf8'),failure.before);
  assert.equal(readdirSync(join(failure.repo,'prompts')).some(path=>path.startsWith('.pdd-sync-')),false);
});

test('LEAD atomic sync preserves concurrent inode replacement and symlink/ancestor swaps',t=>{
  const original=fs.writeSync;
  t.after(()=>{fs.writeSync=original;syncBuiltinESMExports();});
  for(const kind of ['content','inode','symlink','ancestor']) {
    const setup=syncSetup(t);let changed=false;
    fs.writeSync=(...args)=>{
      const result=original(...args);
      if(!changed){changed=true;
        if(kind==='content')writeFileSync(setup.path,'# Concurrent edit\n');
        if(kind==='inode'){writeFileSync(`${setup.path}.replacement`,'# Replacement\n');renameSync(`${setup.path}.replacement`,setup.path);}
        if(kind==='symlink'){renameSync(setup.path,`${setup.path}.saved`);symlinkSync(`${setup.path}.saved`,setup.path);}
        if(kind==='ancestor'){renameSync(join(setup.repo,'prompts'),join(setup.repo,'moved'));symlinkSync(join(setup.repo,'moved'),join(setup.repo,'prompts'));}
      }
      return result;
    };syncBuiltinESMExports();
    const got=sync(setup);assert.equal(got.code,4,kind);assert.match(got.stderr,/changed|symbolic link/,kind);
    if(kind==='content')assert.equal(readFileSync(setup.path,'utf8'),'# Concurrent edit\n');
    if(kind==='inode')assert.equal(readFileSync(setup.path,'utf8'),'# Replacement\n');
    if(kind==='symlink')assert.equal(fs.lstatSync(setup.path).isSymbolicLink(),true);
    if(kind==='ancestor')assert.equal(fs.lstatSync(join(setup.repo,'prompts')).isSymbolicLink(),true);
    assert.equal(readdirSync(join(setup.repo,kind==='ancestor'?'moved':'prompts')).some(path=>path.startsWith('.pdd-sync-')),false);
  }
});

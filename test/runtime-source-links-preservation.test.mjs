import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, symlinkSync, writeFileSync, unlinkSync, readFileSync, truncateSync } from 'node:fs';
import { join } from 'node:path';
import { captureSource, sourceFilePort } from '../src/runtime-preflight.mjs';
import { expandSource } from '../src/contract-refs.mjs';
import { bindingCoverage } from '../src/runtime-bindings.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, portsFor, PLACE } from './runtime-fake.mjs';
const ORDER='tests/place-order.json';
const write=(repo,path,bytes)=>{mkdirSync(join(repo,path,'..'),{recursive:true});writeFileSync(join(repo,path),bytes);};
function fixture(t) {
  const setup=harbor(t); write(setup.repo,'shared/data.json','{"type":"string"}');
  symlinkSync('shared/data.json',join(setup.repo,'alias.json'));
  return setup;
}
function accepted(repo) { assert.doesNotThrow(()=>sourceFilePort(repo).read({path:'alias.json'}),'approved linked source must be accepted first'); }

test('LINK preservation references: linked contract and seed stat/read expand without selection',t=>{
  const {repo}=fixture(t); accepted(repo);
  const port=sourceFilePort(repo);
  assert.deepEqual(port.stat({path:'alias.json'}),{exists:true,is_symlink:false,size:17});
  assert.equal(expandSource({path:'consumer',format:'json-schema',text:'{"$contract":"alias.json#"}'},port).text,'{"type":"string"}');
  assert.equal(expandSource({path:'consumer',format:'scenario',text:'{"initial_world":{"$seed":"alias.json"}}'},port).text,'{"initial_world":{"type":"string"}}');
  const captured=captureSource(repo,{tests:[ORDER],prepareSource({readFile,statFile}) {
    assert.equal(statFile('alias.json').size,17); assert.equal(readFile('alias.json').length,17); return [];
  }});
  assert.ok(!captured.files.some(f=>['alias.json','shared/data.json'].includes(f.path)));
});

test('LINK preservation bindings: root metadata follows safe source policy while executable declarations stay banned',async t=>{
  const {repo}=fixture(t); accepted(repo);
  write(repo,'inventory.json','{"schema_version":"pdd.bindings.v1","modules":[]}');
  symlinkSync('inventory.json',join(repo,'pdd-bindings.json'));
  const found={visible:new Set(['pdd-bindings.json','inventory.json','alias.json','shared/data.json']),stories:[]};
  assert.deepEqual(bindingCoverage({root:repo,found,selected:[]}),{available:true,bound:0,total:0,modules:[]});
  const {ports}=portsFor({HOME:join(repo,'..','home')},{gh:()=>assert.fail('offline auth'),fetch:()=>assert.fail('offline upload')});
  assert.equal(await runCheck({cwd:repo,words:['place-order'],options:{'--files':true}},ports),0,ports.stderr.text);
  write(repo,'inventory.json',JSON.stringify({schema_version:'pdd.bindings.v1',modules:[{module:'alias.json',stories:['missing.md'],reason:'native',port_attempt:'native filesystem'}]}));
  assert.throws(()=>bindingCoverage({root:repo,found,selected:[]}),/symlinks are not allowed/);
});

test('LINK preservation chains: internal absolute, folder aliases and duplicate binary payload remain authored',t=>{
  const {repo}=fixture(t); accepted(repo);
  const binary=Buffer.from([0,255,1,128,10]);write(repo,'shared/data.json',binary);
  symlinkSync(join(repo,'alias.json'),join(repo,'absolute.bin'));
  symlinkSync('shared',join(repo,'folder'));
  write(repo,'pdd-source.json',JSON.stringify({include:['absolute.bin','folder/data.json']}));
  const result=captureSource(repo,{tests:[ORDER]});
  for(const path of ['absolute.bin','folder/data.json']) {
    assert.deepEqual(result.files.find(f=>f.path===path),{path,size:5,target:'shared/data.json'});
    assert.deepEqual(result.sources.find(f=>f.path===path).bytes,binary);
  }
  assert.deepEqual(captureSource(repo,{tests:[ORDER]}).tar,result.tar);
});

for(const race of ['retarget','content','ancestor']) test(`LINK preservation capture retries changed ${race} observations`,t=>{
  const {repo}=fixture(t);accepted(repo);let attempts=0;
  const capture=captureSource(repo,{tests:[ORDER],prepareSource({statFile,readFile}) {
    attempts++;statFile('alias.json');
    if(attempts===1) {
      if(race==='retarget'){unlinkSync(join(repo,'alias.json'));symlinkSync('shared/data.json',join(repo,'alias.json'));}
      if(race==='content')write(repo,'shared/data.json','{"type":"number"}');
      if(race==='ancestor')write(repo,'shared/other.txt','changed parent identity metadata');
    }
    return [{path:'generated.bin',bytes:readFile('alias.json')}];
  }});
  assert.equal(attempts,2);
  assert.equal(capture.sources.find(f=>f.path==='generated.bin').bytes.toString(),readFileSync(join(repo,'shared/data.json'),'utf8'));
});

for(const kind of ['outside ancestor','secret intermediate']) test(`LINK preservation refusal: ${kind} never contributes bytes`,t=>{
  const {repo,sandbox}=fixture(t);accepted(repo);
  if(kind==='outside ancestor') {
    write(sandbox,'external/data.json','private outside');symlinkSync('../external',join(repo,'unsafe'));
    write(repo,'pdd-source.json','{"include":["unsafe/data.json"]}');
    assert.throws(()=>captureSource(repo,{tests:[ORDER]}),error=>error.exitCode===4 && /unsafe.*external.*outside/.test(error.message));
  } else {
    write(repo,'secrets/data.json','private secret');symlinkSync('secrets/data.json',join(repo,'middle.json'));
    symlinkSync('middle.json',join(repo,'unsafe.json'));
    write(repo,'pdd-source.json','{"include":["unsafe.json"]}');
    assert.throws(()=>captureSource(repo,{tests:[ORDER]}),error=>error.exitCode===4 && /unsafe.json.*secrets.*secret/.test(error.message));
  }
});

test('LINK preservation framing: unicode long authored alias uses PAX and aliases retain byte totals',t=>{
  const {repo}=fixture(t);accepted(repo);
  const path=`${'long'.repeat(28)}é.bin`, payload=Buffer.from([0,255,10]);
  write(repo,'shared/data.json',payload);symlinkSync('shared/data.json',join(repo,path));
  write(repo,'pdd-source.json',JSON.stringify({include:[path,'alias.json']}));
  const capture=captureSource(repo,{tests:[ORDER]});
  assert.ok(capture.tar.includes(Buffer.from(`path=${path}\n`)));
  assert.equal(capture.files.filter(f=>f.target==='shared/data.json').reduce((sum,f)=>sum+f.size,0),6);
  assert.deepEqual(capture.sources.find(f=>f.path===path).bytes,payload);
});


test('LINK preservation discovery: linked entry prompt is available to offline checks',async t=>{
  const {repo,home}=fixture(t);accepted(repo);
  const original=readFileSync(join(repo,PLACE));
  unlinkSync(join(repo,PLACE));write(repo,'shared/entry.prompt.md',original);
  symlinkSync('../shared/entry.prompt.md',join(repo,PLACE));
  const {ports}=portsFor({HOME:home},{gh:()=>assert.fail('offline auth'),fetch:()=>assert.fail('offline network')});
  assert.equal(await runCheck({cwd:repo,words:['place-order'],options:{'--files':true}},ports),0,ports.stderr.text);
  assert.ok(ports.stdout.text.includes(`${PLACE} -> shared/entry.prompt.md`));
});


test('LINK preservation limits: each selected alias counts its full target bytes',t=>{
  const {repo}=fixture(t);accepted(repo);
  truncateSync(join(repo,'shared/data.json'),6*1024*1024);
  symlinkSync('shared/data.json',join(repo,'second.json'));
  write(repo,'pdd-source.json','{"include":["alias.json","second.json"]}');
  assert.throws(()=>captureSource(repo,{tests:[ORDER]}),error=>error.exitCode===4 && /too big.*12.0 MB/s.test(error.message));
});

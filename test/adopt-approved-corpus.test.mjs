import test from 'node:test';
import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {existsSync,mkdirSync,mkdtempSync,readFileSync,realpathSync,rmSync,writeFileSync,symlinkSync,linkSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {dirname,join} from 'node:path';
import {adoptReplayCorpus,pinReplayVectors,sourceFingerprint} from '../src/workflow-replay.mjs';
function fixture(t) {
  const base=realpathSync(mkdtempSync(join(tmpdir(),'pdd-corpus-')));t.after(()=>rmSync(base,{recursive:true,force:true}));
  const root=join(base,'repo');mkdirSync(root);
  const git=(...args)=>execFileSync('git',args,{cwd:root,encoding:'utf8'}).trim();
  const put=(path,bytes)=>{mkdirSync(dirname(join(root,path)),{recursive:true});writeFileSync(join(root,path),bytes);};
  git('init','-q');git('remote','add','origin','https://github.com/example/project.git');
  put('prompts/one.prompt.md','# One\n## Dependencies\n- [Rules](../rules/one.md)\n');
  put('rules/one.md','# Rules\n## Dependencies\n- [Deep](deep.md)\n');put('rules/deep.md','Deep rule.\n');
  put('prompts/two.prompt.md','# Second entry\n');put('stories/use.md','# Story\n');put('context.txt','Scenario context.\n');
  const vector={schema_version:'prompt-runtime.program-scenario.v1',story_path:'stories/use.md',context:[{prompt_path:'prompts/two.prompt.md',paths:['context.txt']}],steps:[{step_id:'one',entry_path:'prompts/one.prompt.md',operation:'one',checks:[{criterion_id:'AC1',target:'result',path:'/ok',op:'equals',value:true}]},{step_id:'two',entry_path:'prompts/two.prompt.md',operation:'two',checks:[{criterion_id:'AC1',target:'calls',path:'/save',op:'equals',value:0}]}]};
  put('arbitrary/é corpus.json',JSON.stringify(vector)+'\n');put('ordinary.json','{}\n');put('empty.txt','');
  git('add','.');git('-c','user.name=Test','-c','user.email=test@example.invalid','commit','-qm','Approved synthetic corpus');
  const declaration={schema_version:'pdd.replay-adoption.v1',repository:'example/project',commit:git('rev-parse','HEAD'),prompts:['prompts/one.prompt.md'],scenarios:['arbitrary/é corpus.json'],approval:{kind:'external-human-assertion',reference:'review:42',asserted_by:'Synthetic reviewer'}};
  const file=join(base,'declaration.json');const save=()=>writeFileSync(file,JSON.stringify(declaration));save();
  return {root,base,file,declaration,save,put,git,vector,adopt:()=>adoptReplayCorpus(root,file)};
}
test('2640 native: enumerate original Git blobs and complete closure; unrelated code allowed',async t=>{
  const f=fixture(t),before=pinReplayVectors(f.root,['arbitrary/é corpus.json']);
  assert.equal((await f.adopt()).outcome,'adopted');const old=sourceFingerprint(f.root);f.put('new-code.mjs','export const x=1;\n');
  const result=await f.adopt();assert.equal(result.outcome,'adopted');assert.deepEqual(result.paths,['arbitrary/é corpus.json']);assert.notEqual(old,sourceFingerprint(f.root));
  assert.deepEqual(pinReplayVectors(f.root,result.paths),before);assert.equal(result.provenance.commit,f.declaration.commit);assert.equal(result.provenance.trust,'external-assertion-unverified');
});
for(const path of ['prompts/one.prompt.md','prompts/two.prompt.md','rules/deep.md','stories/use.md','context.txt','arbitrary/é corpus.json']) test(`2640 native: raw bytes cover ${path}`,async t=>{
  const f=fixture(t);f.put(path,readFileSync(join(f.root,path),'utf8')+'\n');const result=await f.adopt();assert.equal(result.outcome,'blocked');assert.equal(result.reason,'content-mismatch');
});
for(const mode of ['missing','empty','symlink','hardlink','cycle','missing-context','call-context']) test(`2640 native: fail closed ${mode}`,async t=>{
  const f=fixture(t),path=join(f.root,'arbitrary/é corpus.json');
  if(mode==='added')f.put('outside/new.json',JSON.stringify(f.vector));
  if(mode==='missing')rmSync(path);
  if(mode==='malformed')f.put('ordinary.json','{');
  if(mode==='untracked-malformed')f.put('elsewhere.json','{');
  if(mode==='empty')f.put('arbitrary/é corpus.json','');
  if(mode==='symlink'){rmSync(path);symlinkSync(join(f.root,'ordinary.json'),path);}
  if(mode==='hardlink'){rmSync(path);linkSync(join(f.root,'ordinary.json'),path);}
  if(mode==='cycle')f.put('rules/deep.md','# Loop\n## Dependencies\n[Back](one.md)\n');
  if(mode==='missing-context')rmSync(join(f.root,'context.txt'));
  if(mode==='call-context')f.put('prompts/two.prompt.md','# Call\n```json\n{"calls":[{"target":"missing.prompt.md"}]}\n```\n');
  assert.equal((await f.adopt()).outcome,'blocked');
});
for(const mode of ['missing','json','version','repository','commit','assertion','blank','duplicate-prompts','path','large','symlink','hardlink','ancestor'])test(`2640 declaration safety ${mode}`,async t=>{
  const f=fixture(t);
  if(mode==='missing')rmSync(f.file);
  else if(mode==='json')writeFileSync(f.file,'{');
  else if(mode==='large')writeFileSync(f.file,' '.repeat(65537));
  else if(mode==='symlink'){const other=join(f.base,'other');writeFileSync(other,readFileSync(f.file));rmSync(f.file);symlinkSync(other,f.file);}
  else if(mode==='hardlink')linkSync(f.file,join(f.base,'other'));
  else if(mode==='ancestor'){symlinkSync(f.base,join(f.base,'alias'));f.file=join(f.base,'alias','declaration.json');assert.equal((await adoptReplayCorpus(f.root,f.file)).outcome,'adopted');return;}
  else {if(mode==='version')f.declaration.schema_version='wrong';if(mode==='repository')f.declaration.repository='foreign/repo';if(mode==='commit')f.declaration.commit='f'.repeat(40);if(mode==='assertion')f.declaration.approval.kind='agent-prose';if(mode==='blank')f.declaration.approval.asserted_by=' ';if(mode==='duplicate-prompts')f.declaration.prompts.push(f.declaration.prompts[0]);if(mode==='path')f.declaration.prompts=['../escape'];f.save();}
  assert.equal((await adoptReplayCorpus(f.root,f.file)).outcome,'blocked');
});
test('2640 snapshot failures, malformed facts, duplicate inventories and throw never adopt',async()=>{
  const doc=JSON.parse(readFileSync(new URL('./runtime/adopt-approved-corpus.json',import.meta.url))),original=doc.initial_world.snapshots[0].snapshot;
  for(const change of [s=>s.approved_vectors=[],s=>s.current_vectors.push(s.current_vectors[0]),s=>s.current_context.push(s.current_context[0]),s=>s.current_context[0].sha256='x',s=>s.current_vectors[0].checks=[],s=>s.declaration.prompts=[],s=>s.available='true']) {
    const snapshot=structuredClone(original);change(snapshot);const result=await adoptReplayCorpus('unused','unused',{readAdoptionSnapshot:async()=>({snapshot})});assert.equal(result.outcome,'blocked');assert.deepEqual(result.paths,[]);
  }
  assert.equal((await adoptReplayCorpus('unused','unused',{readAdoptionSnapshot:async()=>{throw Error('Unavailable');}})).reason,'unavailable');
});
test('2640 native preserves long composite check identities and exact whitespace/NUL Git paths',async t=>{
  const f=fixture(t),path='arbitrary/ café \n.json';
  f.vector.steps[0].operation='o'.repeat(900);f.vector.steps[0].step_id='\u0001'.repeat(900);f.vector.steps[0].checks[0].criterion_id='\u0001'.repeat(900);
  rmSync(join(f.root,'arbitrary/é corpus.json'));f.put(path,JSON.stringify(f.vector)+'\n');f.git('add','-A');f.git('-c','user.name=Test','-c','user.email=test@example.invalid','commit','-qm','Approved long identities');f.declaration.commit=f.git('rev-parse','HEAD');f.declaration.scenarios=[path];f.save();
  const result=await f.adopt();assert.equal(result.outcome,'adopted',result.reason);assert.deepEqual(result.paths,[path]);
  const anchor=pinReplayVectors(f.root,result.paths);assert.equal(anchor.vectors[0].checks[0].operation,'o'.repeat(900));assert.equal(anchor.vectors[0].checks[0].criterion_id,'\u0001'.repeat(900));
});
test('2640 native scratch Git and source selector cannot inherit source index/worktree environment',async t=>{
  const f=fixture(t),index=join(f.root,'.git/index'),before=readFileSync(index),status=f.git('status','--porcelain');
  const moduleUrl=new URL('../src/workflow-replay.mjs',import.meta.url).href;
  const script=`import {adoptReplayCorpus} from ${JSON.stringify(moduleUrl)};process.stdout.write(JSON.stringify(await adoptReplayCorpus(process.argv[1],process.argv[2])));`;
  const reply=execFileSync(process.execPath,['--input-type=module','-e',script,f.root,f.file],{encoding:'utf8',env:{...process.env,GIT_DIR:join(f.root,'.git'),GIT_WORK_TREE:f.root,GIT_INDEX_FILE:index,GIT_CONFIG_COUNT:'1',GIT_CONFIG_KEY_0:'core.worktree',GIT_CONFIG_VALUE_0:f.root}});
  assert.equal(JSON.parse(reply).outcome,'adopted');assert.deepEqual(readFileSync(index),before);assert.equal(f.git('status','--porcelain'),status);
});
test('2640 native leaves large unrelated implementation files outside context validation',async t=>{
  const f=fixture(t);f.put('large-implementation.dat',Buffer.alloc(11*1024*1024));assert.equal((await f.adopt()).outcome,'adopted');
});
for(const mode of ['call','self','cycle'])test(`2640 native approved required ${mode} context is resolved independently`,async t=>{
  const f=fixture(t);
  const target=mode==='call'?'prompts/called.prompt.md':mode==='self'?'prompts/two.prompt.md':'prompts/one.prompt.md';
  f.put('prompts/two.prompt.md',`# Two\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify({calls:[{target}]})}\n\`\`\`\n</details>\n`);
  if(mode==='call')f.put('prompts/called.prompt.md','Called context.\n');
  if(mode==='cycle')f.put('prompts/one.prompt.md','# One\n## Dependencies\n[Two](two.prompt.md)\n');
  f.git('add','-A');f.git('-c','user.name=Test','-c','user.email=test@example.invalid','commit','-qm','Approved required context');f.declaration.commit=f.git('rev-parse','HEAD');f.save();
  const result=await f.adopt();assert.equal(result.outcome,mode==='call'?'adopted':'blocked',result.reason);
  if(mode==='call'){f.put(target,'Changed called context.\n');assert.equal((await f.adopt()).reason,'content-mismatch');}
});

test('2640 positive helper supports symlink TMPDIR and declaration parent, with strict native snapshot',async t=>{
  const f=fixture(t),alias=join(f.base,'tmp-alias');symlinkSync(f.base,alias);
  const moduleUrl=new URL('../src/workflow-replay.mjs',import.meta.url).href;
  const script=`import assert from 'node:assert/strict';import {adoptReplayCorpus} from ${JSON.stringify(moduleUrl)};let snapshot,bytes;const result=await adoptReplayCorpus(process.argv[1],process.argv[2],{onSnapshot:s=>snapshot=s,onNativeDeclaration:b=>bytes=b});assert.equal(result.outcome,'adopted',JSON.stringify(result));assert.equal(snapshot.approved_commit_ancestor,true);assert.equal(snapshot.cause,'');assert.equal(Object.hasOwn(snapshot,'declaration_bytes'),false);assert.ok(Buffer.isBuffer(bytes));console.log(result.outcome);`;
  assert.equal(execFileSync(process.execPath,['--input-type=module','-e',script,f.root,join(alias,'declaration.json')],{env:{...process.env,TMPDIR:alias},encoding:'utf8'}).trim(),'adopted');
});
test('2640 declared scope ignores malformed JSON and broken Harbor-like fixture',async t=>{
  const f=fixture(t);f.put('ordinary.json','{');f.put('test/fixtures/harbor/tests/order.json',JSON.stringify({...f.vector,steps:[{...f.vector.steps[0],entry_path:'prompts/place_order.prompt.md'}]}));
  assert.equal((await f.adopt()).outcome,'adopted');
  f.git('add','-A');f.git('-c','user.name=Test','-c','user.email=test@example.invalid','commit','-qm','Unrelated fixtures');f.declaration.commit=f.git('rev-parse','HEAD');f.save();
  assert.equal((await f.adopt()).outcome,'adopted');
});
test('2640 equal bytes on unrelated commit fail real ancestry, explicit descendant base succeeds',async t=>{
  const f=fixture(t),original=f.declaration.commit,tree=f.git('rev-parse','HEAD^{tree}');
  const unrelated=execFileSync('git',['-c','user.name=Test','-c','user.email=test@example.invalid','commit-tree',tree],{cwd:f.root,input:'Unrelated approval\n',encoding:'utf8'}).trim();
  f.declaration.commit=unrelated;f.save();assert.equal((await f.adopt()).reason,'unrelated-commit');
  f.declaration.commit=original;f.save();f.git('branch','topic');
  assert.equal((await adoptReplayCorpus(f.root,f.file,{currentRef:'topic'})).outcome,'adopted');
  assert.equal((await adoptReplayCorpus(f.root,f.file,{currentRef:unrelated})).reason,'unrelated-commit');
});
test('2640 selected sets must equal declaration even when both snapshots agree on subset or extra',async()=>{
  const doc=JSON.parse(readFileSync(new URL('./runtime/adopt-approved-corpus.json',import.meta.url))),original=doc.initial_world.snapshots[0].snapshot;
  for(const mode of ['subset','extra']) {
    const snapshot=structuredClone(original);
    if(mode==='subset')snapshot.declaration.scenarios.push('tests/missing.json');
    else {const row={...snapshot.approved_vectors[0],path:'tests/extra.json'};snapshot.approved_vectors.push(row);snapshot.current_vectors.push(row);}
    const result=await adoptReplayCorpus('unused','unused',{readAdoptionSnapshot:async()=>({snapshot})});assert.equal(result.reason,'inventory-mismatch');
  }
});

test('2640 immutable corpus reads batch Git blobs across many declared scenarios',async t=>{
  const f=fixture(t);for(let i=0;i<30;i++){const path=`tests/vector-${i}.json`;f.put(path,JSON.stringify(f.vector));f.declaration.scenarios.push(path);}
  f.git('add','-A');f.git('-c','user.name=Test','-c','user.email=test@example.invalid','commit','-qm','Large declared corpus');f.declaration.commit=f.git('rev-parse','HEAD');f.save();
  const bin=join(f.base,'bin');mkdirSync(bin);const log=join(f.base,'git.log');
  const git=execFileSync('which',['git'],{encoding:'utf8'}).trim();
  writeFileSync(join(bin,'git'),`#!/bin/sh\nprintf '%s\\n' "$*" >> "$PDD_GIT_LOG"\nexec '${git.replaceAll("'","'\\''")}' "$@"\n`,{mode:0o755});
  const script=`import {adoptReplayCorpus} from ${JSON.stringify(new URL('../src/workflow-replay.mjs',import.meta.url).href)};console.log(JSON.stringify(await adoptReplayCorpus(process.argv[1],process.argv[2])));`;
  const result=JSON.parse(execFileSync(process.execPath,['--input-type=module','-e',script,f.root,f.file],{env:{...process.env,PATH:`${bin}:${process.env.PATH}`,PDD_GIT_LOG:log},encoding:'utf8'}));
  assert.equal(result.outcome,'adopted',result.cause);assert.equal(result.paths.length,31);
  const commands=readFileSync(log,'utf8').trim().split('\n'),batch=commands.filter(c=>c==='cat-file --batch');
  assert.ok(batch.length>0 && batch.length<12,`31 scenarios used ${batch.length} batch starts`);
  assert.equal(commands.filter(c=>/^cat-file (?:-s|blob)/.test(c)).length,0);
  t.diagnostic(`31 declared scenarios: ${batch.length} cat-file --batch starts; zero per-file cat-file starts`);
});

test('2640 refusal causes are useful, bounded single lines without private paths credentials or Simulator URLs',async()=>{
  const result=await adoptReplayCorpus('unused','unused',{readAdoptionSnapshot:async()=>{throw Error('Read failed: ENOENT prompts/missing.prompt.md /private/person/corpus.json password=secret Authorization: Bearer hiddenToken ghp_hiddenCredential https://runtime.invalid/s/capability\nnext');}});
  assert.equal(result.reason,'unavailable');assert.match(result.cause,/Read failed: ENOENT prompts\/missing\.prompt\.md/);assert.ok(result.cause.length<=1000);assert.doesNotMatch(result.cause,/private|person|secret|hiddenToken|hiddenCredential|capability|https:|[\r\n]/);
});

for(const mode of ['over-limit','missing-key','duplicate','noncanonical','git-case'])test(`2640 rework native declaration cause ${mode}`,async t=>{
  const f=fixture(t),path='arbitrary/é corpus.json';
  const fragments={
    'over-limit':['scenarios','201','200'],
    'missing-key':['scenarios','missing'],
    duplicate:['duplicate',path],
    noncanonical:['noncanonical','./tests/a.json'],
    'git-case':['noncanonical','.GIT/config']
  };
  if(mode==='over-limit')f.declaration.scenarios=Array.from({length:201},(_,i)=>`tests/${i}.json`);
  if(mode==='missing-key')delete f.declaration.scenarios;
  if(mode==='duplicate')f.declaration.scenarios.push(path);
  if(mode==='noncanonical')f.declaration.scenarios=['./tests/a.json'];
  if(mode==='git-case')f.declaration.scenarios=['.GIT/config'];
  f.save();const result=await f.adopt();assert.equal(result.reason,'invalid-approval');
  for(const fragment of fragments[mode])assert.ok(result.cause.includes(fragment),`Missing ${fragment} in ${result.cause}`);
  assert.doesNotMatch(result.cause,/[\r\n]/);assert.ok(!result.cause.includes(f.base));
});
for(const mode of ['approved','current-commit','deleted-worktree'])test(`2640 rework native missing scenario names source and relative path ${mode}`,async t=>{
  const f=fixture(t),path='arbitrary/é corpus.json';
  let result;
  if(mode==='approved'){f.declaration.scenarios=['tests/missing.json'];f.save();result=await f.adopt();}
  else {
    rmSync(join(f.root,path));
    if(mode==='current-commit'){
      f.git('add','-A');f.git('-c','user.name=Test','-c','user.email=test@example.invalid','commit','-qm','Remove current scenario');
      result=await adoptReplayCorpus(f.root,f.file,{currentRef:'HEAD'});
    }else result=await f.adopt();
  }
  assert.equal(result.reason,'unavailable');assert.match(result.cause,/missing/i);
  assert.match(result.cause,mode==='approved'?/approved/i:/current/i);
  assert.ok(result.cause.includes(mode==='approved'?'tests/missing.json':path),result.cause);
  assert.ok(!result.cause.includes(f.base));assert.doesNotMatch(result.cause,/[\r\n]/);
});
test('2640 rework malformed declaration paths retain useful cause without credentials or host paths',async t=>{
  const f=fixture(t);f.declaration.scenarios=['./tests/a.json\npassword=hiddenPassword ghp_hiddenCredential https://runtime.invalid/s/capability /private/person/data'];f.save();
  const result=await f.adopt();assert.equal(result.reason,'invalid-approval');assert.match(result.cause,/noncanonical/);assert.ok(result.cause.includes('./tests/a.json'));
  assert.doesNotMatch(result.cause,/hiddenPassword|hiddenCredential|capability|https:|private|person|[\r\n]/);
});
test('2640 rework rejects case-variant Git directory in approved tree before scratch writes',async t=>{
  const f=fixture(t),index=readFileSync(join(f.root,'.git/index'));
  const gitInput=(args,input)=>execFileSync('git',args,{cwd:f.root,input,encoding:'utf8'}).trim();
  const blob=gitInput(['hash-object','-w','--stdin'],`[core]\nworktree = ${f.root}\n`);
  const subtree=gitInput(['mktree'],`100644 blob ${blob}\tconfig\n`);
  const tree=gitInput(['mktree'],f.git('ls-tree','HEAD')+`\n040000 tree ${subtree}\t.GIT\n`);
  const commit=gitInput(['-c','user.name=Test','-c','user.email=test@example.invalid','commit-tree',tree,'-p',f.declaration.commit],'Synthetic unsafe tree\n');
  f.git('update-ref','HEAD',commit);f.declaration.commit=commit;f.save();
  // Observe the scratch view at its Git boundary: no source-controlled .GIT
  // config may be present when Git initializes it, even on case-sensitive CI.
  const bin=join(f.base,'bin'),marker=join(f.base,'unsafe-view');mkdirSync(bin);
  const git=execFileSync('which',['git'],{encoding:'utf8'}).trim();
  writeFileSync(join(bin,'git'),`#!/bin/sh\nif [ "$1" = init ] && [ -e .GIT/config ]; then printf unsafe > "$PDD_UNSAFE_VIEW"; fi\nexec '${git.replaceAll("'","'\\''")}' "$@"\n`,{mode:0o755});
  const script=`import {adoptReplayCorpus} from ${JSON.stringify(new URL('../src/workflow-replay.mjs',import.meta.url).href)};console.log(JSON.stringify(await adoptReplayCorpus(process.argv[1],process.argv[2])));`;
  const result=JSON.parse(execFileSync(process.execPath,['--input-type=module','-e',script,f.root,f.file],{encoding:'utf8',env:{...process.env,PATH:`${bin}:${process.env.PATH}`,PDD_UNSAFE_VIEW:marker}}));
  assert.equal(existsSync(marker),false,'Git must never initialize a view containing the tree-controlled .GIT/config');
  assert.equal(result.reason,'unavailable');assert.match(result.cause,/path/i);assert.ok(result.cause.includes('.GIT/config'),result.cause);
  assert.deepEqual(readFileSync(join(f.root,'.git/index')),index);assert.doesNotMatch(f.git('config','--local','--list'),/^core\.worktree=/m);
});

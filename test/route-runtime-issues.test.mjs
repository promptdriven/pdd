import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile, mkdtemp, writeFile, rm, mkdir, readdir } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { parseClassification, issueVersion, buildRoutingPlan, routeRuntimeIssues } from '../scripts/route-runtime-issues.mjs';

const exec = promisify(execFile);
const cases = JSON.parse(await readFile(new URL('./fixtures/runtime-router/classifications.json', import.meta.url)));
const runtime = { ownership:'runtime', reason:'Execution loses saved state after the call.' };
const issue = { number:8, title:'Runtime loses state', body:'State disappears after execution.', state:'open', labels:[], assignees:[] };
const marker = '<!-- pdd-runtime-router -->';
for (const row of cases) test(`classifier parser: ${row.name}`, () => {
  if (row.expected) assert.deepEqual(parseClassification(row.text), row.expected);
  else assert.throws(() => parseClassification(row.text), /^Error: Invalid classifier response$/);
});
test('classifier parser rejects nontext and oversized/control reasons', () => {
  for (const text of [null, {}, JSON.stringify({...runtime,reason:'x'.repeat(301)}), JSON.stringify({...runtime,reason:'hello\u0000world'})]) {
    assert.throws(() => parseClassification(text), /Invalid classifier response/);
  }
});
test('dry-run plan lists only label, additive assignment and one explanatory comment', () => {
  assert.deepEqual(buildRoutingPlan({issue,version:'v',classification:runtime,owner:'runtime-owner',comments:[]}), {
    number:8,version:'v',...runtime,actions:[
      {type:'label',label:'pdd:runtime'}, {type:'assign',owner:'runtime-owner'},
      {type:'comment',body:`Runtime ownership: Execution loses saved state after the call.

${marker}`},
    ],
  });
});
test('existing metadata, marker and completed routing suppress duplicate effects', () => {
  const current = {...issue,labels:[{name:'pdd:runtime'}],assignees:[{login:'runtime-owner'},{login:'other'}]};
  const options = {issue:current,version:'v',classification:runtime,owner:'runtime-owner',comments:[{body:marker}]};
  assert.deepEqual(buildRoutingPlan(options).actions, []);
  assert.deepEqual(buildRoutingPlan({...options,issue,applied:true}).actions, []);
  for (const ownership of ['pdd','uncertain']) assert.deepEqual(buildRoutingPlan({...options,issue,classification:{...runtime,ownership}}).actions, []);
  assert.deepEqual(buildRoutingPlan({...options,issue:{...issue,state:'closed'}}).actions, []);
});
test('comment reason cannot inject mentions or Markdown', () => {
  const [,,comment] = buildRoutingPlan({issue,version:'v',classification:{...runtime,reason:'@someone [click](https://example.test) <script>'},owner:'runtime-owner',comments:[]}).actions;
  assert.equal(comment.body, `Runtime ownership: \\@someone \\[click\\]\\(https://example\\.test\\) \\<script\\>

${marker}`);
});
test('content hashes ignore router effects but include human edits and repository identity', () => {
  const comment = {id:2,body:'Observed after the call',updated_at:'2026-11-10T00:00:00Z'};
  const version = issueVersion('team/project',issue,[comment]);
  assert.match(version,/^[a-f0-9]{64}$/);
  assert.equal(issueVersion('team/project',{...issue,labels:[{name:'pdd:runtime'}],assignees:[{login:'owner'}],updated_at:'later'},[comment,{id:3,body:marker,updated_at:'later'}]),version);
  assert.notEqual(issueVersion('team/other',issue,[comment]),version);
  assert.notEqual(issueVersion('team/project',{...issue,body:'Edited'},[comment]),version);
  assert.notEqual(issueVersion('team/project',issue,[{...comment,body:'Edited'}]),version);
  assert.equal(issueVersion('team/project',issue,[comment,{...comment,id:1}]),issueVersion('team/project',issue,[{...comment,id:1},comment]));
});

function fakePorts(overrides={}) {
  const cache = new Map(), writes=[], calls=[];
  const ports = {
    listIssues:async()=>[issue], getIssue:async()=>issue, listComments:async()=>[],
    readCache:async key=>cache.get(key)??null,
    writeCache:async(key,value)=>{cache.set(key,structuredClone(value));},
    classify:async evidence=>{calls.push(evidence);return JSON.stringify(runtime);},
    addLabel:async(...args)=>writes.push(['label',...args]),
    addAssignee:async(...args)=>writes.push(['assign',...args]),
    postComment:async(...args)=>writes.push(['comment',...args]),
    ...overrides,
  };
  return {cache,writes,calls,ports};
}
const options = {repo:'team/project',owner:'runtime-owner'};
test('routing dry run never writes GitHub and caches each content version', async () => {
  const f = fakePorts();
  const first = await routeRuntimeIssues(options,f.ports);
  assert.equal(first[0].actions.length,3);
  assert.deepEqual(await routeRuntimeIssues(options,f.ports),first);
  assert.equal(f.calls.length,1);
  assert.deepEqual(f.writes,[]);
  assert.deepEqual(f.calls[0],{repository:'team/project',number:8,title:issue.title,body:issue.body,comments:[]});
  f.ports.listIssues=async()=>[{...issue,title:'Edited title'}];
  await routeRuntimeIssues(options,f.ports);
  assert.equal(f.calls.length,2);
});
test('failed classification is cached without raw diagnostics and does not retry', async () => {
  let attempts=0;
  const f = fakePorts({classify:async()=>{attempts++;throw Error('SECRET');}});
  const first = await routeRuntimeIssues(options,f.ports);
  assert.match(first[0].error,/Classification failed/);
  await routeRuntimeIssues({...options,apply:true},f.ports);
  assert.equal(attempts,1);
  assert.deepEqual(f.writes,[]);
  assert.ok(!JSON.stringify([...f.cache]).includes('SECRET'));
});
test('invalid output and corrupt cache fail closed', async () => {
  for (const result of ['oops',JSON.stringify({...runtime,reason:''})]) {
    const f=fakePorts({classify:async()=>result});
    assert.ok((await routeRuntimeIssues({...options,apply:true},f.ports))[0].error);
    assert.deepEqual(f.writes,[]);
  }
  const f=fakePorts({readCache:async()=>({classification:{ownership:'runtime'},appliedOwners:[]})});
  assert.ok((await routeRuntimeIssues({...options,apply:true},f.ports))[0].error);
  assert.equal(f.calls.length,0);
  assert.deepEqual(f.writes,[]);
});
test('apply reuses dry-run classification; receipt respects later manual undo', async () => {
  const f=fakePorts();
  await routeRuntimeIssues(options,f.ports);
  await routeRuntimeIssues({...options,apply:true},f.ports);
  assert.deepEqual(f.writes.map(x=>x[0]),['label','assign','comment']);
  assert.equal(f.calls.length,1);
  const after=await routeRuntimeIssues({...options,apply:true},f.ports);
  assert.deepEqual(after[0].actions,[]);
  assert.equal(f.writes.length,3);
  await routeRuntimeIssues({...options,owner:'new-owner',apply:true},f.ports);
  assert.equal(f.calls.length,1);
});
test('preflight refuses changed or closed issues before any writes', async () => {
  for (const getIssue of [async()=>({...issue,title:'Changed'}),async()=>({...issue,state:'closed'})]) {
    const f=fakePorts({getIssue});
    assert.ok((await routeRuntimeIssues({...options,apply:true},f.ports))[0].error);
    assert.deepEqual(f.writes,[]);
  }
});
test('retry after partial failure uses fresh metadata and avoids repeating successful effects', async () => {
  let current=structuredClone(issue), comments=[], fail=true;
  const f=fakePorts({getIssue:async()=>current,listComments:async()=>comments});
  f.ports.addLabel=async()=>{f.writes.push('label');current.labels.push({name:'pdd:runtime'});};
  f.ports.addAssignee=async()=>{if(fail)throw Error('SECRET');f.writes.push('assign');current.assignees.push({login:'runtime-owner'});};
  f.ports.postComment=async(_r,_n,body)=>{f.writes.push('comment');comments.push({id:1,body});};
  assert.ok((await routeRuntimeIssues({...options,apply:true},f.ports))[0].error);
  fail=false;
  await routeRuntimeIssues({...options,apply:true},f.ports);
  assert.deepEqual(f.writes,['label','assign','comment']);
  assert.equal(f.calls.length,1);
});
test('issues are sorted, PRs excluded, uncertain left alone and errors isolated', async () => {
  const f=fakePorts({listIssues:async()=>[{...issue,number:9},{...issue,number:2}, {...issue,number:1,pull_request:{}}],classify:async evidence=>evidence.number===2?'invalid':JSON.stringify({ownership:'uncertain',reason:'Need evidence.'})});
  const rows=await routeRuntimeIssues({...options,apply:true},f.ports);
  assert.deepEqual(rows.map(x=>x.number),[2,9]);
  assert.ok(rows[0].error);
  assert.deepEqual(rows[1].actions,[]);
  assert.deepEqual(f.writes,[]);
});
test('configuration rejects malformed owner and repository before any issue reads', async () => {
  const ports={listIssues:()=>assert.fail('should not read')};
  for (const bad of [{...options,owner:'x;echo secret'},{...options,repo:'../repo'},{...options,owner:''}]) await assert.rejects(routeRuntimeIssues(bad,ports));
});

test('native CLI uses fake gh and headless process, persists cache and defaults to dry run', async t => {
  const dir=await mkdtemp(join(tmpdir(),'pdd-router-test-'));
  t.after(()=>rm(dir,{recursive:true,force:true}));
  const bin=join(dir,'bin');await mkdir(bin);
  const db=join(dir,'db.json'), log=join(dir,'calls.jsonl'), config=join(dir,'config.json'), cache=join(dir,'cache');
  await writeFile(db,JSON.stringify({...issue,comments:[]}));
  await writeFile(join(bin,'gh'),`#!/usr/bin/env node
import fs from 'node:fs';
const args=process.argv.slice(2), db=JSON.parse(fs.readFileSync(process.env.FAKE_ROUTER_DB)), endpoint=args[1];
fs.appendFileSync(process.env.FAKE_ROUTER_LOG,JSON.stringify(args)+'\\n');
if(args.includes('POST')) {
 const data=JSON.parse(fs.readFileSync(0,'utf8'));
 if(endpoint.endsWith('/labels'))db.labels.push(...data.labels.map(name=>({name})));
 else if(endpoint.endsWith('/assignees'))db.assignees.push(...data.assignees.map(login=>({login})));
 else if(endpoint.endsWith('/comments'))db.comments.push({id:1,body:data.body});
 else process.exit(9);
 fs.writeFileSync(process.env.FAKE_ROUTER_DB,JSON.stringify(db)); console.log('{}');
} else console.log(JSON.stringify(args.includes('--paginate') ? [endpoint.includes('/comments')?db.comments:[db]] : db));
`,{mode:0o755});
  const agent=join(dir,'agent.mjs');
  await writeFile(agent,`import fs from 'node:fs';
if(process.env.GH_TOKEN||process.env.GITHUB_TOKEN||fs.readdirSync('.').length)process.exit(8);
const input=fs.readFileSync(0,'utf8');
if(!input.includes('untrusted')||!input.includes('interface blocks')||!input.includes('after the call'))process.exit(9);
fs.appendFileSync(process.env.FAKE_ROUTER_LOG,'AGENT\\n');
console.log(${JSON.stringify(JSON.stringify(runtime))});
`);
  await writeFile(config,JSON.stringify({owner:options.owner,agentCommand:[process.execPath,agent]}));
  const env={...process.env,PATH:`${bin}:${process.env.PATH}`,FAKE_ROUTER_DB:db,FAKE_ROUTER_LOG:log,GH_TOKEN:'fake-value',GITHUB_TOKEN:'fake-value'};
  const command=resolve('scripts/route-runtime-issues.mjs');
  const args=[command,'--repo',options.repo,'--config',config,'--cache-dir',cache];
  let result=await exec(process.execPath,args,{cwd:dir,env});
  assert.equal(JSON.parse(result.stdout)[0].actions.length,3);
  assert.equal(JSON.parse(await readFile(db)).labels.length,0);
  result=await exec(process.execPath,[...args,'--apply'],{cwd:dir,env});
  const saved=JSON.parse(await readFile(db));
  assert.deepEqual(saved.labels,[{name:'pdd:runtime'}]);
  assert.deepEqual(saved.assignees,[{login:options.owner}]);
  assert.equal(saved.comments.length,1);
  await exec(process.execPath,[...args,'--apply'],{cwd:dir,env});
  const calls=(await readFile(log,'utf8')).trim().split('\n');
  assert.equal(calls.filter(x=>x==='AGENT').length,1);
  const posts=calls.filter(x=>x!=='AGENT').map(JSON.parse).filter(x=>x.includes('POST'));
  assert.equal(posts.length,3);
  assert.ok(posts.every(x=>/\/(labels|assignees|comments)$/.test(x[1])));
  assert.ok(!(await readdir(cache)).includes('.lock'));
  await mkdir(join(cache,'.lock'));
  await assert.rejects(exec(process.execPath,args,{cwd:dir,env}), error=>error.code===1 && /locked/i.test(error.stderr) && !error.stderr.includes('fake-value'));
});
test('CLI help and invalid options never invoke a process', async () => {
  const command=resolve('scripts/route-runtime-issues.mjs');
  assert.match((await exec(process.execPath,[command,'--help'],{env:{PATH:''}})).stdout,/--apply/);
  for (const args of [['--apply','--unknown'],['--repo'],['--apply','--apply']]) await assert.rejects(exec(process.execPath,[command,...args],{env:{PATH:''}}),error=>error.code===1);
});

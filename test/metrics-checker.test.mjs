import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,writeFileSync,mkdirSync,rmSync} from 'node:fs';
import {execFileSync,spawnSync} from 'node:child_process';
import {tmpdir} from 'node:os';
import {join,resolve} from 'node:path';

function checkerFixture(t) {
  const root=mkdtempSync(join(tmpdir(),'checker-cli-')); t.after(()=>rmSync(root,{recursive:true,force:true}));
  const git=(...a)=>execFileSync('git',['-C',root,...a],{encoding:'utf8'}).trim();
  git('init','-q'); git('config','user.name','Fixture'); git('config','user.email','fixture@example.test'); git('remote','add','origin','https://github.com/owner/repo.git'); git('commit','--allow-empty','-qm','base'); const head=git('rev-parse','HEAD');
  const at='2026-11-01T00:00:00.000Z', base={schema:'pdd.metrics.event.v1',repo:'owner/repo',issue:1,at,observedAt:at,source:'fixture'};
  writeFileSync(join(root,'seed.json'),JSON.stringify([{...base,id:'selection',type:'selection',data:{snapshotId:'s',inScope:true,state:'ready',reasons:[]}},{...base,id:'mapping',type:'milestone',data:{stage:'implementation-ready',pr:9,head}}]));
  const bin=join(root,'bin'); mkdirSync(bin); writeFileSync(join(bin,'gh'),`#!/usr/bin/env node\nconst f=require(process.env.FIXTURE); const s=process.argv.join(' '); if(s.includes('check-runs'))console.log(JSON.stringify({check_runs:[]})); else if(s.includes('/files?'))console.log(f.files); else if(s.includes('/pulls/9'))console.log(JSON.stringify({head:{sha:f.head}})); else if(s.includes('/comments?'))console.log(f.comments.map(x=>JSON.stringify(x)).join('\\n')); else console.log(JSON.stringify({number:1}));\n`,{mode:0o755});
  const env={...process.env,PATH:bin+':'+process.env.PATH,FIXTURE:join(root,'fixture.json')}, cli=resolve('bin/pdd.mjs');
  const invoke=(...args)=>spawnSync(process.execPath,[cli,'metrics',...args],{cwd:root,env,encoding:'utf8'});
  let result;
  const check=(o={})=>({verdict:'PASS',head,risk:2,family:'codex',session:'fresh-1',checker_mode:'same-family',evidence:['independent checker evidence'],...o});
  const run=(checks,expected,files='src/example.mjs')=>{rmSync(join(root,'.git','pdd','metrics'),{recursive:true,force:true}); result=invoke('record','seed.json'); assert.equal(result.status,0,result.stderr); writeFileSync(env.FIXTURE,JSON.stringify({head,files,comments:checks.map((c,i)=>({id:i+1,author_association:'OWNER',user:{login:'owner'},body:'```json\n'+JSON.stringify(c)+'\n```',html_url:`https://github.com/owner/repo/pull/9#issuecomment-${i+1}`,created_at:`2026-11-02T00:00:0${i}.000Z`}))})); result=invoke('--snapshot','s','--json'); assert.equal(result.status,0,result.stderr); const issue=JSON.parse(result.stdout).issues[0]; assert.equal(issue.validated,expected); return issue;};
  return {run,check};
}

test('public metrics command requires supported independent checker evidence', t => {
  const {run,check}=checkerFixture(t);
  run([check()], 'yes');
  for(const evidence of [[],{},true,'x','nonsense']) run([check({evidence})], 'unknown');
  run([check({checker_mode:'anything'})], 'unknown');
  run([check({risk:4}),check({risk:4,family:'claude'})], 'unknown');
  run([check({risk:4,checker_mode:'different-family'}),check({risk:4,session:'fresh-2',checker_mode:'different-family'})], 'unknown');
  run([check({risk:5,session:'/root/check_one'}),check({risk:5,session:'/root/check_two',evidence:{native:'Independent native test passed'}})], 'yes');
  run([check({risk:4,checker_mode:'different-family'}),check({risk:4,family:'claude',session:'fresh-2',checker_mode:'different-family'})], 'yes');
  run([check()], 'unknown','src/approval.mjs');
  run([check(),check({session:'fresh-2',verdict:'FAIL'})], 'unknown');
});

test('split checker verdicts remain unknown without a second agreeing fresh checker', t => {
  const {run,check}=checkerFixture(t);
  run([check(),check({session:'fresh-2',verdict:'FAIL'})], 'unknown');
  run([check({risk:4,verdict:'FAIL'})], 'unknown');
});

test('slash-containing checker sessions retain distinct reversible identities', t => {
  const {run,check}=checkerFixture(t);
  const issue=run([check({risk:5,session:'/root/check_one'}),check({risk:5,session:'/root/check_two'})], 'yes');
  const identities=issue.checks.map(e=>e.data.reviewer);
  assert.equal(new Set(identities).size,2);
  assert.deepEqual(identities.map(x=>Buffer.from(x.split(':session-')[1],'base64url').toString()).sort(),['/root/check_one','/root/check_two']);
});

test('native split resolution requires two fresh sessions with compatible modes', t => {
  const {run,check}=checkerFixture(t);
  const before=[check(),check({session:'prior-2'}),check({verdict:'FAIL',session:'opponent',family:'claude'})];
  run([...before,check({session:'fresh-3'})], 'unknown');
  run([...before,check({session:'fresh-3',checker_mode:'different-family'}),check({session:'fresh-4',checker_mode:'different-family'})], 'unknown');
  const passed=run([...before,check({session:'fresh-3'}),check({session:'fresh-4'})], 'yes');
  assert.ok(passed.checks.some(e=>e.data.verdict==='FAIL'));
  assert.ok(passed.checks.some(e=>e.data.verdict==='PASS'));
  const failed=run([...before,check({session:'fresh-3',verdict:'FAIL'}),check({session:'fresh-4',verdict:'FAIL'})], 'no');
  assert.ok(failed.checks.some(e=>e.data.verdict==='FAIL'));
  assert.ok(failed.checks.some(e=>e.data.verdict==='PASS'));
  run([...before,check({session:'fresh-3',head:'stale'}),check({session:'fresh-4',head:'stale'})], 'unknown');
});

test('checker family identity ignores case when requiring independent agreement', t => {
  const {run,check}=checkerFixture(t);
  const first=check({risk:4,checker_mode:'different-family'});
  run([first,check({risk:4,family:'CODEX',session:'fresh-2',checker_mode:'different-family'})], 'unknown');
  run([first,check({risk:4,family:'claude',session:'fresh-2',checker_mode:'different-family'})], 'yes');
});

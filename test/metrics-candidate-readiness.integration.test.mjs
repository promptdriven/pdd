import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync, realpathSync, chmodSync, cpSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { execFileSync } from 'node:child_process';
import {pinReplayVectors} from '../src/workflow-replay.mjs';

const packageRoot = resolve(import.meta.dirname, '..');
const url = number => `https://github.com/example/project/pull/${number}`;
const phase = (exitCode, expectedFound = false) => ({ exitCode, signal: '', timedOut: false, outputLimited: false, stdoutTail: [], stderrTail: [], expectedFound, error: '', setupError: '', observedError: 'code: defect' });
function fixture(t, { existing = false, opted = false, prompt = false } = {}) {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-publication-')));
  t.after(() => rmSync(base, { recursive: true, force: true }));
  const root = join(base, 'project'), bare = join(base, 'remote.git'), bin = join(base, 'bin'), state = join(base, 'gh.json');
  mkdirSync(root); mkdirSync(bin);
  const gitBinary = execFileSync('which', ['git'], { encoding: 'utf8' }).trim();
  const route = `url.file://${bare}.insteadOf=https://github.com/example/project.git`;
  const git = (...args) => execFileSync(gitBinary, ['-c', route, ...args], { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }).trim();
  git('init', '--bare', '-q', bare); git('init', '-qb', 'main'); git('config', 'user.name', 'Publication Test'); git('config', 'user.email', 'test@example.invalid');
  // Every network-shaped origin operation goes through real Git to the local bare repository.
  writeFileSync(join(bin, 'git'), `#!/usr/bin/env node\nconst cp=require('node:child_process'),a=process.argv.slice(2);const r=cp.spawnSync(${JSON.stringify(gitBinary)},a[0]==='remote'&&a[1]==='get-url'?a:['-c',${JSON.stringify(route)},...a],{stdio:'inherit'});process.exit(r.status??1);\n`); chmodSync(join(bin, 'git'), 0o755);
  git('remote', 'add', 'origin', 'https://github.com/example/project.git');
  writeFileSync(join(root, 'value'), 'base'); git('add', '.'); git('commit', '-qm', 'base'); git('push', '-q', 'origin', 'main');
  const baseSha = git('rev-parse', 'HEAD'); git('switch', '-qc', 'topic');
  writeFileSync(join(root, 'value'), 'head'); git('commit', '-qam', 'head');
  const head = git('rev-parse', 'HEAD'); if (existing) git('push', '-q', 'origin', 'HEAD:refs/heads/topic');
  const runDir = join(root, '.git', 'pdd', 'runs', '17'); mkdirSync(runDir, { recursive: true });
  const areas = [{ name: 'prompt-pr', steps: ['scope','check'], optional: [], gate: 'pr', then: 'ask-code' }, { name: 'code', steps: ['build', 'verify', 'formal','review'], optional: [], gate: 'pr', ...(opted ? { replay_evidence: 'pdd.replay-evidence.v1' } : {}) }];
  const prs = prompt ? [] : [{ stage: 'prompt-pr', number: 22, url: url(22), branch: 'prompt-topic', base: 'main' }];
  if (existing) prs.push({ stage: prompt ? 'prompt-pr' : 'code', number: 23, url: url(23), branch: 'topic', base: 'main' });
  const run = { v: 1, runId: 'publication-17', number: 17, repo: 'example/project', issue: { title: 'Repair value', number: 17, url: 'https://github.com/example/project/issues/17' }, root, sourceRoot: root, commonDir: join(root, '.git'), runDir, branch: 'topic', baseBranch: 'main', baseSha, workflow: 'small-change', agent: 'codex', areas, area: prompt ? 0 : 1, state: 'running', done: {formal:{summary:'formal',at:4}, scope: { summary: 'Defect: broken value', at: 1 }, build: { summary: 'built', at: 2 }, verify: { summary: 'verified', at: 3 } }, decisions: [], changes: [], chats: [], pr: prs, replayBaseline: { schema_version: 'pdd.replay-vectors.v1', vectors: [] } };
  const row = { number: 23, url: url(23), state: 'OPEN', headRefName: 'topic', baseRefName: 'main', headRefOid: head, body: `Old-code proof: ✓ old success\n<!-- pdd-workflow:${run.runId}:${prompt ? 'prompt-pr' : 'code'} -->\n`, headRepository: { name: 'project' }, headRepositoryOwner: { login: 'example' }, isCrossRepository: false, mergeCommit: null };
  writeFileSync(state, JSON.stringify({ prs: existing ? [row] : [], events: [], failEdit: 0 }));
  const fake = `#!/usr/bin/env node
const fs=require('node:fs'),cp=require('node:child_process');
const file=process.env.PDD_PUBLICATION_GH_STATE,s=JSON.parse(fs.readFileSync(file,'utf8')),a=process.argv.slice(2);
const flag=n=>a[a.indexOf(n)+1],out=x=>process.stdout.write(typeof x==='string'?x:JSON.stringify(x));
const commit=()=>cp.execFileSync('git',['rev-parse','HEAD'],{encoding:'utf8'}).trim();
const remote=()=>{try{return cp.execFileSync('git',['ls-remote','origin','refs/heads/topic'],{encoding:'utf8'}).trim().split('\\t')[0]}catch{return ''}};
if(a[0]==='repo')out({nameWithOwner:'example/project',defaultBranchRef:{name:'main'},url:'https://github.com/example/project'});
else if(a[1]==='list')out(s.prs.filter(p=>!a.includes('--head')||p.headRefName===flag('--head')).map(p=>({...p,headRefOid:remote()||p.headRefOid})));
else if(a[1]==='view')out(s.prs.find(p=>p.url===a[2])||{body:''});
else if(a[1]==='create'||a[1]==='edit'){
 if(flag('--body-file')!=='-')throw Error('must read body from stdin');
 const body=fs.readFileSync(0,'utf8'),kind=a[1];s.events.push({kind,body,remote:remote(),head:commit()});
 if(kind==='edit'&&s.failEdit===s.events.filter(e=>e.kind==='edit').length){fs.writeFileSync(file,JSON.stringify(s));process.stderr.write('error: refused edit');process.exit(1)}
 if(kind==='create'){s.prs.push({number:23,url:'https://github.com/example/project/pull/23',state:'OPEN',headRefName:flag('--head'),baseRefName:flag('--base'),headRefOid:commit(),body,title:flag('--title'),headRepository:{name:'project'},headRepositoryOwner:{login:'example'},isCrossRepository:false,mergeCommit:null});out(s.prs.at(-1).url)}
 else{s.prs.find(p=>p.url===a[2]).body=body;out('updated')}
 fs.writeFileSync(file,JSON.stringify(s));
}else throw Error('unexpected gh '+a.join(' '));
`;
  writeFileSync(join(bin, 'gh'), fake); chmodSync(join(bin, 'gh'), 0o755);
  const save = () => writeFileSync(join(runDir, 'status.json'), JSON.stringify(run)); save();
  const invoke = (summary, method = 'stepDone', failMetrics = false) => {
    const review=String(summary).split('\n').filter(row=>row.startsWith('Review:')).join('\n');if(review)writeFileSync(join(runDir,'review.md'),review);
    const verify=String(summary).split('\n').filter(row=>/^(?:Not fixed yet:|Proof \()/.test(row)).join('\n');if(verify)writeFileSync(join(runDir,'verify.md'),verify);
    const scope=String(summary).split('\n').filter(row=>row.startsWith('Not caught because:')).join('\n');if(scope)writeFileSync(join(runDir,'scope.md'),scope);

    const script = `import * as requireFs from 'node:fs';import {${method}} from ${JSON.stringify(join(packageRoot, 'src/workflow-runner.mjs'))};const r=await ${method}({ref:'17',step:${JSON.stringify(prompt ? 'check' : 'review')},summary:${JSON.stringify(summary)},cwd:${JSON.stringify(root)}},{stateDir:${JSON.stringify(join(base, 'pdd-state'))},isTTY:true,env:{HOME:${JSON.stringify(base)}},confirm:async()=>false,...(${failMetrics} ? {runFiles:{linkSync:(a,b)=>{const fs=requireFs;const saved=JSON.parse(fs.readFileSync(${JSON.stringify(join(runDir,'status.json'))},'utf8'));if(saved.pr.some(pr=>pr.stage==='code' && pr.publishedHeadSha))throw Error('injected post-publication metrics save failure');return fs.linkSync(a,b);}},metricsWarning:()=>{}} : {})});await new Promise(resolve=>setTimeout(resolve,50));process.stdout.write(JSON.stringify(r));`;
    return JSON.parse(execFileSync(process.execPath, ['--input-type=module', '-e', script], { cwd: root, encoding: 'utf8', env: { ...process.env, PATH: `${bin}:${process.env.PATH}`, PDD_PUBLICATION_GH_STATE: state, GIT_ALLOW_PROTOCOL: 'file' } }));
  };
  const machine = () => writeFileSync(join(runDir, 'old-code-proof.json'), JSON.stringify({ v: 2, origin: 'pdd.workflow-prove.v2',interruptSignal:'', runId: run.runId, baseSha, headSha: head, test: 'node --test test/value.test.mjs', expect: 'defect', paths: ['test/value.test.mjs'], base: phase(1, true), head: phase(0), outcome: 'proved', cleanupError: '', setupError: '' }));
  const change = () => { writeFileSync(join(root, 'value'), `new head ${Date.now()} ${Math.random()}`); git('commit', '-qam', 'new source'); return git('rev-parse', 'HEAD'); };
  const data = () => JSON.parse(readFileSync(state, 'utf8'));
  return { base, root, bare, git, run, head, runDir, save, invoke, machine, change, data, configure: values => writeFileSync(state, JSON.stringify({ ...data(), ...values })) };
}

const readiness = f => JSON.parse(readFileSync(join(f.runDir, 'status.json'), 'utf8')).metrics?.events?.filter(e => e.type === 'milestone' && e.data.stage === 'implementation-ready') ?? [];

test('final code area captures exact published candidate when all steps complete', t => {
  const f = fixture(t); f.run.workflow='feature'; f.save();
  const result=f.invoke('Review: ready'); assert.equal(result.exitCode,0,result.message);
  assert.deepEqual(readiness(f).map(e=>[e.data.pr,e.data.head]),[[23,f.head]]);
});

test('prompt PR alone does not capture implementation readiness', t => {
  const f=fixture(t,{prompt:true}); f.run.workflow='feature'; f.save();
  const result=f.invoke('Review: ready'); assert.equal(result.exitCode,0,result.message);
  assert.deepEqual(readiness(f),[]);
});

test('custom prompt-only final PR cannot become code-ready from outcome metadata', t => {
  const f=fixture(t,{prompt:true}); f.run.workflow='custom'; f.run.areas=[{name:'prompt-pr',steps:['scope','check'],optional:[],gate:'pr'}]; f.run.area=0; f.run.metricsOrigin={origin:'manual',requiredOutcome:'code'}; f.save();
  const result=f.invoke('Review: ready'); assert.equal(result.exitCode,0,result.message);
  assert.deepEqual(readiness(f),[]);
});

test('single-area small-change captures readiness for its published candidate', t => {
  const f=fixture(t); f.run.areas=[{name:'change',steps:['review'],optional:[],gate:'pr'}]; f.run.area=0; f.run.pr=[]; f.save();
  const result=f.invoke('Review: ready'); assert.equal(result.exitCode,0,result.message);
  assert.deepEqual(readiness(f).map(e=>[e.data.pr,e.data.head]),[[23,f.head]]);
});

test('custom final implementation area captures readiness when it completes', t => {
  const f=fixture(t); f.run.workflow='custom'; f.run.areas[1].name='implementation'; f.save();
  const result=f.invoke('Review: ready'); assert.equal(result.exitCode,0,result.message);
  assert.deepEqual(readiness(f).map(e=>[e.data.pr,e.data.head]),[[23,f.head]]);
});

test('republishing from an earlier completed step does not assert readiness for a new head', t => {
  const f=fixture(t,{existing:true}); f.run.workflow='feature'; f.save(); f.change();
  const result=f.invoke('Review: ready'); assert.equal(result.exitCode,0,result.message);
  const first=readiness(f); assert.equal(first.length,1);
  f.change(); const script=JSON.stringify(f.root);
  const result2=execFileSync(process.execPath,['--input-type=module','-e',`import {stepDone} from ${JSON.stringify(join(packageRoot,'src/workflow-runner.mjs'))}; const r=await stepDone({step:'formal',summary:'again',cwd:${script}},{stateDir:${JSON.stringify(join(f.base,'pdd-state'))},isTTY:true,env:{HOME:${JSON.stringify(f.base)}},confirm:async()=>false}); process.stdout.write(JSON.stringify(r));`],{cwd:f.root,encoding:'utf8',env:{...process.env,PATH:`${join(f.base,'bin')}:${process.env.PATH}`,PDD_PUBLICATION_GH_STATE:join(f.base,'gh.json'),GIT_ALLOW_PROTOCOL:'file'}});
  assert.equal(JSON.parse(result2).exitCode,0); assert.deepEqual(readiness(f),first);
});

test('completed-run review refresh cannot establish readiness for a later head', t => {
  const f=fixture(t,{existing:true}); f.run.state='completed'; f.run.workflow='feature'; f.save(); f.change();
  f.invoke('Review: ready');
  assert.deepEqual(readiness(f),[]);
});

test('post-publication metrics save failure preserves the native response and retries the fact once', async t => {
  const f=fixture(t); f.run.workflow='feature'; f.save();
  const result=f.invoke('Review: ready','stepDone',true);
  assert.equal(result.exitCode,0,result.message);
  assert.match(result.message,/PR.*open|PR.*pull\/23/i);
  const saved=JSON.parse(readFileSync(join(f.runDir,'status.json'),'utf8'));
  assert.equal(saved.state,'waiting');
  assert.equal(saved.metrics.coverageGap,true);
  assert.equal(saved.metricsObservations.filter(e=>e.data?.stage==='implementation-ready').length,1);
  const {updateRun}=await import('../src/workflow-runs.mjs');
  const retried=updateRun(f.runDir, current=>current, {stateDir:join(f.base,'pdd-state'),skipMetricsDelivery:true});
  assert.equal(readiness(f).length,1);
  const {drainRunJournal}=await import('../src/metrics-hooks.mjs');
  const {appendEvents,readEvents}=await import('../src/metrics-store.mjs');
  await drainRunJournal({run:retried,root:f.root,store:{appendEvents}});
  await drainRunJournal({run:retried,root:f.root,store:{appendEvents}});
  const exported=await readEvents({root:f.root});
  assert.equal(exported.events.filter(e=>e.type==='milestone' && e.data.stage==='implementation-ready').length,1);
});

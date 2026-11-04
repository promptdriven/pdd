import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync, realpathSync, chmodSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const packageRoot = fileURLToPath(new URL('..', import.meta.url));
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
  const run = { v: 1, runId: 'publication-17', number: 17, repo: 'example/project', issue: { title: 'Repair value', number: 17, url: 'https://github.com/example/project/issues/17' }, root, sourceRoot: root, runDir, branch: 'topic', baseBranch: 'main', baseSha, workflow: 'small-change', agent: 'codex', areas, area: prompt ? 0 : 1, state: 'running', done: {review:{summary:'reviewed',at:4}, scope: { summary: 'Defect: broken value', at: 1 }, build: { summary: 'built', at: 2 }, verify: { summary: 'verified', at: 3 } }, decisions: [], changes: [], chats: [], pr: prs, replayBaseline: { schema_version: 'pdd.replay-vectors.v1', vectors: [] } };
  const row = { number: 23, url: url(23), state: 'OPEN', headRefName: 'topic', baseRefName: 'main', headRefOid: head, body: `Old-code proof: ✓ old success\n<!-- pdd-workflow:${run.runId}:${prompt ? 'prompt-pr' : 'code'} -->\n`, headRepository: { name: 'project' }, headRepositoryOwner: { login: 'example' }, isCrossRepository: false, mergeCommit: null };
  writeFileSync(state, JSON.stringify({ prs: existing ? [row] : [], events: [], failEdit: 0 }));
  const fake = `#!/usr/bin/env node
const fs=require('node:fs'),cp=require('node:child_process');
const file=process.env.PDD_PUBLICATION_GH_STATE,s=JSON.parse(fs.readFileSync(file,'utf8')),a=process.argv.slice(2);
const flag=n=>a[a.indexOf(n)+1],out=x=>process.stdout.write(typeof x==='string'?x:JSON.stringify(x));
const commit=()=>cp.execFileSync('git',['rev-parse','HEAD'],{encoding:'utf8'}).trim();
const remote=()=>{try{return cp.execFileSync('git',['ls-remote','origin','refs/heads/topic'],{encoding:'utf8'}).trim().split('\\t')[0]}catch{return ''}};
if(a[0]==='repo')out({nameWithOwner:'example/project',defaultBranchRef:{name:'main'},url:'https://github.com/example/project'});
else if(a[1]==='list')out(s.prs.filter(p=>!a.includes('--head')||p.headRefName===flag('--head')));
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
  const invoke = (summary, method = 'stepDone') => {
    const review=String(summary).split('\n').filter(row=>row.startsWith('Review:')).join('\n');if(review)writeFileSync(join(runDir,'review.md'),review);
    const verify=String(summary).split('\n').filter(row=>/^(?:Not fixed yet:|Proof \()/.test(row)).join('\n');if(verify)writeFileSync(join(runDir,'verify.md'),verify);
    const scope=String(summary).split('\n').filter(row=>row.startsWith('Not caught because:')).join('\n');if(scope)writeFileSync(join(runDir,'scope.md'),scope);

    const script = `import {${method}} from ${JSON.stringify(join(packageRoot, 'src/workflow-runner.mjs'))};const r=await ${method}({ref:'17',step:${JSON.stringify(prompt ? 'check' : 'formal')},summary:${JSON.stringify(summary)},cwd:${JSON.stringify(root)}},{stateDir:${JSON.stringify(join(base, 'pdd-state'))},isTTY:true,env:{HOME:${JSON.stringify(base)}},confirm:async()=>false});process.stdout.write(JSON.stringify(r));`;
    return JSON.parse(execFileSync(process.execPath, ['--input-type=module', '-e', script], { cwd: root, encoding: 'utf8', env: { ...process.env, PATH: `${bin}:${process.env.PATH}`, PDD_PUBLICATION_GH_STATE: state, GIT_ALLOW_PROTOCOL: 'file' } }));
  };
  const machine = () => writeFileSync(join(runDir, 'old-code-proof.json'), JSON.stringify({ v: 2, origin: 'pdd.workflow-prove.v2',interruptSignal:'', runId: run.runId, baseSha, headSha: head, test: 'node --test test/value.test.mjs', expect: 'defect', paths: ['test/value.test.mjs'], base: phase(1, true), head: phase(0), outcome: 'proved', cleanupError: '', setupError: '' }));
  const change = () => { writeFileSync(join(root, 'value'), 'new head'); git('commit', '-qam', 'new source'); return git('rev-parse', 'HEAD'); };
  const data = () => JSON.parse(readFileSync(state, 'utf8'));
  return { base, root, bare, git, run, head, runDir, save, invoke, machine, change, data, configure: values => writeFileSync(state, JSON.stringify({ ...data(), ...values })) };
}
import { sourceFingerprint } from '../src/workflow-replay.mjs';
import { storyCount } from '../src/workflow-runner.mjs';
import { renderJson, renderText } from '../src/runtime-output.mjs';

// Expectations below are bounded instances of the approved Story's Rules to check.
// Fixture mechanics supply Git/GitHub facts only; they do not supply the oracle.
const sourceModes = ['same', 'changed', 'deleted', 'unavailable', 'unbound'];
const verdicts = ['passed', 'failed', 'unknown'];
const token = state => state === 'passed' ? '✓' : state === 'failed' ? '✗' : 'no verdict';
const receipt = (story, state) => `Prompt tests (${story}): ${token(state)} 1 of 1 criteria · 1/1 checks · 1 AI call`;
test('formal freshness: all 450 source-binding and latest-result combinations', () => {
  let cases = 0;
  for (const kind of ['git-content-v1', 'runtime-capture-v1'])
    for (const older of sourceModes) for (const newer of sourceModes)
      for (const oldState of verdicts) for (const newState of verdicts) {
        const source = mode => mode === 'unbound' ? undefined : {kind, sha256: mode === 'same' ? 'current' : mode, tests: [`${mode}.json`]};
        const run = {root:'/synthetic/formal', runtimeHistory:[
          {at:1, summary:receipt('one',oldState)+'\nPrompt tests: ✓ 999 of 999 criteria', source:source(older)},
          {at:2, summary:receipt('two','passed'), source:source('same')},
          {at:3, summary:receipt('one',newState), source:source(newer)}]};
        const ports = {
          fingerprint: () => 'current',
          capture: (_root, {tests}) => {
            const mode = tests[0].replace('.json','');
            if (['deleted','unavailable'].includes(mode)) throw new Error('selected content cannot be verified');
            return {sha256:'current'};
          }
        };
        // For whole-content identity, deleted/unavailable are observations of a
        // differing whole-tree fingerprint; selected capture additionally tests throws.
        const expectedState = newer === 'same' ? newState : older === 'same' ? oldState : null;
        const actual = storyCount(run, ports), context=JSON.stringify({kind,older,newer,oldState,newState});
        assert.equal(actual.total,2,context);
        assert.equal(actual.pass,1 + Number(expectedState === 'passed'),context);
        assert.deepEqual(actual.failing,expectedState === 'failed' ? ['one'] : [],context);
        assert.deepEqual(actual.unknown ?? [],expectedState === null || expectedState === 'unknown' ? ['one'] : [],context);
        cases++;
      }
  assert.equal(cases,450);
});

test('formal freshness: unavailable whole-tree identity cannot validate saved success',()=>{
  for(const fingerprint of [null,'changed']) for(const binding of [undefined,{kind:'git-content-v1',sha256:'saved'}]) {
    const result=storyCount({root:'/synthetic/formal',runtimeHistory:[{at:1,summary:receipt('one','passed'),source:binding}]},{fingerprint:()=>fingerprint});
    assert.equal(result.pass,0);
    assert.deepEqual(result.unknown,['one']);
  }
});

test('formal freshness semantic control: current and stale Stories retain separate status', t=>{
  const root=mkdtempSync(join(tmpdir(),'pdd-formal-freshness-'));
  t.after(()=>rmSync(root,{recursive:true,force:true}));
  const git=(...args)=>execFileSync('git',args,{cwd:root,encoding:'utf8',stdio:['ignore','pipe','pipe']}).trim();
  git('init','-qb','main'); git('config','user.name','Formal'); git('config','user.email','formal@example.invalid');
  writeFileSync(join(root,'value'),'current');git('add','.');git('commit','-qm','source');
  const current={kind:'git-content-v1',sha256:sourceFingerprint(root)};
  for(const state of verdicts) {
    const run={root,runtimeHistory:[
      {at:1,summary:receipt('stale','passed'),source:{kind:'git-content-v1',sha256:'old'}},
      {at:2,summary:receipt('current',state),source:current}]};
    const result=storyCount(run);
    assert.equal(result.total,2,'stale Story must stay visible as unknown beside compatible current evidence');
    assert.equal(result.pass,Number(state==='passed'));
    assert.deepEqual(result.unknown,state==='unknown'?['stale','current']:['stale']);
    assert.deepEqual(result.failing,state==='failed'?['current']:[]);
  }
});

const atoms = [null,
  {criterion_id:'AC1',target:'result',path:'/exit_code'},
  {criterion_id:'AC1',target:'result',path:'/exitCode'},
  {criterion_id:'AC1',target:'result',path:'/stdout'},
  {criterion_id:'AC1',target:'world',path:'/exit_code'},
  {criterion_id:'AC2',target:'result',path:'/exit_code'}];
test('formal coverage: all 5184 four-slot assignments, words and result states', () => {
  let cases=0;
  for (let index=0;index<6**4;index++) for (const text of ['Prints the saved report.','Exits successfully.']) for (const state of ['passed','failed']) {
    let value=index;
    const slots=Array.from({length:4},()=>{const atom=atoms[value%6];value=Math.floor(value/6);return atom;});
    const checks=slots.filter(Boolean), steps=[0,2].map(offset=>({step_id:`step-${offset}`,checks:slots.slice(offset,offset+2).filter(Boolean)}));
    const row={story:'formal',title:'Formal',test:'formal.json',state,phase:'server',calls:0,seconds:0,criterion_texts:{AC1:text,AC2:'Prints another report.',AC3:'No assigned checks.'},steps};
    const expected=['AC1','AC2','AC3'].map(id=>{
      const assigned=checks.filter(check=>check.criterion_id===id);
      // The Story's conjunction: nonempty AND no assigned non-exit result.
      const nonExit=assigned.filter(check=>check.target!=='result' || (check.path!=='/exit_code' && check.path!=='/exitCode'));
      return {criterion_id:id,check_count:assigned.length,exit_code_only:assigned.length!==0 && nonExit.length===0};
    });
    const output=renderJson({repo:'synthetic/formal',rows:[row],exitCode:state==='passed'?0:1});
    const context=JSON.stringify({index,text,state});
    assert.deepEqual(output.rows[0].criterion_coverage,expected,context);
    assert.equal(output.rows[0].state,state,context);
    assert.deepEqual(output.warnings,[],context);
    const printed=renderText({rows:[row],exitCode:state==='passed'?0:1});
    for(const fact of expected) {
      const line=printed.split('\n').find(line=>line.includes(`criterion ${fact.criterion_id}:`));
      assert.ok(line,context);
      assert.equal(line.includes('checked by exit code only'),fact.exit_code_only,context);
    }
    cases++;
  }
  assert.equal(cases,5184);
});
test('formal coverage: unavailable authored steps stay unknown for both verdicts',()=>{
  for(const state of ['passed','failed']) {
    const row={story:'formal',title:'Formal',test:'formal.json',state,phase:'server',calls:0,criterion_texts:{AC1:'Prints a report.'}};
    assert.equal(renderJson({rows:[row],exitCode:0}).rows[0].criterion_coverage,null);
    assert.doesNotMatch(renderText({rows:[row],exitCode:0}),/checked by exit code only/);
  }
});

for(const proofState of ['current','stale','missing']) for(const total of [0,2]) for(const claim of ['665/665 passed','0/665 passed; 665 failed'])
  test(`formal native counts: ${proofState}, ${total} actual tests, agent ${claim}`, t=>{
    const f=fixture(t);
    if(proofState!=='missing') {
      f.machine();
      const path=join(f.runDir,'old-code-proof.json'),record=JSON.parse(readFileSync(path,'utf8'));
      record.head.stdoutTail=[`# tests ${total}`,`# pass ${total}`,'# fail 0'];
      if(proofState==='stale')record.headSha='a'.repeat(40);
      writeFileSync(path,JSON.stringify(record));
    }
    const out=f.invoke(`Proof (defect fixed): Full npm test: ${claim}`);
    assert.equal(out.exitCode,0,JSON.stringify(out));
    const body=f.data().prs[0].body;
    const checked=body.split('\n').filter(line=>line.startsWith('Native tests'));
    assert.deepEqual(checked,[proofState==='current'
      ? `Native tests (current old-code proof, new-code output): ${total}/${total} passed; 0 failed.`
      : 'Native tests: unknown (no current machine counts).']);
    assert.ok(body.split('\n').some(line=>line.startsWith('Agent note — not checked by pdd:') && line.includes(claim)), 'agent claim retains its explicit trust label');
  });

// #2904: a proof saved before the run started is stale on the PR top too, and gives no native counts.
test('2904 native publication: a proof file older than the run start is stale and gives no Native tests counts', async t => {
  const { utimesSync } = await import('node:fs');
  const f = fixture(t); f.run.startedAt = Date.now(); f.save(); f.machine();
  const path = join(f.runDir, 'old-code-proof.json'), record = JSON.parse(readFileSync(path, 'utf8'));
  record.head.stdoutTail = ['# tests 1', '# pass 1', '# fail 0']; writeFileSync(path, JSON.stringify(record));
  const old = new Date(f.run.startedAt - 3600000); utimesSync(path, old, old);
  const out = f.invoke('Proof (defect fixed): checked');
  assert.equal(out.exitCode, 0, JSON.stringify(out));
  const body = f.data().prs[0].body.split('\n');
  assert.ok(body.includes('Old-code proof: stale (saved before this run started; rerun pdd workflow prove).'), body.slice(0, 6).join('\n'));
  assert.ok(body.includes('Native tests: unknown (no current machine counts).'));
  assert.ok(!body.some(line => line.startsWith('Old-code proof: ✓')));
});

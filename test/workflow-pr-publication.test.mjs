import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync, realpathSync, chmodSync, cpSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { execFileSync } from 'node:child_process';
import {pinReplayVectors,sourceFingerprint} from '../src/workflow-replay.mjs';
import { DETAILS_OPEN, detailsOf, prStatus } from '../src/workflow-pr-body.mjs';
import { proseSha256 } from '../src/runtime-seam.mjs';
import { promptHeaderHash } from '../src/file-owner.mjs';

// #3042: pdd's own body (evidence, steps, approvals, Verify) now sits in the closed Details section under the readable
// part. Checks that start at the first line of pdd's body read that section.
const pddPart = body => detailsOf(body)?.details ?? body;

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
  // A saved open PR 1 has a fetchable source branch for the code publication guard.
  if (!prompt) git('push', '-q', 'origin', 'main:refs/heads/prompt-topic');
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
const remote=(ref='topic')=>{try{return cp.execFileSync('git',['ls-remote','origin','refs/heads/'+ref],{encoding:'utf8'}).trim().split('\\t')[0]}catch{return ''}};
if(a[0]==='label'&&a[1]==='list')out((s.repoLabels||[]).map(name=>({name})));
else if(a[0]==='label'&&a[1]==='create'){s.labelCreates=[...(s.labelCreates||[]),a];if(s.failLabel){fs.writeFileSync(file,JSON.stringify(s));process.stderr.write('label refused');process.exit(1)} if(s.labelRace){s.repoLabels=[...new Set([...(s.repoLabels||[]),a[2]])];fs.writeFileSync(file,JSON.stringify(s));process.stderr.write(String(s.labelRace));process.exit(1)} s.repoLabels=[...(s.repoLabels||[]),a[2]];fs.writeFileSync(file,JSON.stringify(s));}
else if(a[0]==='pr'&&a[1]==='edit'&&(a.includes('--add-label')||a.includes('--remove-label'))){const pr=s.prs.find(p=>p.url===a[2]);pr.labels=pr.labels||[];if(a.includes('--add-label'))pr.labels.push(flag('--add-label'));else pr.labels=pr.labels.filter(x=>x!==flag('--remove-label'));fs.writeFileSync(file,JSON.stringify(s));}
else if(a[0]==='repo')out({nameWithOwner:'example/project',defaultBranchRef:{name:'main'},url:'https://github.com/example/project'});
else if(a[1]==='list')out(s.prs.filter(p=>(!a.includes('--head')||p.headRefName===flag('--head'))&&(!a.includes('--search')||p.body.includes(flag('--search').split('"')[1]))).map(p=>({...p,headRefOid:remote(p.headRefName)||p.headRefOid})));
else if(a[1]==='view'){const found=s.prs.find(p=>p.url===a[2]),p=found?.headRefName?{...found,labels:(found.labels||[]).map(name=>({name})),headRefOid:remote(found.headRefName)||found.headRefOid}:found||{body:'',labels:[]};out(String(flag('--json')).split(',').includes('comments')?{...p,comments:(s.comments||[]).map(c=>({author:{login:'reviewer'},authorAssociation:c.author_association,body:c.body,createdAt:c.created_at,url:c.html_url}))}:p)}
else if(a[0]==='api'&&/^repos\\/example\\/project\\/pulls\\/\\d+\\/files\\?per_page=100$/.test(a[1])){
 if(!a.includes('--paginate')||!a.includes('--slurp'))throw Error('file list must include every JSON page');
 const pages=s.prFiles?.[a[1].split('/')[4]];if(!pages)throw Error('file list unavailable');out(pages);
}
else if(a[0]==='api'&&a.some(x=>x.includes('/comments')))out((s.comments||[]).map(c=>JSON.stringify(c)).join('\\n'));
else if(a[1]==='create'||a[1]==='edit'){
 if(flag('--body-file')!=='-')throw Error('must read body from stdin');
 const body=fs.readFileSync(0,'utf8'),kind=a[1];s.events.push({kind,body,remote:remote(),head:commit()});
 if(kind==='edit'&&s.failEdit===s.events.filter(e=>e.kind==='edit').length){fs.writeFileSync(file,JSON.stringify(s));process.stderr.write('error: refused edit');process.exit(1)}
 if(kind==='create'){const number=Math.max(22,...s.prs.map(p=>p.number))+1;s.prs.push({number,url:'https://github.com/example/project/pull/'+number,state:'OPEN',headRefName:flag('--head'),baseRefName:flag('--base'),headRefOid:commit(),body,title:flag('--title'),headRepository:{name:'project'},headRepositoryOwner:{login:'example'},isCrossRepository:false,mergeCommit:null});out(s.prs.at(-1).url)}
 else{s.prs.find(p=>p.url===a[2]).body=body;out('updated')}
 fs.writeFileSync(file,JSON.stringify(s));
}else throw Error('unexpected gh '+a.join(' '));
`;
  writeFileSync(join(bin, 'gh'), fake); chmodSync(join(bin, 'gh'), 0o755);
  const save = () => writeFileSync(join(runDir, 'status.json'), JSON.stringify(run)); save();
  const invoke = (summary, method = 'stepDone', step = prompt ? 'check' : 'formal', results = null) => {
    const review=String(summary).split('\n').filter(row=>row.startsWith('Review:')).join('\n');if(review)writeFileSync(join(runDir,'review.md'),review);
    const verify=String(summary).split('\n').filter(row=>/^(?:Not fixed yet:|Proof \()/.test(row)).join('\n');if(verify)writeFileSync(join(runDir,'verify.md'),verify);
    const scope=String(summary).split('\n').filter(row=>row.startsWith('Not caught because:')).join('\n');if(scope)writeFileSync(join(runDir,'scope.md'),scope);

    const script = `import {${method}} from ${JSON.stringify(join(packageRoot, 'src/workflow-runner.mjs'))};const r=await ${method}({ref:'17',step:${JSON.stringify(step)},summary:${JSON.stringify(summary)},cwd:${JSON.stringify(root)}},{stateDir:${JSON.stringify(join(base, 'pdd-state'))},isTTY:true,env:{HOME:${JSON.stringify(base)}},confirm:async()=>false,...(${JSON.stringify(results)} ? {readRunResults:()=>${JSON.stringify(results)}} : {})});process.stdout.write(JSON.stringify(r));`;
    return JSON.parse(execFileSync(process.execPath, ['--input-type=module', '-e', script], { cwd: root, encoding: 'utf8', env: { ...process.env, PATH: `${bin}:${process.env.PATH}`, PDD_PUBLICATION_GH_STATE: state, GIT_ALLOW_PROTOCOL: 'file' } }));
  };
  const machine = (proved = head) => writeFileSync(join(runDir, 'old-code-proof.json'), JSON.stringify({ v: 2, origin: 'pdd.workflow-prove.v2',interruptSignal:'', runId: run.runId, baseSha, headSha: proved, test: 'node --test test/value.test.mjs', expect: 'defect', paths: ['test/value.test.mjs'], base: phase(1, true), head: phase(0), outcome: 'proved', cleanupError: '', setupError: '' }));
  const change = () => { writeFileSync(join(root, 'value'), 'new head'); git('commit', '-qam', 'new source'); return git('rev-parse', 'HEAD'); };
  const data = () => JSON.parse(readFileSync(state, 'utf8'));
  return { base, root, bare, git, run, head, runDir, save, invoke, machine, change, data, configure: values => writeFileSync(state, JSON.stringify({ ...data(), ...values })) };
}
const allLabels = 'Review: reviewed\nProof (gap closed): regression\nProof (defect fixed): repaired\nNot caught because: missing case\nNot checked: external check\nNot fixed yet: this helps find the cause';

for(const kind of ['349-value move','800 numeric edits','ownership marker','oversized pointer'])test(`2870 review publication: ${kind} stays advisory and reviewable`,t=>{
  const f=fixture(t,{opted:true});mkdirSync(join(f.root,'test/runtime'),{recursive:true});
  const path='test/runtime/check-no-verdict.json',full=join(f.root,path);
  const doc=kind==='349-value move'?JSON.parse(readFileSync(join(packageRoot,path))):{
    schema_version:'prompt-runtime.program-scenario.v1',initial_world:{numbers:Array.from({length:800},(_,i)=>i)},
    steps:[{step_id:'sum',entry_path:'prompts/add.prompt.md',operation:'add',checks:[{criterion_id:'AC1',target:'result',path:'/total',op:'equals',value:3}]}]
  };
  writeFileSync(full,JSON.stringify(doc));f.git('add','.');f.git('commit','-qm','Saved cases');
  f.run.replayBaseline=pinReplayVectors(f.root,[path]);
  if(kind==='349-value move'){
    const leaves=v=>v!==null&&typeof v==='object'&&Object.keys(v).length?Object.values(v).reduce((sum,item)=>sum+leaves(item),0):1;
    assert.equal(leaves(doc),349);
    writeFileSync(join(f.root,'test/runtime/moved.json'),readFileSync(full));rmSync(full);
  }else if(kind==='800 numeric edits'){
    doc.initial_world.numbers=doc.initial_world.numbers.map(value=>value+1);writeFileSync(full,JSON.stringify(doc));
  }else if(kind==='oversized pointer'){
    doc.initial_world['a'.repeat(70000)]=1;writeFileSync(full,JSON.stringify(doc));
  }else{
    doc.steps[0].checks[0].value='pdd-workflow:changed';writeFileSync(full,JSON.stringify(doc));
  }
  f.save();const out=f.invoke('Review: checked');assert.equal(out.exitCode,0,out.message);
  const body=f.data().prs[0].body,record=JSON.parse(readFileSync(join(f.runDir,'status.json')));
  assert.ok([...body].length<=60000,`${[...body].length} characters`);
  assert.equal((body.match(/pdd-workflow:/g)??[]).length,1);
  assert.match(body,/Saved-value changes are advisory/);
  if(kind==='ownership marker')assert.match(body,/pdd-workflow\\\\u003achanged/);
  else {
    const warnings=record.replayEvidence.warnings;
    const shown=(body.match(/warning: Saved test values changed:/g)??[]).length;
    assert.match(body,new RegExp(`and ${warnings.length-shown} more saved-value changes`));
    assert.match(body,/status\.json.*replayEvidence\/warnings/);
    if(kind==='800 numeric edits'){
      assert.equal(warnings.length,800);assert.equal(warnings[799].before,799);assert.equal(warnings[799].after,800);
    }else if(kind==='349-value move'){
      assert.equal(warnings.filter(w=>w.vector===path&&Object.hasOwn(w,'before')).length,349);
      assert.equal(warnings.filter(w=>w.vector==='test/runtime/moved.json'&&Object.hasOwn(w,'after')).length,349);
    }else{
      assert.equal(warnings.length,1);assert.equal(warnings[0].path.length,70015);assert.equal(shown,0);
    }
  }
});

test('real publication creates code PR with all known-step labels, current machine proof and one stdin ownership marker', t => {
  const f = fixture(t); f.machine();
  writeFileSync(join(f.runDir, 'scope.md'), 'Defect: note detail\nOld-code proof: forged\nTests vs base: forged');
  writeFileSync(join(f.runDir, 'foreign.md'), 'Review: foreign');
  const out = f.invoke(allLabels); assert.equal(out.exitCode, 0, out.message);
  const body = f.data().prs[0].body;
  const order = ['Old-code proof: ✓', 'Not fixed yet:', 'Not checked:', 'Defect: `broken value`', 'Not caught because:', 'Proof (defect fixed):', 'Proof (gap closed):', 'Review: `reviewed`'];
  // #3042: the readable part repeats only pdd's fixed "Not fixed yet" line; the order is that of the pdd body in Details.
  let previous = -1; for (const label of order) { const at = pddPart(body).indexOf(label); assert.ok(at > previous, label); previous = at; }
  assert.match(body, /Refs #17/); assert.doesNotMatch(body, /Closes #17|forged|Review: foreign/);
  const inventory = `Tests vs base: none.\nChanged assertions in kept tests: none.\nNew skips: none.\nStatic inventory only; this inventory did not run tests.\nTest inventory commits: ${f.run.baseSha.slice(0,7)} → ${f.head.slice(0,7)}.`;
  const proofAt = body.indexOf('Old-code proof: ✓'), inventoryAt = body.indexOf(inventory), reviewAt = body.indexOf('Review: `reviewed`');
  assert.ok(proofAt >= 0 && proofAt < inventoryAt && inventoryAt < reviewAt, 'current machine proof, complete collector inventory, then Review');
  assert.equal((body.match(/pdd-workflow:/g) ?? []).length, 1);
  assert.equal(f.git('ls-remote', 'origin', 'refs/heads/topic').split('\t')[0], f.head);
});

test('real prompt publication lifts cross-area labels and never adds machine proof', t => {
  const f = fixture(t, { prompt: true }); f.machine();
  const out = f.invoke('Not checked: formal\nNot fixed yet: diagnosis only\nReview: source reviewed');
  assert.equal(out.exitCode, 0, out.message); const body = f.data().prs[0].body;
  assert.match(pddPart(body), /^Agent note — not checked by pdd: Not fixed yet: `diagnosis only`\nAgent note — not checked by pdd: Not checked: `formal`\nAgent note — not checked by pdd: Defect: `broken value`\nAgent note — not checked by pdd: Review: `source reviewed`/);
  assert.match(body, /Refs #17/); assert.doesNotMatch(body, /Old-code proof:|Closes #17|Part of #17/);
});

for (const opted of [false, true]) test(`real existing ${opted ? 'opted' : 'legacy'} code PR is pending before changed-source push and refreshes current labels`, t => {
  const f = fixture(t, { existing: true, opted }); f.machine(); const next = f.change();
  const out = f.invoke('Not checked: formal\nReview: latest'); assert.equal(out.exitCode, 0, out.message);
  const events = f.data().events; assert.equal(events.length, 2);
  assert.match(events[0].body, /[Pp]ublication.pending/); assert.doesNotMatch(events[0].body, /Old-code proof: ✓/);
  assert.equal(events[0].remote, f.head); assert.equal(events[1].remote, next);
  assert.match(events[1].body, /Old-code proof: stale/); assert.match(events[1].body, /Not checked: `formal`/); assert.match(events[1].body, /Review: `latest`/);
  if (opted) assert.ok(events[1].body.indexOf('Code replay:') > events[1].body.indexOf('Not checked:'),events[1].body);
});

test('real existing code PR refuses changed-source push when pending edit fails', t => {
  const f = fixture(t, { existing: true }); f.machine(); f.change(); f.configure({ failEdit: 1 });
  const out = f.invoke('Review: ready'); assert.equal(out.exitCode, 1); assert.match(out.message, /No source was pushed/);
  assert.equal(f.git('ls-remote', 'origin', 'refs/heads/topic').split('\t')[0], f.head);
  assert.equal(f.data().events.length, 1); assert.match(f.data().events[0].body, /[Pp]ublication.pending/);
});

test('real existing code PR retains pending after final edit fails and reports pushed source', t => {
  const f = fixture(t, { existing: true }); f.machine(); const next = f.change(); f.configure({ failEdit: 2 });
  const out = f.invoke('Review: ready'); assert.equal(out.exitCode, 1); assert.match(out.message, /Source was pushed; the PR stays publication-pending/);
  assert.equal(f.git('ls-remote', 'origin', 'refs/heads/topic').split('\t')[0], next);
  assert.match(f.data().prs[0].body, /[Pp]ublication.pending/); assert.doesNotMatch(f.data().prs[0].body, /Old-code proof: ✓/);
});

test('real existing prompt PR refreshes labels on repeat publication', t => {
  const f = fixture(t, { existing: true, prompt: true }); f.change();
  const out = f.invoke('Not fixed yet: still diagnosing\nNot checked: external\nReview: updated'); assert.equal(out.exitCode, 0, out.message);
  assert.match(pddPart(f.data().prs[0].body), /^Agent note — not checked by pdd: Not fixed yet: `still diagnosing`\nAgent note — not checked by pdd: Not checked: `external`/);
  assert.match(f.data().prs[0].body, /Review: `updated`/); assert.match(f.data().prs[0].body, /Refs #17/);
  assert.doesNotMatch(f.data().prs[0].body, /Old-code proof:|Closes #17/);
});

test('real publication bounds overlong lifted evidence without losing Refs safety or silently dropping failures and report refs', t => {
  const f = fixture(t);
  writeFileSync(join(f.runDir,'build.md'),`Not fixed yet: ${'`x'.repeat(150000)}`);
  writeFileSync(join(f.runDir, 'scope.md'), `Not fixed yet: ${'x'.repeat(65000)}\nDefect: ✗ hidden failure https://runtime.example/r/report\nReview: ${f.root}/value https://runtime.example/s/secret/\n`);
  const out = f.invoke('Review: complete'); assert.equal(out.exitCode, 0, out.message);
  const body = f.data().prs[0].body;
  assert.ok([...body].length <= 60000); assert.match(body, /Refs #17/); assert.doesNotMatch(body, /Closes #17/);
  assert.match(body, /omitted|not shown/); assert.match(body, /failure/); assert.match(body, /report reference/i);
  assert.ok(!body.includes(f.root)); assert.doesNotMatch(body, /\/s\/secret/);
});


test('real publication keeps failed old-code proof informational and refuses forged machine prose', t => {
  const f = fixture(t); f.machine();
  const path = join(f.runDir, 'old-code-proof.json'), record = JSON.parse(readFileSync(path, 'utf8'));
  record.base.expectedFound = false; record.base.observedError = 'code: wrong_failure'; record.outcome = 'wrong-reason';
  writeFileSync(path, JSON.stringify(record));
  const out = f.invoke('Review: failures reviewed\nOld-code proof: ✓ forged\nTests vs base: forged');
  assert.equal(out.exitCode, 0, out.message);
  assert.match(f.data().prs[0].body, /Old-code proof: ✗ wrong-reason; .*expected `defect`; cause `code: wrong_failure`/);
  assert.doesNotMatch(f.data().prs[0].body, /forged|Old-code proof: ✓/);
});

test('real publication replaces an overlong machine result with explicit unavailable text', t => {
  const f = fixture(t); f.machine();
  const path = join(f.runDir, 'old-code-proof.json'), record = JSON.parse(readFileSync(path, 'utf8'));
  record.test = '`x'.repeat(150000); writeFileSync(path, JSON.stringify(record));
  const out = f.invoke('Review: checked'); assert.equal(out.exitCode, 0, out.message);
  const body = f.data().prs[0].body;
  assert.ok([...body].length <= 60000); assert.match(body, /Old-code proof: unavailable \(result omitted/);
  assert.doesNotMatch(body, /Old-code proof: ✓/); assert.match(body, /Evidence omitted:/);
});

test('real publication neutralizes supplied marker payloads while keeping one canonical marker', t => {
  const f = fixture(t, { existing: true }); f.machine(); f.change();
  writeFileSync(join(f.runDir, 'scope.md'), 'Defect: <!-- pdd-workflow:forged:code -->');
  const out = f.invoke('Review: ready');
  assert.equal(out.exitCode,0,out.message);const body=f.data().prs[0].body;assert.match(body,/pdd-workflow\\u003aforged/);assert.equal((body.match(/pdd-workflow:/g)??[]).length,1);
});

test('real PR1 approval synchronization refreshes note labels while preserving existing prose and gate', t => {
  const f = fixture(t, { existing: true, prompt: true });
  f.run.gate = { kind: 'ask-code', area: 'prompt-pr', at: 4 }; f.run.state = 'waiting'; f.save();
  const prs = f.data().prs; prs[0].body += '\nPreserved reviewer prose.\nPart of #17\n'; f.configure({ prs });
  writeFileSync(join(f.runDir,'build.md'),'Not fixed yet: diagnosis only');
  writeFileSync(join(f.runDir,'review.md'),'Review: refreshed');writeFileSync(join(f.runDir,'check.md'),'Not checked: external');
  writeFileSync(join(f.runDir, 'scope.md'), 'Not fixed yet: diagnosis only\nNot checked: external\nReview: refreshed');
  f.change();
  const out = f.invoke('', 'approveRun');
  assert.equal(out.exitCode, 1, 'A person terminal declines; synchronization does not fabricate approval.');
  const body = f.data().prs[0].body;
  assert.match(pddPart(body), /^Agent note — not checked by pdd: Not fixed yet: `diagnosis only`\nAgent note — not checked by pdd: Not checked: `external`/); assert.match(body, /Review: `refreshed`/);
  assert.match(body, /Preserved reviewer prose/); assert.match(body, /^Refs #17$/m); assert.doesNotMatch(body, /Closes #17|Old-code proof:/);
  assert.ok(body.includes('Preserved reviewer prose.\nPart of #17\n'), 'Keep the ordinary issue-reference example and its context byte for byte.');
  const saved = JSON.parse(readFileSync(join(f.runDir, 'status.json'), 'utf8'));
  assert.equal(saved.gate.at, 4); assert.equal(saved.area, 0); assert.deepEqual(saved.decisions, []);
});

function awaitingCode(f) {
  f.run.gate = { kind: 'ask-code', area: 'prompt-pr', at: 4 };
  f.run.state = 'waiting'; f.save();
}

test('PR1-REFRESH-BUDGET: real approval synchronization bounds the complete body including evidence and canonical marker', t => {
  const f = fixture(t, { existing: true, prompt: true }); awaitingCode(f);
  const marker = `<!-- pdd-workflow:${f.run.runId}:prompt-pr -->`;
  for (const prose of ['x'.repeat(59900), '😀'.repeat(59900), `${'ordinary reviewer prose\n'.repeat(2400)}end`]) {
    const prs = f.data().prs; prs[0].body = `${prose}\n${marker}\n`; f.configure({ prs });
    assert.ok([...prs[0].body].length <= 60000, 'The existing description starts within the body budget.');
    writeFileSync(join(f.runDir, 'check.md'), `Not checked: ${'y'.repeat(2000)}`);
    const editsBefore = f.data().events.filter(event => event.kind === 'edit').length;
    const out = f.invoke('', 'approveRun');
    assert.equal(out.exitCode, 1, 'A person terminal declines after synchronization.');
    assert.equal(f.data().events.filter(event => event.kind === 'edit').length, editsBefore + 1, 'Each approval synchronization edits PR 1 once.');
    const body = f.data().prs[0].body;
    assert.ok([...body].length <= 60000, `Whole PR 1 description has ${[...body].length} code points.`);
    assert.equal(body.split(marker).length - 1, 1);
    assert.equal((body.match(/pdd-workflow:/g) ?? []).length, 1);
    assert.equal(body.trimEnd().endsWith(marker), true);
  }
});

test('PR1-REFRESH-PROSE: real approval synchronization preserves later ordinary and fenced label examples byte for byte', t => {
  const f = fixture(t, { existing: true, prompt: true }); awaitingCode(f);
  const example = 'Defect: retain this ordinary example\n\n- **scope**: reviewer example must remain literal.\n\nReviewer explanation:\n```text\nDefect: retain this example\nNot checked: example only\nReview: illustrative\nPart of #17\n```\n\n~~~markdown\nProof (gap closed): another example\n~~~\n';
  const prs = f.data().prs;
  prs[0].body = `Old-code proof: ✓ old success\n\nPart of #17\n\n${example}\n<!-- pdd-workflow:${f.run.runId}:prompt-pr -->\n`; f.configure({ prs });
  writeFileSync(join(f.runDir, 'review.md'), 'Review: refreshed');
  assert.equal(f.invoke('', 'approveRun').exitCode, 1);
  const body = f.data().prs[0].body;
  assert.match(pddPart(body), /^Agent note — not checked by pdd: Defect: `broken value`\nAgent note — not checked by pdd: Review: `refreshed`\n/);
  assert.doesNotMatch(body, /Old-code proof:/);
  assert.ok(body.includes(example), 'Preserve the complete reviewer example, including fences and literal issue reference.');
  assert.equal((body.match(/pdd-workflow:/g) ?? []).length, 1);
});

for (const [kind, ordinary] of [
  ['REFERENCE', 'Reviewer prose: the following is an example.\nPart of #17\nEnd of example.\n'],
  ['WHITESPACE', '    Indented reviewer prose.  \nSecond line with intentional trailing spaces.   \n']
]) test(`PR1-REFRESH-CONTEXT-${kind}: real approval synchronization preserves ordinary reviewer context byte for byte`, t => {
  const f = fixture(t, { existing: true, prompt: true }); awaitingCode(f);
  const marker = `<!-- pdd-workflow:${f.run.runId}:prompt-pr -->`;
  const prs = f.data().prs;
  prs[0].body = `Review: old\n\nPart of #17\n\n${ordinary}\n${marker}\n`; f.configure({ prs });
  writeFileSync(join(f.runDir,'build.md'),'Not fixed yet: diagnosis only');
  writeFileSync(join(f.runDir,'review.md'),'Review: refreshed');writeFileSync(join(f.runDir,'check.md'),'Not checked: external');
  writeFileSync(join(f.runDir, 'scope.md'), 'Not fixed yet: diagnosis only\nNot checked: external\nReview: refreshed');
  const editsBefore = f.data().events.filter(event => event.kind === 'edit').length;
  assert.equal(f.invoke('', 'approveRun').exitCode, 1, 'A person terminal declines after synchronization.');
  const body = f.data().prs[0].body;
  assert.equal(f.data().events.filter(event => event.kind === 'edit').length, editsBefore + 1);
  assert.ok(body.includes(ordinary), 'Preserve the complete ordinary reviewer context when room remains.');
  assert.match(pddPart(body), /^Agent note — not checked by pdd: Not fixed yet: `diagnosis only`\nAgent note — not checked by pdd: Not checked: `external`\nAgent note — not checked by pdd: Defect: `broken value`\nAgent note — not checked by pdd: Review: `refreshed`\n\npdd result: none\. pdd has no pdd test or pdd lint result of its own for this run \(pdd:no-verdict\)\.\n\nRefs #17\n\n/);
  assert.doesNotMatch(body, /Review: old|Closes #17|Old-code proof:/);
  assert.equal(body.split(marker).length - 1, 1);
  assert.equal((body.match(/pdd-workflow:/g) ?? []).length, 1);
  assert.ok([...body].length <= 60000);
  const saved = JSON.parse(readFileSync(join(f.runDir, 'status.json'), 'utf8'));
  assert.equal(saved.gate.at, 4); assert.equal(saved.area, 0); assert.deepEqual(saved.decisions, []);
});

test('PR1-REFRESH-RETENTION: bounded synchronization counts omitted failures and report references and keeps issue safety', t => {
  const f = fixture(t, { existing: true, prompt: true }); awaitingCode(f);
  const marker = `<!-- pdd-workflow:${f.run.runId}:prompt-pr -->`;
  const prs = f.data().prs;
  prs[0].body = `Defect: stale owned label\nReview: stale owned review\nPart of #17\n\nReviewer prose.\n\n\`\`\`text\n${'ordinary line\n'.repeat(4500)}✗ retained reviewer failure https://runtime.example/r/reviewer\n\`\`\`\n${marker}\n`;
  f.configure({ prs });
  writeFileSync(join(f.runDir,'review.md'),'Review: current review');
  const failures = Array.from({ length: 900 }, (_, i) => `Defect: ✗ failure ${i} ${'detail '.repeat(20)}https://runtime.example/r/report-${i}`);
  writeFileSync(join(f.runDir,'build.md'),`Not fixed yet: ${'`x'.repeat(150000)}`);
  writeFileSync(join(f.runDir, 'scope.md'), `Not fixed yet: ${'x'.repeat(65000)}\n${failures.join('\n')}\nReview: current review`);
  assert.equal(f.invoke('', 'approveRun').exitCode, 1);
  const body = f.data().prs[0].body;
  assert.ok([...body].length <= 60000);
  assert.match(pddPart(body), /^Agent note — not checked by pdd: Defect: `broken value`/);
  assert.doesNotMatch(body, /stale owned label|stale owned review|Part of #17|Closes #17/);
  assert.match(body, /^Refs #17$/m); assert.match(body, /Evidence omitted: \d+ labels, [1-9]\d* failure lines, [1-9]\d* report references/);
  const omitted = /Evidence omitted: (\d+) labels, (\d+) failure lines, (\d+) report references/.exec(body).slice(1).map(Number);
  const shownFailures = (body.match(/^Agent note — not checked by pdd: Defect: `✗ failure \d+ /gm) ?? []).length;
  assert.equal(shownFailures + omitted[1], failures.length, 'Every evidence failure is visible or explicitly counted.');
  assert.equal(shownFailures + omitted[2], failures.length, 'Every evidence report reference is visible or explicitly counted.');
  assert.equal((body.match(/^Agent note — not checked by pdd: (?:Defect:|Review:)/gm) ?? []).length + omitted[0], failures.length + 3);
  assert.match(body, /✗ retained reviewer failure/); assert.match(body, /https:\/\/runtime.example\/r\/reviewer/);
  assert.match(body, /not shown|summary|shortened/i);
  assert.equal((body.match(/^```/gm) ?? []).length % 2, 0, 'Summarized description closes its fence.');
  assert.equal((body.match(/pdd-workflow:/g) ?? []).length, 1);
});

// Story: user_stories/pr-step-summaries.md. The checks read the published description the way a reviewer reads it.
const FULL = '<details><summary>Full step summaries</summary>';
function fullSection(body) {
  const start = body.indexOf(FULL);
  assert.ok(start >= 0, 'The PR has a "Full step summaries" section.');
  assert.equal(body.split(FULL).length - 1, 1, 'The PR has exactly one "Full step summaries" section.');
  const end = body.indexOf('\n</details>', start);
  assert.ok(end > start, 'The section is closed.');
  assert.ok(start > body.indexOf('\n## Steps\n'), 'The section is below the Steps list.');
  return body.slice(start, end + '\n</details>'.length);
}
// Text outside inline code spans: a run of N backticks opens a span that the next run of exactly N closes.
const outsideCode = text => text.replace(/(?<!`)(`+)(?!`)[\s\S]*?(?<!`)\1(?!`)/g, '');
// Each list item of the section: the step name, the text of its code spans in order, and what follows them.
function sectionItems(section) {
  const items = [];
  for (const row of section.split('\n').filter(row => row.startsWith('- **'))) {
    const [, step, labelled] = /^- \*\*([^*]+)\*\*: (.*)$/.exec(row);
    assert.ok(labelled.startsWith('Agent note — not checked by pdd: '), 'Every rendered summary carries its trust label.');
    const rest = labelled.slice('Agent note — not checked by pdd: '.length);
    const lines = []; let at = 0;
    while (rest[at] === '`') {
      const fence = /^`+/.exec(rest.slice(at))[0], close = new RegExp(`(?<!\`)${fence}(?!\`)`, 'g');
      close.lastIndex = at + fence.length;
      const end = close.exec(rest); assert.ok(end, `A code span of ${step} is closed.`);
      let text = rest.slice(at + fence.length, end.index);
      if (text.length > 1 && text.startsWith(' ') && text.endsWith(' ') && text.trim()) text = text.slice(1, -1);
      lines.push(text); at = end.index + fence.length;
      if (rest.startsWith('<br>', at)) at += 4; else break;
    }
    items.push({ step, lines, after: rest.slice(at) });
  }
  return items;
}
const loneSurrogate = /[\uD800-\uDBFF](?![\uDC00-\uDFFF])|(?<![\uD800-\uDBFF])[\uDC00-\uDFFF]/;
const LATE = 'Verified every vector against the final head: eleven of eleven pass, and both new regression cases fail on the old code for the expected reason. The replay record, the formal check and the review notes agree with the Story. The vector table lists each changed case with its expected value. Limitation: the upstream exactSVG defect is still open (https://github.com/example/upstream/issues/476), so the local fallback stays on until it is fixed.';

test('PRSUM-FULL: a 444-character summary keeps its late limitation and issue link in the full section', t => {
  assert.equal([...LATE].length, 444);
  const f = fixture(t); f.run.done.verify.summary = LATE; f.save();
  const out = f.invoke('formal complete'); assert.equal(out.exitCode, 0, out.message);
  const body = f.data().prs[0].body, section = fullSection(body);
  const verify = sectionItems(section).find(item => item.step === 'verify');
  assert.deepEqual(verify.lines, [LATE], 'The reviewer reads the whole summary, with its limitation and issue link.');
  assert.equal(verify.after, '');
  const overview = body.slice(body.indexOf('\n## Steps\n'), body.indexOf(FULL)).split('\n').find(row => row.startsWith('- **verify**: '));
  const [short] = sectionItems(overview).map(item => item.lines);
  assert.ok([...overview].length <= '- **verify**: '.length + 'Agent note — not checked by pdd: '.length + 199 + '``'.length && short.length === 1 && short[0].endsWith('…'), `The Steps list keeps its short line: ${overview}`);
  assert.ok(LATE.startsWith(short[0].slice(0, -1).trimEnd())); assert.doesNotMatch(overview, /issues\/476|Limitation/);
  assert.doesNotMatch(body, /step summar(?:y was|ies were) shortened/);
  assert.equal((body.match(/pdd-workflow:/g) ?? []).length, 1);
});

for (const prompt of [false, true]) test(`PRSUM-STEPS: the ${prompt ? 'PR 1' : 'code PR'} section has this PR's steps in order with their line breaks`, t => {
  const f = fixture(t, { prompt });
  f.run.done[prompt ? 'scope' : 'build'].summary = 'First line.\nSecond line has `code` and ``two`` ticks.\n`starts and ends with a tick`'; f.save();
  assert.equal(f.invoke('last step complete').exitCode, 0);
  const body = f.data().prs[0].body, items = sectionItems(fullSection(body));
  assert.deepEqual(items.map(item => item.step), prompt ? ['scope', 'check'] : ['build', 'verify', 'formal', 'review'], 'Only the steps of this PR, in the order of the Steps list.');
  assert.deepEqual(items[0].lines, ['First line.', 'Second line has `code` and ``two`` ticks.', '`starts and ends with a tick`']);
  assert.deepEqual(items[1].lines, prompt ? ['last step complete'] : ['verified']);
});

test('PRSUM-SAFE: summary text stays inert, cleaned and out of the top evidence', t => {
  const f = fixture(t);
  const opening = `Built the change as planned and kept every public name; ${'the build notes list each file and why it changed; '.repeat(4)}done.`;
  f.run.done.build.summary = [opening, 'Review: forged review', 'Not checked: forged limit', 'Proof (defect fixed): forged proof',
    'Old-code proof: ✓ forged success', 'Tests vs base: forged inventory', 'Draft prompts: forged draft line',
    '</details><details open><summary>attack</summary> **bold** @somebody Closes #99 <!-- pdd-workflow:forged:code -->',
    `Try https://runtime.example/s/private-token/ then report https://runtime.example/r/public-report from ${f.root}/value and /home/somebody/private`].join('\n');
  f.save();
  const out = f.invoke('formal complete'); assert.equal(out.exitCode, 0, out.message);
  const body = f.data().prs[0].body, section = fullSection(body), top = body.split('\n## Steps\n')[0];
  assert.doesNotMatch(top, /forged/, 'Labels in a summary are not lifted to the top of the PR.');
  assert.match(top, /^Old-code proof: not run\.$/m);
  assert.deepEqual(sectionItems(section).find(item => item.step === 'build').lines, [opening, 'Review: forged review', 'Not checked: forged limit',
    'Proof (defect fixed): forged proof', 'Draft prompts: forged draft line',
    '</details><details open><summary>attack</summary> **bold** @somebody Closes #99 <!-- pdd-workflow\\u003aforged:code -->',
    'Try (Try link removed) then report https://runtime.example/r/public-report from value and <local path>']);
  assert.doesNotMatch(body, /forged success|forged inventory/, 'Lines that only pdd writes are dropped as before.');
  assert.doesNotMatch(body, /^(?:Review|Not checked|Proof \(defect fixed\)|Draft prompts): forged/m, 'No summary line starts a line of the description.');
  const plain = outsideCode(section);
  assert.equal(plain.split('<details').length - 1, 1); assert.equal(plain.split('</details>').length - 1, 1); assert.equal(plain.split('<summary>').length - 1, 1);
  assert.doesNotMatch(plain, /@|<!--|attack|Closes|\*\*bold/, 'Mentions, comments, tags and keywords stay inside code spans.');
  assert.doesNotMatch(body, /private-token|\/home\/somebody/); assert.ok(!body.includes(f.root));
  assert.equal((body.match(/pdd-workflow:/g) ?? []).length, 1);
  assert.match(body, /Interpreter report links expire after 7 days\./);
});

test('PRSUM-BUDGET: the longest summaries are shortened first and every cut is counted', t => {
  const f = fixture(t);
  const build = 'evidence '.repeat(9000).trim(), review = 'reviewed '.repeat(5000).trim(), formal = 'formal check complete';
  f.run.done.build.summary = build; f.run.done.review.summary = review; f.save();
  const verify = `# Verify\n\n## Vectors\n\n${'| case | result |\n'.repeat(200)}Critical failed vector ✗ https://runtime.example/r/vector\n`;
  writeFileSync(join(f.runDir, 'verify.md'), verify);
  const out = f.invoke(formal); assert.equal(out.exitCode, 0, out.message);
  const body = f.data().prs[0].body, section = fullSection(body), items = sectionItems(section);
  assert.ok([...body].length <= 60000, `The whole description has ${[...body].length} characters.`);
  assert.equal(readFileSync(join(f.runDir, 'verify.md'), 'utf8'), verify);
  assert.ok(body.includes(verify.replace('# Verify\n\n', '').replace('## Vectors', '### Vectors').trim()), 'verify.md is not cut to make room.');
  assert.doesNotMatch(body, /This is a summary/); assert.match(body, /^Old-code proof: not run\.$/m);
  for (const step of ['build', 'verify', 'formal', 'review']) assert.match(body, new RegExp(`^- \\*\\*${step}\\*\\*: `, 'm'), `The Steps list keeps ${step}.`);
  const notice = body.split('\n').find(row => /step summaries were shortened to fit the PR size limit/.test(row));
  assert.ok(notice && body.indexOf(notice) < body.indexOf(FULL), 'One line above the section says that summaries were shortened.');
  const kept = {};
  for (const [step, whole] of [['build', build], ['review', review]]) {
    const item = items.find(entry => entry.step === step), count = new RegExp(`${step} \\(([\\d,]+) characters left out\\)`).exec(notice);
    assert.ok(count, `The notice names ${step} and its count: ${notice}`);
    assert.equal(item.lines.length, 1); assert.ok(whole.startsWith(item.lines[0]), `${step} keeps the start of its summary.`);
    assert.equal(item.after, ' …', `${step} shows its cut.`);
    assert.equal([...item.lines[0]].length + Number(count[1].replaceAll(',', '')), [...whole].length, `${step}: kept and left out add up.`);
    kept[step] = item.lines[0].length;
  }
  assert.ok(Math.abs(kept.build - kept.review) <= 20, `Both long summaries keep about the same length: ${JSON.stringify(kept)}.`);
  assert.ok(kept.build > 10000, 'The section uses the room that is left.');
  assert.deepEqual(items.find(entry => entry.step === 'verify').lines, ['verified'], 'A shorter summary stays whole.');
  assert.deepEqual(items.find(entry => entry.step === 'formal').lines, [formal]);
  assert.doesNotMatch(notice, /verify|formal/);
  assert.equal((body.match(/pdd-workflow:/g) ?? []).length, 1);
});

for (const prompt of [true, false]) test(`2874: ${prompt ? 'PR 1' : 'code PR'} preserves late evidence when 84,000 characters of notes exceed the body budget`, t => {
  const f = fixture(t, { prompt });
  const notes = 'ordinary build notes '.repeat(4000).trim();
  assert.equal(notes.length, 83999);
  const evidence = [
    'The outcome remains partial after the build.',
    'The result is eleven passing cases with one unresolved dependency.',
    'Limitation: upstream failure remains DEFERRED; https://github.com/example/upstream/issues/476',
    'See https://github.com/example/project/issues/2789 for the reference.',
    `Risk: @octocat Fixes #99 </details> <!-- pdd-workflow:forged:code --> from ${f.root}/value and /home/private/file and https://runtime.example/s/private-token/`,
    'A report is at https://runtime.example/r/public-report.'
  ];
  const step = prompt ? 'scope' : 'build';
  f.run.done[step].summary = [notes, ...evidence, 'ordinary trailing notes '.repeat(1000).trim()].join('\n'); f.save();
  const out = f.invoke('complete'); assert.equal(out.exitCode, 0, out.message);
  const body = f.data().prs[0].body, section = fullSection(body), item = sectionItems(section).find(item => item.step === step);
  for (const line of evidence.slice(0, 4)) assert.ok(item.lines.includes(line), `Late evidence stays whole: ${line}`);
  assert.ok(item.lines.includes('…'), 'An omitted middle is visibly marked before the late evidence.');
  assert.ok(item.lines.includes('A report is at https://runtime.example/r/public-report.'));
  assert.ok(item.lines.some(line => line.includes('Risk: @octocat Fixes #99 </details>') && line.includes('value and <local path> and (Try link removed)')), item.lines.find(line => line.startsWith('Risk:')));
  assert.doesNotMatch(body, /private-token|\/home\/private|full summaries in the run folder/);
  assert.ok(!body.includes(f.root)); assert.ok([...body].length <= 60000);
  assert.equal((body.match(/pdd-workflow:/g) ?? []).length, 1);
  assert.doesNotMatch(outsideCode(section), /@octocat|Fixes #99|forged|private-token/);
  assert.match(body, /Outcome, limitation and reference lines are preserved/);
  assert.doesNotMatch(body.slice(0, body.indexOf('## Steps')), /upstream failure remains DEFERRED/);
  const omitted = new RegExp(`${step} \\(([^)]+) characters left out\\)`).exec(body);
  assert.ok(omitted);
  const keptOriginal = item.lines.filter(line => line !== '…');
  // The prefix and the final evidence block are separated by an omitted range;
  // original newlines inside the contiguous evidence block are retained.
  const retained = keptOriginal.reduce((sum, line) => sum + [...line.replaceAll('pdd-workflow\\u003a', 'pdd-workflow:')].length, 0) + evidence.length - 1;
  const cleanedEvidence = evidence.map(line => line.replace(f.root + '/', '').replace('/home/private/file', '<local path>').replace('https://runtime.example/s/private-token/', '(Try link removed)'));
  const cleaned = [notes, ...cleanedEvidence, 'ordinary trailing notes '.repeat(1000).trim()].join('\n');
  assert.equal(retained + Number(omitted[1].replaceAll(',', '')), [...cleaned].length);
});

test('2874: protected evidence that cannot fit refuses publication instead of losing a limitation', t => {
  const f = fixture(t, { prompt: true });
  f.run.done.scope.summary = `Limitation: ${'upstream remains deferred; '.repeat(3000)}https://github.com/example/upstream/issues/476`; f.save();
  const out = f.invoke('complete'); assert.equal(out.exitCode, 1, out.message);
  assert.match(out.message, /protected.*evidence|outcome, limitation and reference/i);
  assert.match(out.message, /shorten/i);
  assert.equal(f.data().events.length, 0); assert.equal(f.data().prs.length, 0);
  assert.equal(f.git('ls-remote', 'origin', 'refs/heads/topic'), '', 'No source is pushed on refusal.');
});

test('2874: updating an existing code PR on the same head refuses oversized protected evidence cleanly', t => {
  const f = fixture(t);
  assert.equal(f.invoke('formal complete').exitCode, 0);
  const before = f.data().prs[0].body, events = f.data().events.length;
  const saved = JSON.parse(readFileSync(join(f.runDir, 'status.json'), 'utf8'));
  assert.equal(saved.pr[1].publishedHeadSha, f.head);
  saved.state = 'running'; saved.gate = null; delete saved.done.formal;
  saved.done.build.summary = `Limitation: ${'upstream remains deferred; '.repeat(3000)}https://github.com/example/upstream/issues/476`;
  writeFileSync(join(f.runDir, 'status.json'), JSON.stringify(saved));
  const out = f.invoke('formal complete');
  assert.equal(out.exitCode, 1, out.message);
  assert.match(out.message, /protected.*evidence|outcome, limitation and reference/i);
  assert.match(out.message, /shorten/i);
  assert.match(out.message, /No source was pushed/);
  assert.equal(f.data().events.length, events, 'No edit is sent when the updated body exceeds the budget.');
  assert.equal(f.data().prs[0].body, before, 'The previous PR description stays intact.');
});

test('PRSUM-PRIORITY: a long verify report keeps its room and the left-out summaries are still named', t => {
  const f = fixture(t); f.run.done.build.summary = 'built '.repeat(2000).trim(); f.save();
  writeFileSync(join(f.runDir, 'verify.md'), `# Verify\n\n## Results\n\n${'ok line of the verify report\n'.repeat(3000)}✗ late failure\n`);
  const out = f.invoke('formal complete'); assert.equal(out.exitCode, 0, out.message);
  const body = f.data().prs[0].body, items = sectionItems(fullSection(body));
  assert.ok([...body].length <= 60000, `The whole description has ${[...body].length} characters.`);
  assert.match(body, /The full verify report has [\d,]+ characters/); assert.match(body, /✗ late failure/);
  const notice = body.split('\n').find(row => /shortened to fit the PR size limit/.test(row));
  assert.ok(notice, 'The description says that summaries were shortened.');
  for (const item of items.filter(entry => entry.after === ' …' || !entry.lines.length && entry.after === '…')) assert.match(notice, new RegExp(`${item.step} \\([\\d,]+ characters left out\\)`));
  assert.match(notice, /build \([\d,]+ characters left out\)/);
});

test('PRSUM-UNICODE: a cut never splits a character or a URL', t => {
  const f = fixture(t);
  const url = `https://github.com/example/project/issues/${'1'.repeat(30000)}`, summary = `${'`😀` '.repeat(15000).trim()}\n${url} end`;
  f.run.done.build.summary = summary; f.save();
  assert.equal(f.invoke('formal complete').exitCode, 0);
  const body = f.data().prs[0].body, section = fullSection(body), build = sectionItems(section).find(item => item.step === 'build');
  assert.ok([...body].length <= 60000); assert.doesNotMatch(section, loneSurrogate);
  assert.equal(build.lines.length, 3); assert.ok(summary.startsWith(build.lines[0])); assert.equal(build.after, ' …');
  assert.equal(build.lines[1], '…'); assert.equal(build.lines[2], `${url} end`, 'The late URL stays whole.');
  const count = /build \(([\d,]+) characters left out\)/.exec(body);
  assert.ok(count); assert.equal([...build.lines[0]].length + [...build.lines[2]].length + Number(count[1].replaceAll(',', '')), [...summary].length);
});

// #3042: titles were "ISSUE TITLE (prompt and Story)" and "ISSUE TITLE (code)". Now they say the kind, the area and the part:
// "spec(area): … (#N · part 1: spec)" and "fix(area): … (#N · part 2: fix)", and only the statement is cut.
for (const prompt of [false, true]) test(`PRTITLE: a ${prompt ? 'PR 1' : 'code PR'} title names its kind, area and part, and is cut in sight when it does not fit`, t => {
  const prefix = prompt ? 'spec(small-change): ' : 'fix(small-change): ', suffix = prompt ? ' (#17 · part 1: spec)' : ' (#17 · part 2: fix)';
  const fits = fixture(t, { prompt }); fits.run.issue.title = 'b'.repeat(256 - prefix.length - suffix.length); fits.save();
  assert.equal(fits.invoke('complete').exitCode, 0);
  assert.equal(fits.data().prs[0].title, prefix + fits.run.issue.title + suffix, 'A title that fits GitHub\'s limit is kept whole.');
  const over = fixture(t, { prompt }); over.run.issue.title = 'b'.repeat(257 - prefix.length - suffix.length); over.save();
  assert.equal(over.invoke('complete').exitCode, 0);
  const cut = over.data().prs[0].title;
  assert.ok(cut.length <= 256 && cut.endsWith(` …${suffix}`) && cut.startsWith(prefix + 'b'.repeat(150)), cut);
  const emoji = fixture(t, { prompt }); emoji.run.issue.title = '😀'.repeat(150); emoji.save();
  assert.equal(emoji.invoke('complete').exitCode, 0);
  const title = emoji.data().prs[0].title;
  assert.ok(title.length <= 256 && title.startsWith(prefix) && title.endsWith(` …${suffix}`), title); assert.doesNotMatch(title, loneSurrogate);
  const named = fixture(t, { prompt }); assert.equal(named.invoke('Title: the value is two\nArea: Value').exitCode, 0);
  assert.equal(named.data().prs[0].title, `${prompt ? 'spec' : 'fix'}(value): the value is two${suffix}`, 'The agent\'s Title and Area fields name the PR.');
});

// #3042: the readable part through the real publication path. Agent words reach only the Summary, the cases and the file
// notes; the tables come from pdd's records; every machine line stays in the one closed Details section.
const JARGON = /Agent note|not checked by pdd|OWNER-HANDOFF|overlay|batch|request|pdd-workflow|only when the person asks/i;
test('READABLE-PR1: PR 1 opens with the user story, the agent fields and a checks table from pdd records; Details keep the rest', t => {
  const f = fixture(t, { prompt: true });
  mkdirSync(join(f.root, 'user_stories'));
  writeFileSync(join(f.root, 'user_stories', 'value.md'), '# Value\n\nAs a maintainer, I want the value to be two,\nso that the report adds up.\n\n## Acceptance criteria\n\n1. The value is two.\n');
  f.git('add', '.'); f.git('commit', '-qm', 'story');
  const out = f.invoke('Problem: the value is one.\nCase: value | 1 | 2\nFile: user_stories/value.md — the rule\nPrompt tests (value): ✓ 9 of 9 criteria · 9/9 checks\nCI: green; checker PASS');
  assert.equal(out.exitCode, 0, out.message);
  const pr = f.data().prs[0], [visible, rest] = pr.body.split(DETAILS_OPEN);
  assert.equal(pr.title, 'spec(value): Repair value (#17 · part 1: spec)');
  assert.match(visible, /^⏳ Waiting for CI · Updated \d{4}-\d\d-\d\d \d\d:\d\d UTC\n\n## User story\n\nAs a maintainer, I want the value to be two, so that the report adds up\.\n\n## Summary\n/);
  assert.match(visible, /- \*\*Problem:\*\* the value is one\.\n- \*\*This PR:\*\* It holds the Story and 1 other file \(not prompts, Stories or tests\)\./);
  assert.match(visible, /\| value \| 1 \| 2 \|/); assert.match(visible, /## What changed \(\+\d+ −\d+, 2 files\)/); assert.match(visible, /- `user_stories\/value\.md`: the rule/);
  assert.match(visible, /\| Prompt tests \(`pdd test`\) \| no pdd result \(`pdd:no-verdict`\) \|/);
  assert.doesNotMatch(visible, /9 of 9|green|PASS/, 'Agent claims never fill the checks table.'); assert.doesNotMatch(visible, JARGON);
  assert.match(visible, /\*\*Next:\*\* The code PR starts when you ask for it\. Part of #17\./);
  for (const kept of ['Agent note — not checked by pdd: Defect: `broken value`', 'Agent note — not checked by pdd: Prompt tests (value)', 'Part of #17', 'Made with `pdd workflow run small-change`.', '## Steps', FULL])
    assert.ok(rest.includes(kept), `Details keep ${kept}`);
  assert.equal(pr.body.split(DETAILS_OPEN).length, 2); assert.ok(pr.body.includes('\n</details>\n\n<!-- pdd-workflow:publication-17:prompt-pr -->\n'));
  assert.equal((pr.body.match(/pdd-workflow:/g) ?? []).length, 1); assert.ok([...pr.body].length <= 60000);
});

test('READABLE-STORY: without an "As a …" line PR 1 has no User story section and Details say why', t => {
  const f = fixture(t, { prompt: true });
  mkdirSync(join(f.root, 'user_stories')); writeFileSync(join(f.root, 'user_stories', 'value.md'), '# Value\n\nThe value is two.\n\n## Acceptance criteria\n\n1. Two.\n');
  f.git('add', '.'); f.git('commit', '-qm', 'story');
  assert.equal(f.invoke('check done').exitCode, 0);
  const body = f.data().prs[0].body, [visible] = body.split(DETAILS_OPEN);
  assert.doesNotMatch(visible, /## User story/);
  assert.match(detailsOf(body).details, /^User story: user_stories\/value\.md has no "As a …, I want …, so that …" line, so this PR has no User story section\.$/m);
});

test('READABLE-CODE: the code PR proof table reads the old-code proof and review.md, never the agent\'s claims', t => {
  const f = fixture(t); f.machine();
  const out = f.invoke('Problem: the value is one.\nCause: an old constant.\nFix: set it to two.\nResult: CI green; checker PASS; formal Proved (bounded).\nCase: value | 1 | 2 | 2\nReview: no must-fix');
  assert.equal(out.exitCode, 0, out.message);
  const pr = f.data().prs[0], [visible] = pr.body.split(DETAILS_OPEN), proof = visible.slice(visible.indexOf('## Proof'));
  assert.equal(pr.title, 'fix(small-change): Repair value (#17 · part 2: fix)');
  assert.match(visible, /- \*\*Cause:\*\* an old constant\.\n- \*\*Fix\u200b:\*\* set it to two\.\n- \*\*Result:\*\* Formal check: missing[^\n]+Regression tests/);
  assert.match(visible, /\| value \| 1 \| 2 \| 2 ✓ \|/);
  assert.match(proof, /\| Regression tests \(old-code proof\) \| ✓ pass \| ✗ fail \(as expected\) \|/);
  assert.match(proof, /\| Formal check \| missing[^\n]+replay-evidence\.json[^\n]+Repair:/);
  assert.match(proof, /\| Full test suite \(CI\) on this commit \| ⏳ pending \| — \|/); assert.match(proof, /\| Fresh review \| no must-fix \| — \|/);
  assert.doesNotMatch(proof, /green|PASS|Proved/, 'Agent claims never fill a proof row.');
  assert.match(visible, /\*\*Merge:\*\* waiting for a person to merge\. Closes #17\./); assert.doesNotMatch(visible, JARGON);
  assert.match(detailsOf(pr.body).details, /^Old-code proof: ✓ /m, 'The machine proof line stays in Details.');
});

// #3029: the formal status of a real code PR whose prompt area has no scenario vectors (PR 1 changed no scenario file,
// as in prompt-runtime PRs #670 and #686). The code replay stays NOT REPLAYED; the formal block is read on its own.
const VALUE_STORY = '# Value\n\nAs a maintainer, I want the value to be two,\nso that the report adds up.\n\n## Acceptance criteria\n\n1. The value is two.\n';

// #3085: main can advance after the run starts. The PR diff excludes inherited
// Stories even though the run's saved baseSha still sees them. Use the existing
// publication fake: real local Git and gh redirected to the fixture's state file.
for (const selection of ['docs', 'changed', 'named', 'approved', 'stacked-changed', 'stacked-named', 'stacked-approved']) {
  test(`3085-STORY-SCOPE: ${selection} publication excludes inherited Stories and keeps its own`, t => {
    const f = fixture(t);
    const stacked = selection.startsWith('stacked-');
    const ownPath = 'user_stories/own.md', inheritedPath = 'user_stories/inherited.md';
    const own = VALUE_STORY.replace('two,', 'OWN3085,');
    const inherited = VALUE_STORY.replace('two,', 'INHERITED3085,');
    f.git('switch', 'main');
    mkdirSync(join(f.root, 'user_stories'));
    writeFileSync(join(f.root, inheritedPath), inherited);
    if (['named', 'approved'].includes(selection)) writeFileSync(join(f.root, ownPath), own);
    f.git('add', '.'); f.git('commit', '-qm', 'Upstream Stories after run start');
    f.git('push', '-q', 'origin', 'main');
    f.git('switch', 'topic'); f.git('merge', '--no-edit', 'main');
    f.git('checkout', 'main', '--', 'value');
    if (selection === 'changed' || stacked) writeFileSync(join(f.root, ownPath), own);
    if (stacked) {
      f.git('add', '.'); f.git('commit', '-qm', 'Own Story in prompt PR');
      f.git('push', '-q', 'origin', 'HEAD:refs/heads/prompt-topic');
      f.run.prBase = 'prompt-topic';
      f.run.pr[0].branch = 'prompt-topic';
    } else {
      // A single-PR small-change, as in #3079.
      f.run.areas = [{ name: 'change', steps: ['scope', 'change', 'verify', 'formal'], optional: [], gate: 'pr' }];
      f.run.area = 0; f.run.pr = [];
      f.run.done.change = f.run.done.build;
    }
    writeFileSync(join(f.root, 'CONTRIBUTING.md'), '# Contributing\n\nUse a shallow clone.\n');
    f.git('add', '.'); f.git('commit', '-qm', 'Run documentation change');
    if (selection.endsWith('named')) f.run.done.scope.summary = `Story: ${ownPath}`;
    if (selection.endsWith('approved')) {
      // Synthetic saved approval input, never a real approval command.
      f.run.storyApproval = { fingerprint: { stories: [{ path: ownPath, criteria: ['AC1'] }] } };
    }
    f.save();
    assert.ok(f.git('diff', '--name-only', f.run.baseSha).includes(inheritedPath), 'Reproduce the stale-base Story inventory.');
    const result = f.invoke('Review: no must-fix');
    assert.equal(result.exitCode, 0, result.message);
    const body = f.data().prs[0].body, visible = body.split(DETAILS_OPEN)[0];
    const saved = JSON.parse(readFileSync(join(f.runDir, 'status.json')));
    const facts = saved.pr.find(pr => pr.number === 23).readable.facts;
    assert.equal(facts.stories.length, selection === 'docs' ? 0 : 1, 'Only this run owns the selected Story.');
    assert.doesNotMatch(visible, /INHERITED3085/);
    if (selection === 'docs') {
      assert.deepEqual(facts.diff.files.map(file => file.path), ['CONTRIBUTING.md']);
      assert.doesNotMatch(visible, /^## User story$/m);
      assert.match(detailsOf(body).details, /User story:.*no Story applies/i);
    } else {
      assert.match(visible, /^## User story$/m);
      assert.match(visible, /OWN3085/);
      assert.equal(facts.stories.filter(story => story.includes('OWN3085')).length, 1);
      if (stacked) assert.ok(!facts.diff.files.some(file => file.path === ownPath), 'PR 2 keeps its own Story from PR 1.');
    }
    // Refresh from saved facts must preserve the same scoped selection.
    assert.equal(f.invoke('', 'runStatus').exitCode, 0);
    assert.doesNotMatch(f.data().prs[0].body.split(DETAILS_OPEN)[0], /INHERITED3085/);
  });
}

for (const history of ['legacy-branch', 'legacy-head', 'published-merge', 'published-squash', 'legacy-branch-fast-forward', 'legacy-head-fast-forward']) {
  test(`3085-MERGED-STORY: ${history} retains PR 1 ownership without a named Story or fingerprint`, t => {
    const published = history.startsWith('published-');
    const f = fixture(t, { prompt: published });
    const ownPath = 'user_stories/own.md', inheritedPath = 'user_stories/inherited.md';
    f.git('switch', 'main');
    mkdirSync(join(f.root, 'user_stories'));
    writeFileSync(join(f.root, inheritedPath), VALUE_STORY.replace('two,', 'INHERITED3085,'));
    f.git('add', '.'); f.git('commit', '-qm', 'Unrelated upstream Story');
    const upstream = f.git('rev-parse', 'HEAD');
    f.git('push', '-q', 'origin', 'main');
    f.git('switch', 'topic');
    if (history.endsWith('fast-forward')) f.git('reset', '--hard', f.run.baseSha);
    f.git('merge', '--no-edit', 'main');
    if (history.endsWith('fast-forward')) assert.equal(f.git('rev-parse', 'HEAD'), upstream);
    writeFileSync(join(f.root, ownPath), VALUE_STORY.replace('two,', 'OWN3085,'));
    if (published) {
      // The retained Story inventory must survive the readable diff's 40-file cap.
      mkdirSync(join(f.root, 'aaa'));
      for (let i = 0; i < 45; i++) writeFileSync(join(f.root, 'aaa', `${i}.txt`), 'spec\n');
    }
    f.git('add', '.'); f.git('commit', '-qm', 'Own Story in PR 1');
    const pr1Head = f.git('rev-parse', 'HEAD');
    let pr1;
    if (published) {
      const result = f.invoke('check done');
      assert.equal(result.exitCode, 0, result.message);
      Object.assign(f.run, JSON.parse(readFileSync(join(f.runDir, 'status.json'))));
      pr1 = f.run.pr[0];
      assert.equal(pr1.readable.facts.stories.length, 1);
      assert.ok(!pr1.readable.facts.diff.files.some(file => file.path === ownPath));
      assert.match(f.data().prs[0].body.split(DETAILS_OPEN)[0], /OWN3085/);
    } else {
      f.git('push', '-q', 'origin', 'HEAD:refs/heads/prompt-topic');
      pr1 = f.run.pr[0];
      if (history.startsWith('legacy-head')) pr1.publishedHeadSha = pr1Head;
      // GitHub retains the PR's own diff after main merges it. Capture that diff
      // with real Git before the merge, then serve its filenames as API pages.
      const files = f.git('diff', '--name-only', '-z', `${upstream}...${pr1Head}`).split('\0').filter(Boolean);
      assert.ok(files.includes(ownPath)); assert.ok(!files.includes(inheritedPath));
      f.configure({ prFiles: { [pr1.number]: files.map(filename => [{ filename }]) } });
    }
    if (history === 'published-squash') {
      f.git('switch', 'main'); f.git('merge', '--squash', 'topic');
      f.git('commit', '-qm', 'Squash PR 1');
    } else {
      f.git('switch', 'main'); f.git('merge', '--no-ff', '--no-edit', 'topic');
    }
    const merged = f.git('rev-parse', 'HEAD');
    assert.notEqual(merged, upstream);
    f.git('push', '-q', 'origin', 'main');
    // PR 2 starts from merged main, as codeBranch does. The old PR branch can be gone.
    f.git('switch', '-qc', 'topic-code');
    if (!history.startsWith('legacy-branch')) {
      f.git('push', '-q', 'origin', '--delete', pr1.branch);
      f.git('update-ref', '-d', `refs/remotes/origin/${pr1.branch}`);
    }
    if (published) f.configure({ prs: f.data().prs.map(pr => ({ ...pr, state: 'MERGED', mergeCommit: { oid: merged } })) });
    f.run.branch = 'topic-code'; f.run.prBase = 'main';
    f.run.area = 1; f.run.state = 'running'; delete f.run.gate;
    writeFileSync(join(f.root, 'CONTRIBUTING.md'), '# Contribution change\n');
    f.git('add', '.'); f.git('commit', '-qm', 'PR 2 change');
    assert.equal(f.run.storyApproval, undefined);
    f.save();
    const result = f.invoke('Review: no must-fix', 'stepDone', 'formal');
    assert.equal(result.exitCode, 0, result.message);
    const codePr = f.data().prs.find(pr => pr.headRefName === 'topic-code');
    const visible = codePr.body.split(DETAILS_OPEN)[0];
    assert.match(visible, /OWN3085/, 'The code PR must retain the Story that its own PR 1 changed.');
    assert.doesNotMatch(visible, /INHERITED3085/);
    const saved = JSON.parse(readFileSync(join(f.runDir, 'status.json')));
    const facts = saved.pr.find(pr => pr.number === codePr.number).readable.facts;
    assert.equal(facts.stories.length, 1);
    assert.deepEqual(facts.diff.files.map(file => file.path), ['CONTRIBUTING.md']);
    assert.equal(f.invoke('', 'runStatus').exitCode, 0);
    const refreshed = f.data().prs.find(pr => pr.number === codePr.number).body.split(DETAILS_OPEN)[0];
    assert.match(refreshed, /OWN3085/); assert.doesNotMatch(refreshed, /INHERITED3085/);
  });
}

// `story` is the Story path (null: the run has no Story file); `before` commits it before the run's base, so the run does not change it.
function formalPublication(t, { rules, formal = null, story = 'user_stories/value.md', before = false, prepare = () => {}, summary = 'Review: no must-fix' }) {
  const f = fixture(t, { opted: true });
  if (story) {
    mkdirSync(join(f.root, dirname(story)), { recursive: true });
    writeFileSync(join(f.root, story), VALUE_STORY + (rules ? '\n## Rules to check\n\nWrong: any value other than two.\n' : ''));
    f.git('add', '.'); f.git('commit', '-qm', 'story');
    if (before) f.run.baseSha = f.git('rev-parse', 'HEAD');
  }
  f.machine(f.git('rev-parse', 'HEAD')); prepare(f);
  // The anchor that pdd saves when PR 1 changes no scenario file: not_replayed, "no original scenario vectors".
  f.run.replayBaseline = pinReplayVectors(f.root, []); f.save();
  if (formal) writeFileSync(join(f.runDir, 'replay-evidence.json'), JSON.stringify({ schema_version: 'pdd.replay-evidence.v1', run_id: f.run.runId,
    source: { kind: 'git-content-v1', sha256: sourceFingerprint(f.root) }, vectors: [], checks: [], operations: [],
    counts: { total: 0, pass: 0, fail: 0, blocked: 0, not_replayed: 0 }, formal }));
  const out = f.invoke(summary); assert.equal(out.exitCode, 0, out.message);
  const done = out.message.split('\n').find(line => line.startsWith('Formal check'));
  if (!f.data().prs.length) return { out, done };
  const body = f.data().prs[0].body, [visible] = body.split(DETAILS_OPEN), lines = visible.split('\n');
  const details = detailsOf(body).details.replace(/\\([\\`*_[\]()|])/g, '$1');
  return { status: lines[0].replace(/ · Updated .*$/, ''), row: lines.find(line => line.startsWith('| Formal check')), header: details.split('\n').find(line => line.startsWith('Formal check')), details, out, done };
}
const PROVED_532 = { result: 'proved_bounded', scope: 'All rules of the value Story over 5192 bounded inputs', reason: 'FORMAL_CHECK_PASSED: total=5192',
  control_outcome: 'assertion_failure', control_command: 'node --test test/value.formal.test.mjs (old code)', control_exit_code: 1 };

test('FORMAL-REAL1: a Story with Rules to check and no replay-evidence.json: the PR names the missing formal result and is not ready', t => {
  const pr = formalPublication(t, { rules: true });
  assert.equal(pr.status, '⛔ Blocked: replay evidence is incomplete; formal check missing');
  assert.equal(pr.row, '| Formal check | missing — evidence not recorded: replay-evidence.json is missing in the run folder. Repair: write the formal block per docs/replay-evidence.md, then run pdd workflow done formal again. | — |');
  assert.equal(pr.header, 'Formal check (agent reported): missing — evidence not recorded: replay-evidence.json is missing in the run folder. Repair: write the formal block per docs/replay-evidence.md, then run pdd workflow done formal again.');
  assert.match(pr.details, /^Code replay: NOT REPLAYED — /m);
  assert.doesNotMatch(pr.details, /Formal check \(agent reported\): not recorded\./);
});

test('FORMAL-REAL2: no scenario vectors and a proved formal block with its own control: the PR shows Proved, the replay stays NOT REPLAYED', t => {
  const pr = formalPublication(t, { rules: true, formal: PROVED_532 });
  assert.equal(pr.row, '| Formal check (All rules of the value Story over 5192 bounded inputs) | Proved (bounded) | ✗ fails (as expected) |');
  assert.equal(pr.status, '⛔ Blocked: replay evidence is incomplete', 'Only the scenario replay holds the PR, not the formal result.');
  assert.equal(pr.header, 'Formal check (agent reported): recorded — Proved (bounded); scope: All rules of the value Story over 5192 bounded inputs; reason: FORMAL_CHECK_PASSED: total=5192; control: assertion failure (exit 1).');
  assert.match(pr.details, /^Code replay: NOT REPLAYED — The approved prompt area has no original scenario vectors\./m);
  assert.doesNotMatch(pr.details, /Code replay: PASS|Manifest SHA256: unavailable/);
});

test('FORMAL-REAL3: a Story without Rules to check: the formal check is "not needed" and does not hold the PR', t => {
  const pr = formalPublication(t, { rules: false });
  assert.equal(pr.row, '| Formal check | not needed (no Rules to check in the Story) | — |');
  assert.equal(pr.status, '⛔ Blocked: replay evidence is incomplete');
  assert.equal(pr.header, 'Formal check: not needed (no Rules to check in the Story).');
});

const MISSING_FORMAL = 'missing — evidence not recorded: replay-evidence.json is missing in the run folder. Repair: write the formal block per docs/replay-evidence.md, then run pdd workflow done formal again.';
const UNKNOWN_RULES = 'pdd found no Story file of this run, so the formal check counts as needed. When the Story has no Rules to check, name its path (user_stories/NAME.md) in the formal step summary.';
test('FORMAL-REAL4: a Story in a subfolder of user_stories counts: with Rules to check it holds the PR, without them it is "not needed"', t => {
  let pr = formalPublication(t, { rules: true, story: 'user_stories/journeys/value.md' });
  assert.equal(pr.row, `| Formal check | ${MISSING_FORMAL} | — |`, 'pdd read the Story, so the row has no "no Story file" note.');
  assert.equal(pr.status, '⛔ Blocked: replay evidence is incomplete; formal check missing');
  pr = formalPublication(t, { rules: false, story: 'user_stories/journeys/value.md' });
  assert.equal(pr.row, '| Formal check | not needed (no Rules to check in the Story) | — |');
  assert.equal(pr.status, '⛔ Blocked: replay evidence is incomplete');
});

test('FORMAL-REAL5: a run with no Story file: Rules to check are unknown, so the formal check counts as needed and the row says why', t => {
  const pr = formalPublication(t, { rules: false, story: null });
  assert.equal(pr.row, `| Formal check | ${MISSING_FORMAL} ${UNKNOWN_RULES} | — |`);
  assert.equal(pr.header, `Formal check (agent reported): ${MISSING_FORMAL} ${UNKNOWN_RULES}`);
  assert.equal(pr.status, '⛔ Blocked: replay evidence is incomplete; formal check missing');
  assert.doesNotMatch(pr.details, /not needed/);
});

test('FORMAL-REAL6: done formal sees a Story that only its own summary names', t => {
  const early = f => { delete f.run.done.review; };
  // The Story with Rules to check was committed before the run's base, so the run does not change it.
  let pr = formalPublication(t, { rules: true, before: true, prepare: early, summary: 'Formal: proved the rules of user_stories/value.md' });
  assert.equal(pr.done, `Formal check (agent reported): ${MISSING_FORMAL}`, pr.out.message);
  pr = formalPublication(t, { rules: true, before: true, prepare: early, summary: 'Formal: proved the rules' });
  assert.equal(pr.done, `Formal check (agent reported): ${MISSING_FORMAL} ${UNKNOWN_RULES}`, 'No Story named and none changed: unknown.');
});

// #3029 M3: resolve pre-existing named Stories through stepDone and the real publication path.
// Git pushes stay in the fixture's local bare repository; gh is the fixture's local command fake.
const NAMED_NOT_RUN = { result: 'not_run', scope: 'Named Story rules', reason: 'No formal execution', control_outcome: 'not_run' };
function namedStoryPublication(t, { story, rules, reference = story, vectors = false, invalid = false, prefixRules = false }) {
  const f = fixture(t, { opted: true });
  mkdirSync(join(f.root, dirname(story)), { recursive: true });
  writeFileSync(join(f.root, story), VALUE_STORY.replace('two,', '3029,') + (rules ? '\n## Rules to check\n\nWrong: a value other than two.\n' : ''));
  if (prefixRules) writeFileSync(join(f.root, 'user_stories/value.md'), VALUE_STORY + '\n## Rules to check\n\nWrong: another value.\n');
  // Neither named Story is in the changed-file list or the scenario anchor.
  if (vectors) writeFileSync(join(f.root, 'user_stories/first.md'), VALUE_STORY);
  const unsafe = ['user_stories/absolute.md', 'user_stories/traversal.md', 'user_stories/control\u0001.md'];
  if (invalid) for (const path of unsafe) writeFileSync(join(f.root, path), VALUE_STORY.replace('two,', '9999,') + '\n## Rules to check\n\nWrong: any other value.\n');
  f.git('add', '.'); f.git('commit', '-qm', 'Existing named Stories'); f.run.baseSha = f.git('rev-parse', 'HEAD');
  let path, vector;
  if (vectors) {
    mkdirSync(join(f.root, 'tests'));
    writeFileSync(join(f.root, 'user_stories/current.md'), VALUE_STORY);
    path = 'tests/current.json';
    vector = { schema_version: 'prompt-runtime.program-scenario.v1', story_path: 'user_stories/current.md',
      steps: [{ step_id: 'value', entry_path: 'prompts/value.prompt.md', operation: 'value',
        checks: [{ criterion_id: 'AC1', target: 'result', path: '/value', op: 'equals', value: 2 }] }] };
    writeFileSync(join(f.root, path), JSON.stringify(vector)); f.git('add', '.'); f.git('commit', '-qm', 'Current Story and vectors');
  }
  f.machine(f.git('rev-parse', 'HEAD'));
  f.run.replayBaseline = pinReplayVectors(f.root, vectors ? [path] : []); f.save();
  const manifest = { schema_version: 'pdd.replay-evidence.v1', run_id: f.run.runId,
    source: { kind: 'git-content-v1', sha256: sourceFingerprint(f.root) }, vectors: [], checks: [], operations: [],
    counts: { total: 0, pass: 0, fail: 0, blocked: 0, not_replayed: 0 }, formal: NAMED_NOT_RUN };
  if (vectors) Object.assign(manifest, {
    vectors: [{ path, sha256: f.run.replayBaseline.vectors[0].sha256 }],
    checks: [{ vector: path, step_id: 'value', check_index: 0, entry_path: 'prompts/value.prompt.md', operation: 'value', criterion_id: 'AC1', target: 'result', path: '/value', op: 'equals', outcome: 'pass' }],
    operations: [{ vector: path, step_id: 'value', entry_path: 'prompts/value.prompt.md', operation: 'value', executed: true, outcome: 'returned', boundary: { kind: 'function', name: 'value' }, command: 'node --test test/value.test.mjs', exit_code: 0 }],
    counts: { total: 1, pass: 1, fail: 0, blocked: 0, not_replayed: 0 },
    mutation: { kind: 'semantic', description: 'Return a wrong value', command: 'node --test test/value.test.mjs --mutant', exit_code: 1, outcome: 'assertion_failure', failed_checks: [{ vector: path, step_id: 'value', check_index: 0 }] }
  });
  writeFileSync(join(f.runDir, 'replay-evidence.json'), JSON.stringify(manifest));
  const badReferences = invalid ? `; /tmp/${unsafe[0]}; ../${unsafe[1]}; ${unsafe[2]}` : '';
  const out = f.invoke(`Review: no must-fix; ${vectors ? 'Story: user_stories/first.md; ' : ''}Story: ${reference}${badReferences}`);
  assert.equal(out.exitCode, 0, out.message);
  const saved = JSON.parse(readFileSync(join(f.runDir, 'status.json')));
  return { facts: saved.pr.find(pr => pr.stage === 'code').readable.facts, replay: saved.replayEvidence,
    visible: f.data().prs[0].body.split(DETAILS_OPEN)[0] };
}

for (const [story, reference] of [
  ['user_stories/règle.md', 'user_stories/règle.md'],
  ['user_stories/dot règle.md', './user_stories/dot règle.md'],
  ['user_stories/a name.md', '`user_stories/a name.md`'],
  ['user_stories/café.md', '[Story](user_stories/café.md)']
]) {
  test(`FORMAL-NAMED: Rules in ${story} block publication even with passing replay`, t => {
    const { facts, replay, visible } = namedStoryPublication(t, { story, reference, rules: true, vectors: true });
    assert.ok(facts.stories.some(text => text.includes('3029')), 'The named Story must be resolved before publication.');
    assert.equal(facts.records.rulesToCheck, true);
    assert.equal(replay.outcome, 'pass');
    assert.equal(replay.formal.result, 'not_run');
    assert.match(visible.split('\n')[0], /^⛔/);
    // Supply green facts locally to test both merge routes; no real CI or checker run is claimed.
    facts.records.ci = 'passing';
    assert.match(prStatus(facts), /^⛔/);
    facts.mode = 'auto'; facts.records.checker = { verdict: 'PASS' };
    assert.match(prStatus(facts), /^⛔/);
  });
  test(`FORMAL-NAMED: no Rules in ${story} avoids a false formal block and rejects unsafe references`, t => {
    const { facts, replay } = namedStoryPublication(t, { story, reference: `"${story}"`, rules: false });
    assert.ok(facts.stories.some(text => text.includes('3029')), 'The named Story must be resolved before publication.');
    assert.ok(facts.stories.every(text => !text.includes('9999')), 'Unsafe references must not select their relative suffix.');
    assert.equal(facts.records.rulesToCheck, false);
    assert.equal(replay.outcome, 'not_replayed');
    assert.equal(replay.formal.result, 'not_run');
    facts.records.ci = 'passing';
    const withFormal = prStatus(facts);
    facts.records.formalStep = false;
    assert.equal(withFormal, prStatus(facts), 'The formal step must add no block for resolved no-Rules Stories.');
    const unsafe = namedStoryPublication(t, { story, reference, rules: false, invalid: true });
    assert.ok(unsafe.facts.stories.every(text => !text.includes('9999')));
    assert.equal(unsafe.facts.records.rulesToCheck, false, 'Unsafe references must not add Rules.');
  });
}

test('READABLE-CHECKS: an existing code PR update reads CI and the checker verdict for the pushed head', t => {
  const verdict = (head, word = 'PASS', author = 'OWNER') => ({ author_association: author, html_url: 'https://github.com/example/project/pull/23#issuecomment-1', created_at: '2026-11-06T12:00:00Z', body: `Checked.\n\n\`\`\`json\n${JSON.stringify({ verdict: word, head, risk: 2 })}\n\`\`\`` });
  for (const trusted of [false, true]) {
    // The old-code proof is for the pushed head: a stale proof never gives ✅ (#3042 M4).
    const f = fixture(t, { existing: true }); const next = f.change(); f.machine(next);
    const prs = f.data().prs; prs[0].statusCheckRollup = [{ conclusion: 'SUCCESS' }];
    f.configure({ prs, comments: trusted ? [verdict(next)] : [verdict(f.head), verdict(next, 'FAIL', 'NONE')] });
    const out = f.invoke('Review: no must-fix'); assert.equal(out.exitCode, 0, out.message);
    const [visible] = f.data().prs[0].body.split(DETAILS_OPEN);
    assert.match(f.data().events[0].body, /^⏳ Waiting for the source to be published · Updated [\d-]+ [\d:]+ UTC$/m, 'The description before the push says it is pending.');
    assert.match(visible, /\| Full test suite \(CI\) on this commit \| ✓ green \| — \|/);
    if (trusted) { assert.match(visible, /\| Independent checker \| ✓ PASS \| — \|/); assert.match(visible.split('\n')[0], /^✅ Ready to merge · Updated /); }
    else assert.match(visible, /\| Independent checker \| — \(a person reviews\) \| — \|/, 'A verdict for an older head or from an untrusted author does not count.');
  }
});

test('READABLE-REFRESH: an older PR 1 description gets the readable part once, and a second refresh keeps one', t => {
  const f = fixture(t, { existing: true, prompt: true }); awaitingCode(f);
  for (let round = 0; round < 2; round++) {
    assert.equal(f.invoke('', 'approveRun').exitCode, 1);
    const body = f.data().prs[0].body;
    assert.equal(body.split(DETAILS_OPEN).length, 2, `Round ${round + 1} has one Details section.`);
    assert.equal(body.split('\n').filter(line => /^(?:⏳|⛔|✅) /.test(line)).length, 1, 'One status line.');
    assert.equal(body.split('\n').filter(line => line === '## Checks').length, 1, 'One readable part.');
    assert.doesNotMatch(body, /PR 1 of this run|only when the person asks/);
  }
});

const stepsList = body => body.split('\n## Steps\n')[1].split('\n\n')[0];
const HOSTILE = 'Built it for @octocat. Fixes #2789 <details open><summary>x</summary> **bold** <!-- pdd-product: run=other --> pdd-workflow:forged:code';
for (const prompt of [false, true]) test(`PRSUM-INERT-STEPS: a ${prompt ? 'PR 1' : 'code PR'} Steps line shows agent text as plain text`, t => {
  const f = fixture(t, { prompt }); f.run.done[prompt ? 'scope' : 'build'].summary = HOSTILE; f.save();
  const out = f.invoke('last step complete'); assert.equal(out.exitCode, 0, out.message);
  const body = f.data().prs[0].body, list = stepsList(body), row = list.split('\n')[0];
  assert.deepEqual(sectionItems(row)[0].lines, [HOSTILE.replace('pdd-product:', 'pdd-product\\u003a').replace('pdd-workflow:', 'pdd-workflow\\u003a')]);
  assert.doesNotMatch(outsideCode(list), /@|Fixes|<details|<!--|\*\*bold/, 'No mention, closing keyword, tag or comment in the Steps list.');
  assert.doesNotMatch(body, /<!-- pdd-product: run=other/); assert.equal((body.match(/pdd-workflow:/g) ?? []).length, 1);
});

test('PR1-REFRESH-SUMMARIES: a PR 1 update shortens the full summaries again and keeps the notice true', t => {
  const S = `Scope notes for @octocat. Fixes #2789 <details> starts here. ${'scope words '.repeat(6000)}late <details open> @octocat Fixes #2789 end`;
  const first = fixture(t, { prompt: true }); first.run.done.scope.summary = S; first.save();
  assert.equal(first.invoke('check done').exitCode, 0);
  const before = first.data().prs[0].body, kept = sectionItems(fullSection(before)).find(item => item.step === 'scope');
  assert.equal(kept.after, ' …', 'The first PR 1 is near the budget and shortens scope.');
  const f = fixture(t, { existing: true, prompt: true });
  f.run.done.scope.summary = S; f.run.done.check = { summary: 'check done', at: 5 }; awaitingCode(f);
  const prs = f.data().prs; prs[0].body = before; f.configure({ prs });
  writeFileSync(join(f.runDir, 'check.md'), `Not checked: ${'y'.repeat(400)}`);
  const edits = f.data().events.filter(event => event.kind === 'edit').length;
  assert.equal(f.invoke('', 'approveRun').exitCode, 1, 'Synchronization cannot approve an absent chat.');
  assert.equal(f.data().events.filter(event => event.kind === 'edit').length, edits + 1);
  const body = f.data().prs[0].body, items = sectionItems(fullSection(body)), scope = items.find(item => item.step === 'scope');
  assert.ok([...body].length <= 60000, `The whole description has ${[...body].length} characters.`);
  assert.match(pddPart(body), /^Agent note — not checked by pdd: Not checked: `y{400}`$/m); assert.equal(stepsList(body), stepsList(before), 'The Steps list is not cut.');
  assert.deepEqual(items.find(item => item.step === 'check').lines, ['check done']);
  assert.equal(scope.after, ' …'); assert.ok(S.startsWith(scope.lines[0]) && scope.lines[0].length < kept.lines[0].length, 'The block is shortened first.');
  const notice = body.split('\n').find(row => /step summar(?:y was|ies were) shortened to fit the PR size limit/.test(row)), count = /scope \(([\d,]+) characters left out\)/.exec(notice ?? '');
  assert.ok(count && body.indexOf(notice) < body.indexOf(FULL), `One true notice above the block: ${notice}`);
  assert.equal([...scope.lines[0]].length + Number(count[1].replaceAll(',', '')), [...S].length, 'The notice counts what this description leaves out.');
  assert.doesNotMatch(body, /not shown here/); assert.doesNotMatch(outsideCode(body), /@octocat|Fixes #2789|<details open/);
  assert.equal(outsideCode(pddPart(body)).split('<details').length - 1, 1); assert.equal((body.match(/pdd-workflow:/g) ?? []).length, 1);
});

test('2874: a PR 1 refresh reserves all protected summaries before fitting large top evidence', t => {
  const protectedLines = Array.from({ length: 120 }, (_, index) => `Limitation: ${String(index).padStart(3, '0')} ${'e'.repeat(74)}`);
  const summary = `${'ordinary notes '.repeat(6000).trim()}\n${protectedLines.join('\n')}`;
  const note = `Not checked: ${'y'.repeat(50000)}`;
  const first = fixture(t, { prompt: true }); first.run.done.scope.summary = summary; first.save();
  assert.equal(first.invoke('check done').exitCode, 0);
  const before = first.data().prs[0].body;
  const creation = fixture(t, { prompt: true }); creation.run.done.scope.summary = summary; creation.save();
  writeFileSync(join(creation.runDir, 'check.md'), note);
  assert.equal(creation.invoke('check done').exitCode, 0, 'The same inputs fit at initial publication.');
  const f = fixture(t, { existing: true, prompt: true });
  f.run.done.scope.summary = summary; f.run.done.check = { summary: 'check done', at: 5 }; awaitingCode(f);
  const prs = f.data().prs; prs[0].body = before; f.configure({ prs });
  writeFileSync(join(f.runDir, 'check.md'), note);
  const edits = f.data().events.length;
  const out = f.invoke('', 'approveRun');
  assert.doesNotMatch(out.message, /workflow_pr_body_too_large/);
  assert.equal(f.data().events.length, edits + 1, 'Fresh evidence refreshes the PR when protected summaries fit.');
  for (const body of [creation.data().prs[0].body, f.data().prs[0].body]) {
    const scope = sectionItems(fullSection(body)).find(item => item.step === 'scope');
    for (const line of protectedLines) assert.ok(scope.lines.includes(line), 'Every protected line stays whole.');
    assert.match(body, /Evidence omitted:/, 'Oversized top evidence uses the existing omission policy.');
    assert.ok([...body].length <= 60000, `The whole description has ${[...body].length} characters.`);
  }
  const body = f.data().prs[0].body;
  assert.equal(stepsList(body), stepsList(before), 'Refreshing does not cut the Steps list.');
  const scope = sectionItems(fullSection(body)).find(item => item.step === 'scope');
  const notice = body.split('\n').find(row => /step summary was shortened/.test(row));
  const count = /scope \(([\d,]+) characters left out\)/.exec(notice ?? '');
  assert.ok(count, 'The refreshed omission notice identifies the shortened step.');
  const retained = scope.lines.filter(line => line !== '…').reduce((sum, line) => sum + [...line].length, 0) + protectedLines.length - 1;
  assert.equal(retained + Number(count[1].replaceAll(',', '')), [...summary].length, 'The notice counts omitted characters, excluding inserted gap markers.');
});

test('2874: a PR 1 refresh preserves late evidence and refuses an oversized replacement', t => {
  const line = 'Limitation: upstream failure remains DEFERRED; https://github.com/example/upstream/issues/476';
  const summary = `${'ordinary notes '.repeat(6000).trim()}\n${line}`;
  const first = fixture(t, { prompt: true }); first.run.done.scope.summary = summary; first.save();
  assert.equal(first.invoke('check done').exitCode, 0);
  const before = first.data().prs[0].body;
  const f = fixture(t, { existing: true, prompt: true });
  f.run.done.scope.summary = summary; f.run.done.check = { summary: 'check done', at: 5 }; awaitingCode(f);
  const prs = f.data().prs; prs[0].body = before; f.configure({ prs });
  writeFileSync(join(f.runDir, 'check.md'), `Not checked: ${'y'.repeat(400)}`);
  const edits = f.data().events.length;
  f.invoke('', 'approveRun');
  assert.equal(f.data().events.length, edits + 1, 'Fresh evidence refreshes the PR.');
  const body = f.data().prs[0].body;
  assert.ok(sectionItems(fullSection(body)).find(item => item.step === 'scope').lines.includes(line));
  assert.ok([...body].length <= 60000); assert.doesNotMatch(body, /full summaries in the run folder/);
  assert.equal((body.match(/step summary was shortened/g) ?? []).length, 1, 'The old omission notice is replaced.');
  f.run.done.scope.summary = `Limitation: ${'upstream deferred '.repeat(5000)}`; f.save();
  const written = f.data().events.length;
  const out = f.invoke('', 'approveRun');
  assert.match(out.message, /workflow_pr_body_too_large/);
  assert.match(out.message, /shorten the notes while retaining outcome, limitation and reference evidence/i);
  assert.equal(f.data().events.length, written, 'The oversized replacement is never written.');
  assert.equal(f.data().prs[0].body, body, 'The previous PR description remains available.');
});

test('PR1-REFRESH-CODE-TAGS: a tag inside a code span does not fold the rest of a long PR 1 description', t => {
  const f = fixture(t, { existing: true, prompt: true }); awaitingCode(f);
  const marker = `<!-- pdd-workflow:${f.run.runId}:prompt-pr -->`, row = '- **scope**: `<details> notes`';
  const prs = f.data().prs;
  prs[0].body = `Part of #17\n\nMade with \`pdd workflow run small-change\`.\n\n## Steps\n${row}\n\n${'ordinary reviewer prose\n'.repeat(2600)}end\n${marker}\n`; f.configure({ prs });
  assert.equal(f.invoke('', 'approveRun').exitCode, 1);
  const body = f.data().prs[0].body;
  assert.ok([...body].length <= 60000); assert.ok(body.split('\n').includes(row.replace(': ', ': Agent note — not checked by pdd: ')), 'The Steps payload stays under its unchecked label.');
  assert.match(body, /It was shortened to fit/); assert.doesNotMatch(body, /not shown here/);
});

// #2596 expectations derive from the approved current-head Story. These exercise
// the CLI-facing publication boundary, real local Git and the fake gh transport.
const currentRuntime = 'Prompt tests (release): ✓ 1 of 1 criteria · 2/2 checks · 1 AI call';
async function runtimeReceipt(f) {
  const { sourceFingerprint } = await import('../src/workflow-replay.mjs');
  f.run.evidence = [{ summary: currentRuntime, at: 10, source: {kind:'git-content-v1',sha256:sourceFingerprint(f.root)} }];
  f.save();
}
test('#2596 publication checks only compatible receipts and labels every prose surface', async t => {
  const f = fixture(t); await runtimeReceipt(f);
  const prose = 'Full npm test: 665/665 passed';
  f.run.done.verify.summary = `verified\n${currentRuntime}\n${prose}`; f.save();
  writeFileSync(join(f.runDir,'verify.md'), `# Verify\n${currentRuntime}\n${prose}\n## Vectors\n| case | result |\n| A | pass |`);
  assert.equal(f.invoke(`Not checked: ${prose}`).exitCode, 0);
  const body = f.data().prs[0].body;
  assert.match(body, new RegExp(currentRuntime.replace(/[.*+?^${}()|[\]\\]/g,'\\$&')));
  assert.match(body, /Native tests: unknown/);
  assert.match(body, /- \*\*verify\*\*: Agent note — not checked by pdd:/);
  assert.match(body, /## Verify\n\nAgent note — not checked by pdd:/);
  assert.equal((body.match(/^# Verify$/gm) ?? []).length,0);
  assert.match(body, /Saved runtime receipt \(unverified in this agent note\): Prompt tests/);
  assert.match(body, /Agent note — not checked by pdd: Not checked: `Full npm test: 665\/665 passed`/);
});
for (const failure of ['pending','final']) test(`#2596 ${failure} description failure keeps current-success claims cleared before push`, async t => {
  const f = fixture(t, {existing:true}); await runtimeReceipt(f); f.machine(); const next = f.change();
  f.configure({failEdit:failure === 'pending' ? 1 : 2});
  const out = f.invoke('Not checked: live CI'); assert.equal(out.exitCode, 1, out.message);
  const events = f.data().events;
  assert.doesNotMatch(events[0].body, /^Prompt tests.*✓|Old-code proof: ✓|Native tests.*\d+\/\d+/m);
  assert.match(events[0].body, /Native tests: publication-pending/);
  assert.equal(events[0].remote, f.head);
  if (failure === 'pending') assert.equal(f.git('ls-remote','origin','refs/heads/topic').split('\t')[0], f.head);
  else { assert.equal(events[1].remote, next); assert.equal(f.data().prs.at(-1).body,events[0].body); assert.match(out.message,/stays publication-pending/); }
});
for (const proofState of ['current','stale','unreadable','missing']) test(`#2596 native counts come from actual ${proofState} machine proof output`, t => {
  const f = fixture(t);
  if (proofState !== 'missing') {
    f.machine(); const path=join(f.runDir,'old-code-proof.json'), record=JSON.parse(readFileSync(path));
    record.head.stdoutTail=['# tests 8','# pass 7','# fail 1','# cancelled 0','# skipped 0','# todo 0'];
    record.head.exitCode=1; record.outcome='head-fails';
    if (proofState === 'stale') record.headSha='a'.repeat(40);
    writeFileSync(path,proofState === 'unreadable' ? '{' : JSON.stringify(record));
  }
  assert.equal(f.invoke('Proof (defect fixed): Full npm test: 665/665 passed').exitCode,0);
  const body=f.data().prs[0].body;
  if(proofState==='current') assert.match(body,/Native tests \(current old-code proof, new-code output\): 7\/8 passed; 1 failed\./);
  else {assert.match(body,/Native tests: unknown/);assert.doesNotMatch(body,/Native tests.*(?:7\/8|665\/665)/);}
});

for (const failure of ['pending','final']) test(`#2596 PR1 approval synchronization retains pending custody on ${failure} edit failure`, async t => {
  const f=fixture(t,{existing:true,prompt:true}); awaitingCode(f); await runtimeReceipt(f);
  const prs=f.data().prs;
  prs[0].body=`${currentRuntime}\n\nPart of #17\n\nPR 1 of this run: the prompt, Story and test cases. The code comes in PR 2 only when the person asks for it.\n\nReviewer prose.\n<!-- pdd-workflow:${f.run.runId}:prompt-pr -->\n`;
  f.configure({prs,failEdit:failure==='pending'?1:2});
  const next=f.change(), out=f.invoke('','approveRun'); assert.equal(out.exitCode,1);
  const events=f.data().events;
  assert.doesNotMatch(events[0].body,/^Prompt tests.*✓/m);
  assert.equal(events[0].remote,f.head);
  if(failure==='pending') {assert.match(out.message,/No source was pushed/);assert.equal(f.git('ls-remote','origin','refs/heads/topic').split('\t')[0],f.head);}
  else {assert.equal(events[1].remote,next);assert.equal(f.data().prs[0].body,events[0].body);assert.match(out.message,/stays publication-pending/);}
});

test('#2596 PR1 refresh removes a deleted runtime scenario from its contents description', async t => {
  const f=fixture(t,{existing:true,prompt:true}); awaitingCode(f);
  mkdirSync(join(f.root,'tests'));
  writeFileSync(join(f.root,'tests/release.json'),JSON.stringify({schema_version:'prompt-runtime.program-scenario.v1',story_path:'user_stories/release.md',criteria:[],steps:[]}));
  f.git('add','.');f.git('commit','-qm','add scenario');
  assert.equal(f.invoke(currentRuntime).exitCode,0);
  // #3042: the readable Summary's "This PR" line (from the current Git diff) replaced the old "PR 1 of this run: …" sentence.
  assert.match(f.data().prs[0].body,/^- \*\*This PR:\*\* [^\n]*1 test file/m);
  f.git('rm','tests/release.json');f.git('commit','-qm','remove scenario');
  assert.equal(f.invoke('refreshed').exitCode,0);
  const body=f.data().prs[0].body;
  assert.match(body,/^- \*\*This PR:\*\* /m);
  assert.doesNotMatch(body,/^- \*\*This PR:\*\* [^\n]*test file|PR 1 of this run|^Prompt tests.*✓/m);
});

for(const change of ['identical','prompt','dependency','deleted']) test(`#2596 selected-source receipt publication after ${change} content`, async t=>{
  // Authored prompt changes publish through PR 1; PR 2 forbids prompt edits.
  const f=fixture(t,{prompt:true});
  for(const folder of ['prompts','tests','user_stories']) cpSync(join(packageRoot,'test/fixtures/harbor',folder),join(f.root,folder),{recursive:true});
  const prompt=join(f.root,'prompts/place_order.prompt.md');
  writeFileSync(prompt,readFileSync(prompt,'utf8').replace('## Dependencies\n\nNone.', '## Dependencies\n\n- [Prices](prices.md): required runtime context.'));
  writeFileSync(join(f.root,'prompts/prices.md'),'Synthetic selected dependency.\n');
  f.git('add','.');f.git('commit','-qm','selected runtime corpus');
  const {captureSource}=await import('../src/runtime-seam.mjs');
  const tests=['tests/place-order.json'];
  const source=captureSource(f.root,{tests,appMap:null});
  f.run.evidence=[{at:10,summary:currentRuntime.replace('(release)', '(place-order)'),source:{kind:'runtime-capture-v1',tests,sha256:source.sha256}}];f.save();
  if(change==='identical')f.git('commit','--allow-empty','-qm','same selected bytes');
  if(change==='prompt')writeFileSync(prompt,readFileSync(prompt,'utf8')+'\nChanged prompt.\n');
  if(change==='dependency')writeFileSync(join(f.root,'prompts/prices.md'),'Changed required dependency.\n');
  if(change==='deleted')f.git('rm','tests/place-order.json');
  assert.equal(f.invoke('verified publication').exitCode,0);
  const body=f.data().prs[0].body;
  if(change==='identical')assert.match(body,/^Prompt tests \(place-order\): ✓ 1 of 1 criteria · 2\/2 checks · 1 AI call$/m);
  else assert.doesNotMatch(body,/^Prompt tests.*✓/m);
});

// #3042 review (repair 1): the real publication and status paths, with real Git and a fake gh.
const NOT_FIXED_TOP = 'Not fixed yet: this helps find the cause. The issue stays open.';
// PR 1 open on GitHub with the given checks; the code PR is stacked on PR 1's branch (the reviewer's real run).
function stackedOnPr1(t, { checks = [{ conclusion: 'FAILURE' }], state = 'OPEN' } = {}) {
  const f = fixture(t); f.machine();
  const gh = join(f.base, 'bin', 'gh');
  writeFileSync(gh, readFileSync(gh, 'utf8').replace("p=>!a.includes('--head')||p.headRefName===flag('--head')", "p=>(!a.includes('--head')||p.headRefName===flag('--head'))&&(!a.includes('--search')||String(p.body).includes(flag('--search').split('\"')[1]))"));
  f.git('push', '-q', 'origin', 'main:refs/heads/prompt-topic');
  f.run.prBase = 'prompt-topic'; f.run.workflow = 'bug'; f.save();
  f.configure({ prs: [{ number: 22, url: url(22), state, headRefName: 'prompt-topic', baseRefName: 'main', body: 'x', statusCheckRollup: checks }] });
  writeFileSync(join(f.runDir, 'review.md'), 'Review: no must-fix\n');
  return f;
}
const codePr = f => f.data().prs.find(pr => pr.number === 23);
const liveKeyword = () => /\b(?:close[sd]?|fix(?:es|ed)?|resolve[sd]?)[\s:*_~]*(?:[\w.-]+\/[\w.-]+)?#\d+/gi;
const SUMMARY = 'Title: the value is two\nProblem: the value is one.\nCause: an old constant.\nFix: Fixes: #5 by setting two.\nResult: all good.';

test('RED-PAIR: a new code PR stacked on a red PR 1 says that it also merges PR 1, and never "merge it first"', t => {
  for (const [checks, state, line, waits, detail] of [
    [[{ conclusion: 'FAILURE' }], 'OPEN', 'This PR also merges PR 1 (#22). Do not merge PR 1 alone.', null, "It is stacked on PR 1's branch `prompt-topic`. PR 1's CI fails, so this PR also merges PR 1. Do not merge PR 1 alone."],
    [[{ conclusion: 'SUCCESS' }], 'OPEN', 'Builds on PR 1 (#22): merge it first.', 'PR 1 (#22)', "It is stacked on PR 1's branch `prompt-topic`: merge PR 1 first."],
    [[{ status: 'IN_PROGRESS' }], 'OPEN', 'Builds on PR 1 (#22).', 'the CI of PR 1 (#22)', "It is stacked on PR 1's branch `prompt-topic`. PR 1's CI has no result yet."],
    [[{ conclusion: 'SUCCESS' }], 'MERGED', null, null, "It was stacked on PR 1's branch `prompt-topic`; PR 1 is merged."],
  ]) {
    const f = stackedOnPr1(t, { checks, state });
    const out = f.invoke(SUMMARY); assert.equal(out.exitCode, 0, out.message);
    const pr = codePr(f), [visible] = pr.body.split(DETAILS_OPEN), status = visible.split('\n')[0];
    assert.equal(pr.baseRefName, 'prompt-topic');
    if (line) assert.ok(visible.trimEnd().endsWith(`Closes #17.\n\n${line}`), visible); else assert.doesNotMatch(visible, /PR 1/);
    if (waits) assert.ok(status.includes(waits), status); else assert.doesNotMatch(status, /PR 1/, status);
    assert.ok(pddPart(pr.body).split('\n').includes(detail), pddPart(pr.body));
    if (checks[0].conclusion === 'FAILURE') assert.doesNotMatch(pr.body, /merge it first|merge PR 1 first/, 'A red PR 1 is never merged first.');
  }
});

test('CLOSING-REAL: agent words with a colon keyword close nothing; only pdd\'s own Closes line can close the issue', t => {
  const f = stackedOnPr1(t);
  assert.equal(f.invoke(SUMMARY).exitCode, 0);
  const [visible] = codePr(f).body.split(DETAILS_OPEN);
  assert.match(visible, /^- \*\*Fix\u200b:\*\* Fixes\u200b: #5 by setting two\.$/m);
  assert.deepEqual(visible.match(liveKeyword()), ['Closes #17']);
});

test('NOT-FIXED-REAL: a warning-light code PR shows "Not fixed yet" under its status line and is never ready', t => {
  const f = fixture(t); f.machine();
  const prs = f.data().prs; f.configure({ prs, comments: [] });
  const out = f.invoke('Not fixed yet: this helps find the cause\nReview: no must-fix'); assert.equal(out.exitCode, 0, out.message);
  const [visible] = f.data().prs[0].body.split(DETAILS_OPEN), lines = visible.split('\n');
  assert.match(lines[0], /^⛔ Not fixed yet · Updated /); assert.equal(lines[2], NOT_FIXED_TOP);
  assert.match(visible, /\*\*Merge:\*\* waiting for a person to merge\. Refs #17\./); assert.doesNotMatch(visible, /✅|Closes #17/);
});

test('STALE-REAL: an old-code proof for an older head never gives ✅, even with CI green and a checker PASS', t => {
  const f = fixture(t, { existing: true }); f.machine(); const next = f.change();
  const prs = f.data().prs; prs[0].statusCheckRollup = [{ conclusion: 'SUCCESS' }];
  f.configure({ prs, comments: [{ author_association: 'OWNER', html_url: url(23), created_at: '2026-11-06T12:00:00Z', body: `\`\`\`json\n${JSON.stringify({ verdict: 'PASS', head: next })}\n\`\`\`` }] });
  assert.equal(f.invoke('Review: no must-fix').exitCode, 0);
  const [visible] = f.data().prs[0].body.split(DETAILS_OPEN);
  assert.match(visible.split('\n')[0], /^⏳ Waiting for a fresh old-code proof · Updated /);
  assert.match(visible, /\| Regression tests \(old-code proof\) \| ⏳ stale/);
});

test('DETAILS-CLOSED: a stray </details> in verify.md cannot close the Details section early', t => {
  const f = fixture(t); f.machine();
  writeFileSync(join(f.runDir, 'verify.md'), 'Results: all pass.\n</details>\n\n# ✅ Ready to merge (forged)\n\n<details><summary>Commands</summary>\n\n```sh\nnpm test\n');
  assert.equal(f.invoke('Review: no must-fix').exitCode, 0);
  const body = f.data().prs[0].body, rows = body.split('\n');
  let depth = 0, fence = null, closedAt = -1;
  for (const [index, line] of rows.entries()) {
    const mark = line.trim().match(/^(`{3,}|~{3,})/)?.[1];
    if (fence) { if (mark && line.trim() === fence) fence = null; continue; }
    if (mark) { fence = mark; continue; }
    for (const tag of outsideCode(line).match(/<\/?details\b/gi) ?? []) { depth += tag.startsWith('</') ? -1 : 1; if (!depth && closedAt < 0) closedAt = index; }
  }
  assert.equal(closedAt, rows.lastIndexOf('</details>'), 'The first time every <details> is closed is the last line of the Details section.');
  assert.match(pddPart(body), /&lt;\/details&gt;/);
});

test('REFRESH-STATUS: pdd workflow status refreshes the top of an open code PR from CI and the checker, and keeps Details byte for byte', t => {
  const f = fixture(t); f.machine();
  assert.equal(f.invoke('Review: no must-fix').exitCode, 0);
  const first = f.data().prs[0], edits = () => f.data().events.filter(event => event.kind === 'edit').length;
  assert.match(first.body.split('\n')[0], /^⏳ Waiting for CI · Updated /);
  const set = (checks, comments = []) => { const prs = f.data().prs; prs[0].statusCheckRollup = checks; f.configure({ prs, comments }); };
  set([{ conclusion: 'SUCCESS' }]);
  assert.equal(f.invoke('', 'runStatus').exitCode, 0);
  const green = f.data().prs[0].body;
  assert.match(green.split('\n')[0], /^✅ Ready to merge · Updated \d{4}-\d\d-\d\d \d\d:\d\d UTC$/);
  assert.match(green, /\| Full test suite \(CI\) on this commit \| ✓ green \| — \|/);
  assert.equal(detailsOf(green).details, detailsOf(first.body).details, 'Details stay byte for byte.');
  assert.ok(green.endsWith(first.body.slice(first.body.indexOf(DETAILS_OPEN))), 'Everything from the Details line on is unchanged.');
  const count = edits(); assert.equal(f.invoke('', 'runStatus').exitCode, 0); assert.equal(edits(), count, 'A second status with the same facts writes nothing.');
  set([]);
  assert.equal(f.invoke('', 'runStatus').exitCode, 0);
  const none = f.data().prs[0].body;
  assert.match(none.split('\n')[0], /^⛔ Blocked: no CI checks configured · Updated /); assert.match(none, /\| no CI checks configured \| — \|/);
  const verdict = (word, author) => ({ author_association: author, html_url: url(23), created_at: `2026-11-06T12:0${word.length}:00Z`, body: `\`\`\`json\n${JSON.stringify({ verdict: word, head: first.headRefOid })}\n\`\`\`` });
  set([{ conclusion: 'SUCCESS' }], [verdict('FAIL', 'MEMBER'), verdict('PASS', 'OWNER')]);
  assert.equal(f.invoke('', 'runStatus').exitCode, 0);
  const split = f.data().prs[0].body;
  assert.match(split, /\| Independent checker \| ✗ split \(PASS and FAIL\) \| — \|/, 'Two verdicts on one head are a split, not the newest.');
  assert.match(split.split('\n')[0], /^⛔ Blocked: the checkers disagree on this head/);
});

test('REFRESH-RED-PAIR: status follows PR 1\'s CI and the retarget before the merge, in the top and in the Details line', t => {
  const f = stackedOnPr1(t, { checks: [{ status: 'IN_PROGRESS' }] });
  assert.equal(f.invoke(SUMMARY).exitCode, 0);
  const before = codePr(f).body;
  assert.ok(before.split(DETAILS_OPEN)[0].trimEnd().endsWith('Builds on PR 1 (#22).'));
  const update = change => { const prs = f.data().prs; change(prs); f.configure({ prs }); assert.equal(f.invoke('', 'runStatus').exitCode, 0); return codePr(f).body; };
  const red = update(prs => { prs[0].statusCheckRollup = [{ conclusion: 'FAILURE' }]; });
  assert.ok(red.split(DETAILS_OPEN)[0].trimEnd().endsWith('This PR also merges PR 1 (#22). Do not merge PR 1 alone.'));
  assert.ok(pddPart(red).split('\n').includes("It is stacked on PR 1's branch `prompt-topic`. PR 1's CI fails, so this PR also merges PR 1. Do not merge PR 1 alone."));
  assert.doesNotMatch(red, /merge it first|merge PR 1 first/);
  const retargeted = update(prs => { prs[0].statusCheckRollup = [{ conclusion: 'SUCCESS' }]; prs.find(pr => pr.number === 23).baseRefName = 'main'; });
  assert.ok(retargeted.split(DETAILS_OPEN)[0].trimEnd().endsWith('This PR also merges PR 1 (#22). Do not merge PR 1 alone.'), 'After the retarget the code PR carries PR 1.');
  assert.ok(pddPart(retargeted).split('\n').includes("It was stacked on PR 1's branch `prompt-topic` and now targets `main`. This PR also merges PR 1. Do not merge PR 1 alone."));
  const rest = body => { const rows = detailsOf(body).details.split('\n'); return rows.filter(row => !/^It (?:is|was) stacked on PR 1's branch /.test(row)).join('\n'); };
  assert.equal(rest(retargeted), rest(before), 'Only the merge-order line of Details changes.');
});

test('REFRESH-PR1: status refreshes PR 1\'s top too: its CI row, its status line and the link to PR 2', t => {
  const f = fixture(t, { prompt: true });
  assert.equal(f.invoke('check done').exitCode, 0);
  const first = f.data().prs[0];
  assert.match(first.body.split('\n')[0], /^⏳ Waiting for CI · Updated /);
  const saved = JSON.parse(readFileSync(join(f.runDir, 'status.json'), 'utf8'));
  saved.pr.push({ stage: 'code', number: 24, url: url(24), branch: 'topic-code', base: 'topic' }); writeFileSync(join(f.runDir, 'status.json'), JSON.stringify(saved));
  const prs = f.data().prs; prs[0].statusCheckRollup = [{ conclusion: 'SUCCESS' }]; f.configure({ prs });
  assert.equal(f.invoke('', 'runStatus').exitCode, 0);
  const body = f.data().prs[0].body, [visible] = body.split(DETAILS_OPEN);
  assert.match(visible.split('\n')[0], /^✅ Ready to merge · Updated /);
  assert.match(visible, /\| Full test suite \(CI\) \| ✓ green \|/);
  assert.match(visible, /^\*\*Next:\*\* PR 2 \(the code\): #24\. Part of #17\.$/m);
  assert.ok(body.endsWith(first.body.slice(first.body.indexOf(DETAILS_OPEN))), 'PR 1 keeps its Details byte for byte.');
});

// #3042 review 2: the title and verify.md close nothing; a refresh never writes over a newer publication; an unchanged
// refresh makes no GitHub call besides the status read.
const shell = value => `'${String(value).replaceAll("'", "'\\''")}'`;
// Would GitHub close an issue from this text? Code spans and fences are removed: GitHub reads no reference in code.
const liveOutsideCode = text => String(text).replace(/^(```|~~~)[^\n]*\n[\s\S]*?^\1\s*$/gm, '').replace(/(?<![`\\])(`+)(?!`)[\s\S]*?(?<!`)\1(?!`)/g, '').match(liveKeyword()) ?? [];
// The gh command with a shell step: `before` runs before the real gh, `after` after it (its output is kept and printed last).
const wrapGh = (f, { match, after = '', before = '' }) => {
  const real = join(f.base, 'bin', 'gh-real'), gh = join(f.base, 'bin', 'gh');
  writeFileSync(real, readFileSync(gh, 'utf8')); chmodSync(real, 0o755);
  writeFileSync(gh, `#!/bin/sh\nhit=; case "$*" in ${match}) if [ -z "$INNER" ] && [ -f ${shell(join(f.base, 'trigger'))} ]; then rm ${shell(join(f.base, 'trigger'))}; hit=1; fi;; esac\n`
    + `if [ -n "$hit" ]; then ${before || ':'}; fi\nout=$(${shell(real)} "$@") || exit $?\nif [ -n "$hit" ]; then ${after || ':'}; fi\nprintf '%s' "$out"\n`);
  chmodSync(gh, 0o755); writeFileSync(join(f.base, 'trigger'), '1');
};
const doneScript = (f, step, summary) => `import {stepDone} from ${JSON.stringify(join(packageRoot, 'src/workflow-runner.mjs'))};const r=await stepDone({ref:'17',step:${JSON.stringify(step)},summary:${JSON.stringify(summary)},cwd:${JSON.stringify(f.root)}},{stateDir:${JSON.stringify(join(f.base, 'pdd-state'))},isTTY:true,env:{HOME:${JSON.stringify(f.base)}},confirm:async()=>false});process.stdout.write(JSON.stringify(r));`;
const editsOf = f => f.data().events.filter(event => event.kind === 'edit');

test('CLOSING-TITLE-VERIFY: an agent title "Fixes #5 by padding" and verify.md "Fixes #8" / "Resolves: #9" close nothing', t => {
  const f = stackedOnPr1(t);
  writeFileSync(join(f.runDir, 'verify.md'), 'Results: all pass.\nThis Fixes #8 and Resolves: #9.\n\n```sh\ngit commit -m "fixes #5"\n```\n');
  const out = f.invoke('Title: Fixes #5 by padding\nProblem: closes: #6\nCause: c\nFix: Fixes: #7\nResult: ok'); assert.equal(out.exitCode, 0, out.message);
  const pr = codePr(f), [visible] = pr.body.split(DETAILS_OPEN), details = pr.body.slice(pr.body.indexOf(DETAILS_OPEN));
  assert.equal(pr.title, 'fix(bug): Fixes\u200b #5 by padding (#17 · part 2: fix)');
  assert.deepEqual(pr.title.match(liveKeyword()), null, 'The title closes nothing (GitHub puts it into the merge commit).');
  assert.ok(details.includes('This Fixes\u200b #8 and Resolves\u200b: #9.'), details);
  assert.ok(details.includes('```sh\ngit commit -m "fixes #5"\n```'), 'A fence in verify.md stays byte for byte.');
  assert.deepEqual(liveOutsideCode(visible), ['Closes #17']); assert.deepEqual(liveOutsideCode(details), ['Closes #17'], 'Only pdd\'s own Closes line closes an issue.');
});

test('RACE: a status refresh never writes over a description that a done published after the status read', t => {
  const f = fixture(t, { existing: true }); f.machine();
  assert.equal(f.invoke('Review: no must-fix').exitCode, 0);
  const b1 = f.data().prs[0].body, next = f.change(); f.machine(next);
  const prs = f.data().prs; prs[0].statusCheckRollup = [{ conclusion: 'SUCCESS' }]; f.configure({ prs });
  // The worker's done publishes right after GitHub answered the status read, so status holds the older description and head.
  writeFileSync(join(f.base, 'done.mjs'), doneScript(f, 'review', 'Review: no must-fix'));
  wrapGh(f, { match: '*comments*', after: `(cd ${shell(f.root)} && INNER=1 ${shell(process.execPath)} ${shell(join(f.base, 'done.mjs'))} > ${shell(join(f.base, 'done.out'))} 2> ${shell(join(f.base, 'done.err'))})` });
  const before = editsOf(f).length;
  assert.equal(f.invoke('', 'runStatus').exitCode, 0);
  assert.equal(JSON.parse(readFileSync(join(f.base, 'done.out'), 'utf8')).exitCode, 0, 'The worker\'s done published during the status.');
  const edits = editsOf(f), final = f.data().prs[0].body, inventory = body => pddPart(body).split('\n').find(line => line.startsWith('Test inventory commits:'));
  assert.equal(edits.length, before + 2, 'Only the done wrote (its pending and its final description); the status wrote nothing.');
  assert.equal(final, edits.at(-1).body);
  assert.ok(inventory(final).endsWith(`→ ${next.slice(0, 7)}.`), inventory(final)); assert.notEqual(inventory(final), inventory(b1));
  assert.equal(f.invoke('', 'runStatus').exitCode, 0);
  const after = f.data().prs[0].body;
  assert.equal(detailsOf(after).details, detailsOf(final).details, 'The next status keeps the newer Details.');
  assert.match(after.split('\n')[0], /^✅ Ready to merge · Updated /);
});

test('RACE-RECORD: a status refresh writes nothing when the run record changed after its first read; the next status writes', t => {
  const f = fixture(t); f.machine();
  assert.equal(f.invoke('Review: no must-fix').exitCode, 0);
  const prs = f.data().prs; prs[0].statusCheckRollup = [{ conclusion: 'SUCCESS' }]; f.configure({ prs });
  const record = join(f.runDir, 'status.json');
  // Just before the write, another process saves new readable facts for the PR.
  wrapGh(f, { match: '*"--json body,headRefOid"', before: `${shell(process.execPath)} -e ${shell(`const fs=require('fs'),r=JSON.parse(fs.readFileSync(${JSON.stringify(record)},'utf8'));r.pr.find(p=>p.number===23).readable.facts.updatedAt=1;fs.writeFileSync(${JSON.stringify(record)},JSON.stringify(r));`)}` });
  const body = f.data().prs[0].body, count = editsOf(f).length;
  const first = f.invoke('', 'runStatus'); assert.equal(first.exitCode, 0);
  assert.equal(editsOf(f).length, count); assert.equal(f.data().prs[0].body, body); assert.doesNotMatch(first.message, /updated the top|could not update/);
  assert.equal(f.invoke('', 'runStatus').exitCode, 0);
  assert.equal(editsOf(f).length, count + 1); assert.match(f.data().prs[0].body.split('\n')[0], /^✅ Ready to merge · Updated /);
});

test('CALLS: a status refresh reads each PR once (with its description, head and comments); a change adds one read and the edit', t => {
  const f = fixture(t); f.machine();
  assert.equal(f.invoke('Review: no must-fix').exitCode, 0);
  const log = join(f.base, 'gh-calls.log'), real = join(f.base, 'bin', 'gh-real'), gh = join(f.base, 'bin', 'gh');
  writeFileSync(real, readFileSync(gh, 'utf8')); chmodSync(real, 0o755);
  writeFileSync(gh, `#!/bin/sh\nprintf '%s\\n' "$*" >> ${shell(log)}\nexec ${shell(real)} "$@"\n`); chmodSync(gh, 0o755);
  const calls = () => { try { return readFileSync(log, 'utf8').trim().split('\n').filter(Boolean); } catch { return []; } };
  const status = () => { const from = calls().length; assert.equal(f.invoke('', 'runStatus').exitCode, 0); return calls().slice(from); };
  const prs = f.data().prs; prs[0].statusCheckRollup = [{ conclusion: 'SUCCESS' }]; f.configure({ prs });
  const changed = status(), same = status();
  const views = list => list.filter(call => call.startsWith('pr view'));
  assert.deepEqual(views(same), [`pr view ${url(22)} --json state,mergedAt,statusCheckRollup,baseRefName,headRefOid`, `pr view ${url(23)} --json state,mergedAt,statusCheckRollup,baseRefName,headRefOid,body,comments`], same.join('\n'));
  assert.deepEqual(same.filter(call => !call.startsWith('pr view')), [], 'No change: no other GitHub call (no comments read, no second view, no edit).');
  assert.deepEqual(changed.filter(call => !views(same).includes(call)), [`pr view ${url(23)} --json body,headRefOid`, `pr edit ${url(23)} --body-file -`], changed.join('\n'));
});

 test('FORMAL-PREFIX: a complete filename does not select an unrelated prefix Story', t => {
  const { facts, replay } = namedStoryPublication(t, { story: 'user_stories/value.md extra.md', rules: false, prefixRules: true, vectors: true });
  assert.equal(facts.records.rulesToCheck, false);
  assert.equal(replay.outcome, 'pass');
  facts.records.ci = 'passing';
  assert.match(prStatus(facts), /^✅/);
  facts.mode = 'auto'; facts.records.checker = { verdict: 'PASS' };
  assert.match(prStatus(facts), /^✅/);
});

// #3088: use the real publication boundary, local bare origin and this file's fake gh.
function evidence3088(t, { production = false, fixtureOnly = false, formal = {result: 'not_applicable', scope: 'Coverage validation', reason: 'No separate runtime rule in this synthetic coverage change', control_outcome: 'not_run'}, stale = false, malformed = false, extraFiles = 0, unavailableDiff = false } = {}) {
  const f = fixture(t);
  f.run.areas = [{ name: 'code', steps: ['scope', 'verify', 'formal'], optional: [], gate: 'pr' }];
  f.run.area = 0; f.run.pr = [];
  writeFileSync(join(f.root, 'value'), production ? 'head' : 'base');
  mkdirSync(join(f.root, 'test/helpers'), { recursive: true });
  writeFileSync(join(f.root, fixtureOnly ? 'test/helpers/value.mjs' : 'test/value.test.mjs'), 'import assert from "node:assert/strict"; assert.equal(2, 2);\n');
  for (let i = 0; i < extraFiles; i++) writeFileSync(join(f.root, `test/helpers/extra-${i}.mjs`), 'export const value = 2;\n');
  f.git('add', '.'); f.git('commit', '-qm', 'coverage scope');
  f.machine(f.git('rev-parse', 'HEAD'));
  const path = join(f.runDir, 'old-code-proof.json'), record = JSON.parse(readFileSync(path));
  record.base = phase(0); record.outcome = 'old-passes'; writeFileSync(path, JSON.stringify(record));
  if (formal) writeFileSync(join(f.runDir, 'replay-evidence.json'), JSON.stringify({ schema_version: 'pdd.replay-evidence.v1', run_id: f.run.runId,
    source: { kind: 'git-content-v1', sha256: stale ? '0'.repeat(64) : sourceFingerprint(f.root) }, formal: malformed ? { ...formal, scope: '' } : formal }));
  if (unavailableDiff) {
    const wrapper = join(f.base, 'bin/git');
    writeFileSync(wrapper, readFileSync(wrapper, 'utf8').replace('#!/usr/bin/env node\n', '#!/usr/bin/env node\nif (process.argv.includes("--numstat")) process.exit(1);\n'));
  }
  f.save();
  const out = f.invoke('Result: Formal check: Proved (solver); CI green; checker PASS.\nFormal check: Proved (solver)');
  assert.equal(out.exitCode, 0, out.message);
  const pr = f.data().prs[0], saved = JSON.parse(readFileSync(join(f.runDir, 'status.json'))).pr[0];
  return { f, body: pr.body, visible: pr.body.split(DETAILS_OPEN)[0], facts: saved.readable.facts, details: detailsOf(pr.body).details };
}

test('3088 publication records tests-only old-passes as coverage with no defect-proof blocker', t => {
  const pr = evidence3088(t);
  assert.equal(pr.facts.records.proof.kind, 'coverage');
  assert.equal(pr.facts.records.proof.status, 'old-passes');
  assert.doesNotMatch(pr.visible.split('\n')[0], /⛔/);
  assert.match(pr.visible, /\| Coverage validation[^\n]+✓ pass[^\n]+✓ pass/);
  assert.doesNotMatch(pr.visible, /Proved \(solver\)|CI green|checker PASS|should fail/);
  assert.match(pr.details, /Proved \(solver\)/, 'The original agent report stays attributed in Details.');
});

test('3088 repair 1: scenario-only publication recognizes executable coverage and keeps scope guards', t => {
  const scenario = { schema_version: 'prompt-runtime.program-scenario.v1', steps: [{ step_id: 'value',
    entry_path: 'prompts/value.prompt.md', operation: 'value', checks: [
      { criterion_id: 'AC1', target: 'result', path: '', op: 'equals', value: 2 },
    ] }] };
  for (const options of [
    { path: 'test/runtime/coverage.json', coverage: true },
    { path: 'tests/runtime/coverage.json', coverage: true },
    { path: 'test/runtime/fixture.json', document: { steps: scenario.steps }, coverage: false },
    { path: 'test/runtime/empty.json', document: { ...scenario, steps: [] }, coverage: false },
    { path: 'test/runtime/coverage.json', scenarioRead: 'malformed', coverage: false },
    { path: 'test/runtime/coverage.json', scenarioRead: 'unavailable', coverage: false },
    { path: 'test/runtime/coverage.json', production: true, coverage: false },
    { path: 'test/runtime/coverage.json', unavailableDiff: true, coverage: false },
  ]) {
    const f = fixture(t);
    f.run.areas = [{ name: 'code', steps: ['scope', 'verify', 'formal'], optional: [], gate: 'pr' }];
    f.run.area = 0; f.run.pr = [];
    writeFileSync(join(f.root, 'value'), 'base');
    mkdirSync(join(f.root, 'src'));
    mkdirSync(join(f.root, 'test'), { recursive: true });
    mkdirSync(dirname(join(f.root, options.path)), { recursive: true });
    writeFileSync(join(f.root, 'src/value.mjs'), 'export function value() { return 2; }\n');
    // This runner and production source already exist on the base. Only the scenario is overlaid.
    const relativeScenario = options.path.startsWith('tests/') ? `../${options.path}` : `./${options.path.slice(5)}`;
    writeFileSync(join(f.root, 'test/value.vectors.test.mjs'), `import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {value} from '../src/value.mjs';
const scenario = JSON.parse(readFileSync(new URL(${JSON.stringify(relativeScenario)}, import.meta.url)));
test('scenario coverage', () => {
  for (const step of scenario.steps) for (const check of step.checks)
    assert.equal(value(), check.value, 'ASSERT_3088_SCENARIO');
});
`);
    f.git('add', '.'); f.git('commit', '-qm', 'existing production and vector runner');
    f.git('push', '-q', 'origin', 'HEAD:refs/heads/main');
    f.run.baseSha = f.git('rev-parse', 'HEAD');
    writeFileSync(join(f.root, options.path), JSON.stringify(options.document ?? scenario));
    if (options.production) writeFileSync(join(f.root, 'src/value.mjs'), 'export function value() { return 1 + 1; }\n');
    f.git('add', '.'); f.git('commit', '-qm', 'scenario coverage'); f.save();
    const script = `import {proveRun} from ${JSON.stringify(join(packageRoot, 'src/workflow-prove.mjs'))};
const result = await proveRun({ref:'17', cwd:${JSON.stringify(f.root)}, test:'node --test test/value.vectors.test.mjs', expect:'ASSERT_3088_SCENARIO'});
process.stdout.write(JSON.stringify(result));`;
    execFileSync(process.execPath, ['--input-type=module', '-e', script], { cwd: f.root, encoding: 'utf8',
      env: { ...process.env, PATH: `${join(f.base, 'bin')}:${process.env.PATH}`, GIT_ALLOW_PROTOCOL: 'file' } });
    const proof = JSON.parse(readFileSync(join(f.runDir, 'old-code-proof.json')));
    assert.equal(proof.outcome, 'old-passes');
    assert.deepEqual(proof.paths, [options.path]);
    for (const snapshot of [proof.base, proof.head]) {
      assert.equal(snapshot.exitCode, 0);
      assert.ok(snapshot.stdoutTail.includes('# pass 1'));
      assert.ok(snapshot.stdoutTail.includes('# fail 0'));
      assert.ok(snapshot.stdoutTail.includes('# skipped 0'));
    }
    if (options.unavailableDiff) {
      const wrapper = join(f.base, 'bin/git');
      writeFileSync(wrapper, readFileSync(wrapper, 'utf8').replace('#!/usr/bin/env node\n', '#!/usr/bin/env node\nif (process.argv.includes("--numstat")) process.exit(1);\n'));
    }
    if (options.scenarioRead) {
      const wrapper = join(f.base, 'bin/git');
      const failure = options.scenarioRead === 'malformed' ? 'process.stdout.write("{"); process.exit(0);' : 'process.exit(1);';
      writeFileSync(wrapper, readFileSync(wrapper, 'utf8').replace('#!/usr/bin/env node\n',
        `#!/usr/bin/env node\nif (process.argv[2] === 'show' && process.argv[3]?.endsWith(${JSON.stringify(`:${options.path}`)})) { ${failure} }\n`));
    }
    // Coverage is not a defect proof; record its formal exemption explicitly.
    writeFileSync(join(f.runDir, 'replay-evidence.json'), JSON.stringify({schema_version: 'pdd.replay-evidence.v1', run_id: f.run.runId,
      source: {kind: 'git-content-v1', sha256: sourceFingerprint(f.root)},
      formal: {result: 'not_applicable', scope: 'Scenario coverage', reason: 'No changed runtime rule in this synthetic scenario coverage', control_outcome: 'not_run'}}));
    const out = f.invoke('Result: scenario coverage; both snapshots pass.');
    assert.equal(out.exitCode, 0, out.message);
    const pr = f.data().prs[0], saved = JSON.parse(readFileSync(join(f.runDir, 'status.json'))).pr[0];
    assert.equal(saved.readable.facts.records.proof.kind, options.coverage ? 'coverage' : 'defect', JSON.stringify(options));
    assert.equal(saved.readable.facts.records.proof.status, 'old-passes');
    if (options.coverage) {
      assert.doesNotMatch(pr.body.split('\n')[0], /^⛔/);
      assert.match(pr.body, /\| Coverage validation[^\n]+✓ pass[^\n]+✓ pass/);
    } else assert.match(pr.body.split('\n')[0], /^⛔/);
  }
});

for (const options of [{ production: true }, { fixtureOnly: true }]) test(`3088 non-coverage scope stays blocked ${JSON.stringify(options)}`, t => {
  const pr = evidence3088(t, options);
  assert.equal(pr.facts.records.proof.kind, 'defect');
  assert.match(pr.visible, /^⛔/);
});

const FORMAL3088 = { result: 'not_run', scope: 'bounded values', reason: 'CONTROL_UNAVAILABLE', control_outcome: 'not_run' };
for (const [name, formal, expected] of [
  ['not-run', FORMAL3088, 'not_run'],
  ['proved', PROVED_532, 'proved_bounded'],
  ['failed', { ...FORMAL3088, result: 'failed', counterexample: 3088 }, 'failed'],
]) test(`3088 standalone formal publication uses its recorded ${name} result`, t => {
  const pr = evidence3088(t, { formal });
  assert.equal(pr.facts.records.replay, null);
  assert.ok(pr.facts.records.formal, 'The publication must read the standalone formal block.');
  assert.equal(pr.facts.records.formal.status, 'recorded');
  assert.equal(pr.facts.records.formal.result, expected);
  assert.doesNotMatch(pr.visible, /Proved \(solver\)/);
  const row = pr.visible.split('\n').find(line => line.startsWith('| Formal check'));
  const header = pr.details.split('\n').find(line => line.startsWith('Formal check'));
  assert.ok(row && header);
  if (expected === 'not_run') { assert.match(row, /Not run: CONTROL_UNAVAILABLE/); assert.match(header, /Not run/); }
  if (expected === 'proved_bounded') { assert.match(row, /Proved \(bounded\)/); assert.match(header, /Proved \(bounded\)/); }
  if (expected === 'failed') { assert.match(row, /3088/); assert.match(header, /Failed/); assert.match(pr.visible, /^⛔/); }
  assert.doesNotMatch(pr.details, /^Code replay:/m, 'Reading the formal block does not add a replay requirement.');
});

for (const [option, expected] of [['stale', 'stale'], ['malformed', 'malformed']]) test(`3088 ${option} formal evidence cannot accept the narrative proof claim`, t => {
  const pr = evidence3088(t, { formal: PROVED_532, [option]: true });
  assert.ok(pr.facts.records.formal, 'The publication must read the supplied formal block.');
  assert.equal(pr.facts.records.formal.status, expected);
  assert.match(pr.visible, /^⛔/);
  assert.doesNotMatch(pr.visible, /Proved \(solver\)/);
  assert.match(pr.visible, new RegExp(`\\| Formal check \\| ${expected}`));
  assert.match(pr.details, new RegExp(`^Formal check[^\\n]+${expected}`, 'm'));
});

for (const options of [{ extraFiles: 45 }, { extraFiles: 45, production: true }, { unavailableDiff: true }]) test(`3088 full diff controls coverage, not the bounded display ${JSON.stringify(options)}`, t => {
  const pr = evidence3088(t, options);
  const coverage = !options.production && !options.unavailableDiff;
  assert.equal(pr.facts.records.proof.kind, coverage ? 'coverage' : 'defect');
  if (options.extraFiles) { assert.equal(pr.facts.diff.files.length, 40); assert.ok(pr.facts.diff.count > 40); }
  if (coverage) assert.doesNotMatch(pr.visible, /^⛔/);
  else assert.match(pr.visible, /^⛔/);
});

const makePromptText = (prose, iface) => {
  const placeholder = `${prose}\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify({ ...iface, prose_sha256: '' }, null, 2)}\n\`\`\`\n</details>\n`;
  return `${prose}\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify({ ...iface, prose_sha256: proseSha256(placeholder) }, null, 2)}\n\`\`\`\n</details>\n`;
};

test('2923 publication labels a PR without a saved pdd result and creates missing repo label', t => {
  const f = fixture(t);
  const out = f.invoke('Review: agent claims a pass');
  assert.equal(out.exitCode, 0, out.message);
  assert.deepEqual(f.data().repoLabels, ['pdd:no-verdict']);
  assert.ok(f.data().prs[0].labels?.includes('pdd:no-verdict'));
  assert.match(f.data().prs[0].body, /pdd:no-verdict/);
});

for (const kind of ['pdd test', 'pdd lint']) test(`2923 saved failed ${kind} removes only the no-verdict label`, t => {
  const f = fixture(t, { existing: true });
  const state = f.data(); state.prs[0].labels = ['other', 'pdd:no-verdict']; state.repoLabels = ['pdd:no-verdict']; f.configure(state);
  const out = f.invoke('Review: note', 'stepDone', 'formal', [{ kind, result: 'failed', summary: '✗ failed', at: 1 }]);
  assert.equal(out.exitCode, 0, out.message);
  assert.deepEqual(f.data().prs[0].labels, ['other']);
});

test('2923 label failure warns while the PR remains open', t => {
  const f = fixture(t); f.configure({ failLabel: true });
  const out = f.invoke('Review: note');
  assert.equal(out.exitCode, 0, out.message);
  assert.match(out.message, /warning: pdd could not update the pdd:no-verdict PR label/);
  assert.equal(f.data().prs[0].state, 'OPEN');
});

test('2923 existing repository label is reused without changing it', t => {
  const f = fixture(t); f.configure({ repoLabels: ['pdd:no-verdict', 'other'] });
  const out = f.invoke('Review: note');
  assert.equal(out.exitCode, 0, out.message);
  assert.deepEqual(f.data().repoLabels, ['pdd:no-verdict', 'other']);
  assert.deepEqual(f.data().prs[0].labels, ['pdd:no-verdict']);
});

test('2923 valid native-only PR 1 with zero scenario JSONs renders not-applicable (native-only) and omits pdd:no-verdict', t => {
  const f = fixture(t, { prompt: true });
  mkdirSync(join(f.root, 'prompts'), { recursive: true });
  mkdirSync(join(f.root, 'user_stories'), { recursive: true });
  const promptText = makePromptText('# Crypto ECDH\n\nOwn `src/crypto.mjs`. Validate P-256 ECDH public keys with Node native crypto.', {
    kind: 'native-only',
    status: 'approved',
    reason: 'Node P-256 ECDH validation uses native OpenSSL bindings that bound ports cannot fake',
  });
  writeFileSync(join(f.root, 'prompts/crypto.prompt.md'), promptText);
  writeFileSync(join(f.root, 'user_stories/ecdh.md'), '# Validate ECDH keys\n\nAs a service operator, I want invalid P-256 ECDH public keys rejected, so that handshakes fail safely.\n\n## Acceptance criteria\n\n1. An invalid P-256 point is rejected before shared-secret derivation.\n');
  f.git('add', '.'); f.git('commit', '-qm', 'native-only prompt and story');
  const out = f.invoke('Prompt scope checked');
  assert.equal(out.exitCode, 0, out.message);
  const pr = f.data().prs[0];
  assert.ok(!pr.labels?.includes('pdd:no-verdict'), `unexpected labels: ${JSON.stringify(pr.labels)}`);
  assert.doesNotMatch(pr.body, /pdd:no-verdict/);
  assert.match(pr.body, /\| Prompt tests \(`pdd test`\) \| not-applicable \(native-only\) \|/);
  assert.match(pddPart(pr.body), /pdd result: not-applicable \(native-only\): prompts\/crypto\.prompt\.md \(Node P-256 ECDH validation uses native OpenSSL bindings that bound ports cannot fake\)\./);
});

test('2923 valid native-only code update removes prior pdd:no-verdict label; blank reason or mixed scope still gets pdd:no-verdict', t => {
  const f = fixture(t, { existing: true });
  const validNative = makePromptText('# Crypto ECDH\n\nOwn `src/crypto.mjs`.', {
    kind: 'native-only',
    status: 'approved',
    reason: 'Native OpenSSL P-256 curve point validation',
  });
  f.git('switch', '-q', 'main');
  mkdirSync(join(f.root, 'prompts'), { recursive: true });
  writeFileSync(join(f.root, 'prompts/crypto.prompt.md'), validNative);
  f.git('add', '.'); f.git('commit', '-qm', 'merged native-only prompt');
  f.git('push', '-q', 'origin', 'main', 'main:refs/heads/prompt-topic');
  const mergedBase = f.git('rev-parse', 'HEAD');
  f.git('switch', '-q', 'topic');
  f.git('rebase', '-q', 'main');
  mkdirSync(join(f.root, 'src'), { recursive: true });
  writeFileSync(join(f.root, 'src/crypto.mjs'), `// Generated from prompts/crypto.prompt.md (sha256: ${promptHeaderHash(validNative)}).\nexport const ok = true;\n`);
  f.git('add', '.'); f.git('commit', '-qm', 'native-only code implementation');
  f.git('push', '-qf', 'origin', 'HEAD:refs/heads/topic');
  f.run.baseSha = mergedBase;
  f.save();
  const state = f.data(); state.prs[0].labels = ['keep-me', 'pdd:no-verdict']; state.repoLabels = ['pdd:no-verdict']; f.configure(state);
  const okOut = f.invoke('Review: checked');
  assert.equal(okOut.exitCode, 0, okOut.message);
  assert.deepEqual(f.data().prs[0].labels, ['keep-me']);
  assert.doesNotMatch(f.data().prs[0].body, /pdd:no-verdict/);
  assert.match(pddPart(f.data().prs[0].body), /pdd result: not-applicable \(native-only\): prompts\/crypto\.prompt\.md/);

  // Blank reason on a native-only prompt fails local interface validation and must apply pdd:no-verdict.
  const fp = fixture(t, { existing: true, prompt: true });
  mkdirSync(join(fp.root, 'prompts'), { recursive: true });
  mkdirSync(join(fp.root, 'user_stories'), { recursive: true });
  writeFileSync(join(fp.root, 'user_stories/ecdh.md'), '# Validate ECDH keys\n\nAs a service operator, I want invalid P-256 ECDH public keys rejected, so that handshakes fail safely.\n\n## Acceptance criteria\n\n1. An invalid P-256 point is rejected.\n');
  const blankNative = makePromptText('# Crypto ECDH\n\nOwn `src/crypto.mjs`.', {
    kind: 'native-only',
    status: 'approved',
    reason: '   ',
  });
  writeFileSync(join(fp.root, 'prompts/crypto.prompt.md'), blankNative);
  fp.git('add', '.'); fp.git('commit', '-qm', 'blank reason');
  const pState = fp.data(); pState.prs[0].labels = ['keep-me']; pState.repoLabels = ['pdd:no-verdict']; fp.configure(pState);
  const blankOut = fp.invoke('Prompt scope checked');
  assert.equal(blankOut.exitCode, 0, blankOut.message);
  assert.deepEqual(fp.data().prs[0].labels, ['keep-me', 'pdd:no-verdict']);
  assert.match(fp.data().prs[0].body, /pdd:no-verdict/);

  // Restoring valid native-only reason while adding an executable partial prompt keeps pdd:no-verdict because scope is mixed.
  writeFileSync(join(fp.root, 'prompts/crypto.prompt.md'), validNative);
  const partialPrompt = makePromptText('# Policy\n\nOwn `src/policy.mjs`.', {
    kind: 'partial',
    status: 'approved',
    entries: [],
    calls: [],
    resources: [],
    limits: { max_steps: 1, max_model_calls: 1 },
    conventions: [],
  });
  writeFileSync(join(fp.root, 'prompts/policy.prompt.md'), partialPrompt);
  fp.git('add', '.'); fp.git('commit', '-qm', 'mixed prompts');
  const current = fp.data(); current.prs[0].labels = ['keep-me']; fp.configure(current);
  const mixedOut = fp.invoke('Prompt scope mixed');
  assert.equal(mixedOut.exitCode, 0, mixedOut.message);
  assert.deepEqual(fp.data().prs[0].labels, ['keep-me', 'pdd:no-verdict']);
});

test('2923 unusable local-only lint and partial unfinished batches keep pdd:no-verdict and emit noResultLine, while finished failed and refused verdicts remove it', t => {
  for (const unusable of [
    { kind: 'pdd lint', localOnly: true, state: 'partial', summary: 'Local lint: 0 layout problems. partial (local-only).', at: 1 },
    { kind: 'pdd test', state: 'partial', states: [{ test: 'test/runtime/value.json', state: 'partial' }], summary: 'Prompt tests: no verdict · 1 partial (no-server-verdict)', at: 1 },
  ]) {
    const f = fixture(t, { existing: true });
    const state = f.data(); state.prs[0].labels = ['other']; state.repoLabels = ['pdd:no-verdict']; f.configure(state);
    const out = f.invoke('Review: note', 'stepDone', 'formal', [unusable]);
    assert.equal(out.exitCode, 0, out.message);
    assert.deepEqual(f.data().prs[0].labels, ['other', 'pdd:no-verdict']);
    const details = pddPart(f.data().prs[0].body);
    assert.match(details, new RegExp(`pdd result: ${unusable.kind}`));
    assert.match(details, /pdd result: none\. pdd has no pdd test or pdd lint result of its own for this run \(pdd:no-verdict\)\./);
  }

  for (const usable of [
    { kind: 'pdd test', state: 'failed', states: [{ test: 'test/runtime/value.json', state: 'failed' }], summary: 'Prompt tests: ✗ 0 of 1 criteria', at: 1 },
    { kind: 'pdd lint', state: 'refused', summary: 'Prompt lint: refused · 1 problem', at: 1 },
  ]) {
    const f = fixture(t, { existing: true });
    const state = f.data(); state.prs[0].labels = ['other', 'pdd:no-verdict']; state.repoLabels = ['pdd:no-verdict']; f.configure(state);
    const out = f.invoke('Review: note', 'stepDone', 'formal', [usable]);
    assert.equal(out.exitCode, 0, out.message);
    assert.deepEqual(f.data().prs[0].labels, ['other']);
    assert.doesNotMatch(pddPart(f.data().prs[0].body), /pdd result: none\. pdd has no pdd test or pdd lint result/);
  }
});

test('2923 valid native-only PR 1 with saved pdd lint still renders not-applicable (native-only) for Prompt tests in Checks', t => {
  const f = fixture(t, { prompt: true });
  mkdirSync(join(f.root, 'prompts'), { recursive: true });
  mkdirSync(join(f.root, 'user_stories'), { recursive: true });
  writeFileSync(join(f.root, 'prompts/crypto.prompt.md'), makePromptText('# Crypto ECDH\n\nOwn `src/crypto.mjs`.', {
    kind: 'native-only',
    status: 'approved',
    reason: 'Native OpenSSL P-256 curve point validation',
  }));
  writeFileSync(join(f.root, 'user_stories/ecdh.md'), '# Validate ECDH keys\n\nAs a service operator, I want invalid P-256 ECDH public keys rejected, so that handshakes fail safely.\n\n## Acceptance criteria\n\n1. An invalid P-256 point is rejected.\n');
  f.git('add', '.'); f.git('commit', '-qm', 'native-only prompt and story');
  const out = f.invoke('Prompt scope checked', 'stepDone', 'check', [
    { kind: 'pdd lint', state: 'passed', summary: 'Prompt lint: ✓ 0 of 0 tests pass · 0 problems', at: 1 },
  ]);
  assert.equal(out.exitCode, 0, out.message);
  const pr = f.data().prs[0];
  assert.ok(!pr.labels?.includes('pdd:no-verdict'), `unexpected labels: ${JSON.stringify(pr.labels)}`);
  assert.doesNotMatch(pr.body, /pdd:no-verdict/);
  assert.match(pr.body, /\| Prompt tests \(`pdd test`\) \| not-applicable \(native-only\) \|/);
  assert.match(pr.body, /\| Lint \(`pdd lint`\) \| 0 of 0 tests pass \|/);
  assert.match(pddPart(pr.body), /pdd result: pdd lint/);
  assert.match(pddPart(pr.body), /pdd result: not-applicable \(native-only\): prompts\/crypto\.prompt\.md \(Native OpenSSL P-256 curve point validation\)\./);
});

test('2923 nativeOnlyPrompts scopes to merge-base against origin/baseBranch plus pr1.sourcePaths after PR 1 merges and ignores uncommitted edits', t => {
  const validNative = makePromptText('# Crypto ECDH\n\nOwn `src/crypto.mjs`.', {
    kind: 'native-only',
    status: 'approved',
    reason: 'Native OpenSSL P-256 curve point validation',
  });
  const partialPrompt = makePromptText('# Policy\n\nOwn `src/policy.mjs`.', {
    kind: 'partial',
    status: 'approved',
    entries: [],
    calls: [],
    resources: [],
    limits: { max_steps: 1, max_model_calls: 1 },
    conventions: [],
  });
  const blankNative = makePromptText('# Crypto ECDH\n\nOwn `src/crypto.mjs`.', {
    kind: 'native-only',
    status: 'approved',
    reason: '   ',
  });

  // 1. Upstream advancing on origin/main with a non-native partial prompt does not cause a false pdd:no-verdict alarm when merged into a valid native-only branch.
  const f1 = fixture(t, { prompt: true });
  f1.git('switch', '-q', 'main');
  mkdirSync(join(f1.root, 'prompts'), { recursive: true });
  writeFileSync(join(f1.root, 'prompts/upstream.prompt.md'), partialPrompt);
  f1.git('add', '.'); f1.git('commit', '-qm', 'upstream partial prompt');
  f1.git('push', '-q', 'origin', 'main');
  f1.git('switch', '-q', 'topic');
  f1.git('merge', '--no-edit', '-q', 'origin/main');
  mkdirSync(join(f1.root, 'user_stories'), { recursive: true });
  writeFileSync(join(f1.root, 'prompts/crypto.prompt.md'), validNative);
  writeFileSync(join(f1.root, 'user_stories/ecdh.md'), '# Validate ECDH keys\n\nAs a service operator, I want invalid P-256 ECDH public keys rejected, so that handshakes fail safely.\n\n## Acceptance criteria\n\n1. An invalid P-256 point is rejected.\n');
  f1.git('add', '.'); f1.git('commit', '-qm', 'own native-only prompt');
  const out1 = f1.invoke('Prompt scope checked');
  assert.equal(out1.exitCode, 0, out1.message);
  assert.ok(!f1.data().prs[0].labels?.includes('pdd:no-verdict'));
  assert.doesNotMatch(f1.data().prs[0].body, /pdd:no-verdict/);

  // 2. Upstream advancing on origin/main with a native-only prompt does not grant a false exemption when merged into a branch with no prompt of its own.
  const f2 = fixture(t, { prompt: true });
  f2.git('switch', '-q', 'main');
  mkdirSync(join(f2.root, 'prompts'), { recursive: true });
  writeFileSync(join(f2.root, 'prompts/upstream-native.prompt.md'), validNative);
  f2.git('add', '.'); f2.git('commit', '-qm', 'upstream native-only prompt');
  f2.git('push', '-q', 'origin', 'main');
  f2.git('switch', '-q', 'topic');
  f2.git('merge', '--no-edit', '-q', 'origin/main');
  const out2 = f2.invoke('Prompt scope with unowned change only');
  assert.equal(out2.exitCode, 0, out2.message);
  assert.ok(f2.data().prs[0].labels?.includes('pdd:no-verdict'));
  assert.match(f2.data().prs[0].body, /pdd:no-verdict/);

  // 3. PR 2 after PR 1 merged into origin/main preserves valid native-only scope via pr1.sourcePaths even when PR 2 only changes tests.
  const f3 = fixture(t, { existing: true });
  f3.git('switch', '-q', 'main');
  f3.git('checkout', '-q', 'topic', '--', 'value');
  mkdirSync(join(f3.root, 'prompts'), { recursive: true });
  writeFileSync(join(f3.root, 'prompts/crypto.prompt.md'), validNative);
  f3.git('add', '.'); f3.git('commit', '-qm', 'merged PR 1 native-only prompt');
  f3.git('push', '-q', 'origin', 'main', 'main:refs/heads/prompt-topic');
  f3.git('switch', '-q', 'topic');
  f3.git('rebase', '-q', 'main');
  mkdirSync(join(f3.root, 'test'), { recursive: true });
  writeFileSync(join(f3.root, 'test/crypto.test.mjs'), 'import assert from "node:assert/strict";\nassert.equal(1, 1);\n');
  f3.git('add', '.'); f3.git('commit', '-qm', 'native test only on PR 2');
  f3.git('push', '-qf', 'origin', 'HEAD:refs/heads/topic');
  f3.run.prBase = 'main';
  f3.run.pr[0].sourcePaths = ['prompts/crypto.prompt.md'];
  f3.save();
  const s3 = f3.data(); s3.prs[0].labels = ['keep-me', 'pdd:no-verdict']; s3.repoLabels = ['pdd:no-verdict']; f3.configure(s3);
  const out3 = f3.invoke('Review: test-only PR 2 after merged native-only PR 1');
  assert.equal(out3.exitCode, 0, out3.message);
  assert.deepEqual(f3.data().prs[0].labels, ['keep-me']);
  assert.doesNotMatch(f3.data().prs[0].body, /pdd:no-verdict/);
  assert.match(pddPart(f3.data().prs[0].body), /pdd result: not-applicable \(native-only\): prompts\/crypto\.prompt\.md/);

  // 4. Uncommitted working-tree edits during draftDescription are ignored in both directions because committed HEAD:<path> is read.
  const f4 = fixture(t, { existing: true, prompt: true });
  mkdirSync(join(f4.root, 'prompts'), { recursive: true });
  writeFileSync(join(f4.root, 'prompts/crypto.prompt.md'), validNative);
  f4.git('add', '.'); f4.git('commit', '-qm', 'committed valid native-only prompt');
  const validHead = f4.git('rev-parse', 'HEAD');
  f4.git('commit', '--allow-empty', '-qm', 'remote ahead');
  f4.git('push', '-qf', 'origin', 'HEAD:refs/heads/topic');
  f4.git('reset', '-q', '--hard', validHead);
  awaitingCode(f4);
  const s4 = f4.data(); s4.prs[0].labels = ['keep-me', 'pdd:no-verdict']; s4.repoLabels = ['pdd:no-verdict']; f4.configure(s4);
  // Dirty uncommitted invalid edit + untracked partial prompt must not break committed valid native-only PR 1 (removes pdd:no-verdict).
  writeFileSync(join(f4.root, 'prompts/crypto.prompt.md'), blankNative);
  writeFileSync(join(f4.root, 'prompts/untracked.prompt.md'), partialPrompt);
  const out4 = f4.invoke('', 'approveRun');
  assert.equal(out4.exitCode, 1);
  assert.deepEqual(f4.data().prs[0].labels, ['keep-me']);
  assert.doesNotMatch(f4.data().prs[0].body, /pdd:no-verdict/);

  // Dirty uncommitted valid native-only edit must not spoof exemption when committed HEAD prompt has blank reason.
  rmSync(join(f4.root, 'prompts/untracked.prompt.md'));
  f4.git('add', 'prompts/crypto.prompt.md'); f4.git('commit', '-qm', 'committed blank reason');
  const blankHead = f4.git('rev-parse', 'HEAD');
  f4.git('commit', '--allow-empty', '-qm', 'remote ahead 2');
  f4.git('push', '-qf', 'origin', 'HEAD:refs/heads/topic');
  f4.git('reset', '-q', '--hard', blankHead);
  writeFileSync(join(f4.root, 'prompts/crypto.prompt.md'), validNative);
  const out5 = f4.invoke('', 'approveRun');
  assert.equal(out5.exitCode, 1);
  assert.deepEqual(f4.data().prs[0].labels, ['keep-me', 'pdd:no-verdict']);
  assert.match(f4.data().prs[0].body, /pdd:no-verdict/);
});

test('2923 draftDescription syncs pdd:no-verdict only after gh pr edit succeeds and on sameReadableTop no-op, and label create tolerates already_exists without --force', t => {
  const f = fixture(t, { existing: true, prompt: true });
  mkdirSync(join(f.root, 'user_stories'), { recursive: true });
  writeFileSync(join(f.root, 'user_stories/value.md'), VALUE_STORY);
  f.git('add', '.'); f.git('commit', '-qm', 'add story');
  f.git('push', '-qf', 'origin', 'HEAD:refs/heads/topic');
  awaitingCode(f);
  // When gh pr edit --body-file - fails, labels are NOT mutated (neither added nor removed).
  f.configure({ prs: [{ ...f.data().prs[0], labels: ['keep-me'] }], repoLabels: ['pdd:no-verdict'], failEdit: 1 });
  const failedAdd = f.invoke('', 'approveRun');
  assert.equal(failedAdd.exitCode, 1);
  assert.match(failedAdd.message, /could not update the PR 1 description/);
  assert.deepEqual(f.data().prs[0].labels, ['keep-me']);

  f.configure({ prs: [{ ...f.data().prs[0], labels: ['keep-me', 'pdd:no-verdict'] }], failEdit: 2 });
  const failedRemove = f.invoke('', 'approveRun', 'check', [{ kind: 'pdd lint', state: 'passed', summary: 'Prompt lint: ✓ 1 of 1 tests pass', at: 1 }]);
  assert.equal(failedRemove.exitCode, 1);
  assert.deepEqual(f.data().prs[0].labels, ['keep-me', 'pdd:no-verdict']);

  // Once gh pr edit succeeds, syncNoVerdictLabel applies the label update.
  f.configure({ failEdit: 0, prs: [{ ...f.data().prs[0], labels: ['keep-me'] }] });
  const okSync = f.invoke('', 'approveRun');
  assert.equal(okSync.exitCode, 1);
  assert.deepEqual(f.data().prs[0].labels, ['keep-me', 'pdd:no-verdict']);

  // On a subsequent refresh where sameReadableTop holds (zero body edits), syncNoVerdictLabel still reconciles a missing label.
  const editsBefore = f.data().events.filter(event => event.kind === 'edit').length;
  f.configure({ prs: [{ ...f.data().prs[0], labels: ['keep-me'] }] });
  const noopSync = f.invoke('', 'approveRun');
  assert.equal(noopSync.exitCode, 1);
  assert.equal(f.data().events.filter(event => event.kind === 'edit').length, editsBefore, 'sameReadableTop skips gh pr edit --body-file -');
  assert.deepEqual(f.data().prs[0].labels, ['keep-me', 'pdd:no-verdict']);

  // Concurrent label creation returning already_exists / "already exists" succeeds without --force or warning.
  for (const raceMessage of ['GraphQL: Label already exists (createLabel)', 'HTTP 422: Validation Failed (already_exists)']) {
    const fr = fixture(t);
    fr.configure({ repoLabels: [], labelRace: raceMessage });
    const out = fr.invoke('Review: note');
    assert.equal(out.exitCode, 0, out.message);
    assert.doesNotMatch(out.message, /warning: pdd could not update the pdd:no-verdict PR label/);
    assert.deepEqual(fr.data().labelCreates, [['label', 'create', 'pdd:no-verdict', '--repo', 'example/project']]);
    assert.ok(!fr.data().labelCreates[0].includes('--force'));
    assert.deepEqual(fr.data().prs[0].labels, ['pdd:no-verdict']);
  }
});

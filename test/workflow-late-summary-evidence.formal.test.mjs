import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync, realpathSync, chmodSync, cpSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { execFileSync } from 'node:child_process';
import {pinReplayVectors,sourceFingerprint} from '../src/workflow-replay.mjs';
import { DETAILS_OPEN, detailsOf, prStatus } from '../src/workflow-pr-body.mjs';

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
else if(a[1]==='list')out(s.prs.filter(p=>!a.includes('--head')||p.headRefName===flag('--head')).map(p=>({...p,headRefOid:remote()||p.headRefOid})));
else if(a[1]==='view'){const found=s.prs.find(p=>p.url===a[2]),p=found?.headRefName==='topic'?{...found,headRefOid:remote()||found.headRefOid}:found||{body:''};out(String(flag('--json')).split(',').includes('comments')?{...p,comments:(s.comments||[]).map(c=>({author:{login:'reviewer'},authorAssociation:c.author_association,body:c.body,createdAt:c.created_at,url:c.html_url}))}:p)}
else if(a[0]==='api'&&a[1]==='user')out('publisher');
else if(a[0]==='api'&&a.some(x=>x.includes('/comments'))&&a.includes('POST')){
 const body=JSON.parse(fs.readFileSync(0,'utf8')).body,number=(s.comments||[]).length+1;
 s.events.push({kind:'comment',body});s.comments??=[];
 if(!s.failComment){s.comments.push({body:s.wrongContent?body+' altered':body,user:{login:s.wrongActor?'other':'publisher'},html_url:'https://github.com/example/project/pull/'+(s.wrongPr?24:23)+'#issuecomment-'+number});
  if(s.ambiguousComment)s.comments.push({body,user:{login:'publisher'},html_url:'https://github.com/example/project/pull/23#issuecomment-'+(number+1)});
  if(s.foreignComment)s.comments.push({body,user:{login:'other'},html_url:'https://github.com/example/project/pull/23#issuecomment-'+(number+1)});
 }
 fs.writeFileSync(file,JSON.stringify(s));if(s.failComment){process.stderr.write('error: comment failed');process.exit(1)}out('{}');
}
else if(a[0]==='api'&&a.some(x=>x.includes('/comments')))out(a.includes('--slurp')?[s.comments||[]]:(s.comments||[]).map(c=>JSON.stringify(c)).join('\\n'));
else if(a[1]==='create'||a[1]==='edit'){
 if(flag('--body-file')!=='-')throw Error('must read body from stdin');
 const body=fs.readFileSync(0,'utf8'),kind=a[1];s.events.push({kind,body,remote:remote(),head:commit()});
 if(kind==='edit'&&s.failEdit===s.events.filter(e=>e.kind==='edit').length){fs.writeFileSync(file,JSON.stringify(s));process.stderr.write('error: refused edit');process.exit(1)}
 if(kind==='create'){s.prs.push({number:23,url:'https://github.com/example/project/pull/23',state:'OPEN',headRefName:flag('--head'),baseRefName:flag('--base'),headRefOid:commit(),body,title:flag('--title'),headRepository:{name:'project'},headRepositoryOwner:{login:'example'},isCrossRepository:false,mergeCommit:null});out(s.prs.at(-1).url)}
 else{s.prs.find(p=>p.url===a[2]).body=body;out('updated')}
 fs.writeFileSync(file,JSON.stringify(s));
 if(kind==='edit'&&s.unknownEdit){process.stderr.write('lost reply');process.exit(1)}
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
  const machine = (proved = head) => writeFileSync(join(runDir, 'old-code-proof.json'), JSON.stringify({ v: 2, origin: 'pdd.workflow-prove.v2',interruptSignal:'', runId: run.runId, baseSha, headSha: proved, test: 'node --test test/value.test.mjs', expect: 'defect', paths: ['test/value.test.mjs'], base: phase(1, true), head: phase(0), outcome: 'proved', cleanupError: '', setupError: '' }));
  const change = () => { writeFileSync(join(root, 'value'), 'new head'); git('commit', '-qam', 'new source'); return git('rev-parse', 'HEAD'); };
  const data = () => JSON.parse(readFileSync(state, 'utf8'));
  return { base, root, bare, git, run, head, runDir, save, invoke, machine, change, data, configure: values => writeFileSync(state, JSON.stringify({ ...data(), ...values })) };
}
// Finite domain: 2 note alphabets × 2 boundary offsets × 3 custody states.
// Each case exercises the actual stepDone publication boundary with an isolated fake GitHub.
for (const glyph of ['x', '😀']) for (const offset of [0, 1]) for (const custody of ['valid', 'wrongActor', 'wrongPr']) {
  test(`bounded recovery: ${glyph} offset ${offset} custody ${custody}`, t => {
    const f = fixture(t, { prompt: true });
    const late = 'Limitation: upstream failure remains DEFERRED; https://github.com/example/upstream/issues/476';
    const summary = `${glyph.repeat(60000 + offset)}\n${late}\n/home/somebody/private https://runtime.example/s/private-token`;
    f.run.done.scope.summary = summary; f.save();
    if (custody !== 'valid') f.configure({ [custody]: true });
    const result = f.invoke('check complete'), data = f.data();
    data.comments ??= [];
    assert.equal(data.prs.length, 1);
    assert.ok([...data.prs[0].body].length <= 60000);
    assert.ok(data.comments.every(c => [...c.body].length <= 60000));
    assert.doesNotMatch(data.prs[0].body + data.comments.map(c => c.body).join(''), /private-token|\/home\/somebody/);
    if (custody !== 'valid') {
      assert.equal(result.exitCode, 1);
      assert.match(data.prs[0].body, /recovery is pending/);
      assert.equal(data.events.filter(e => e.kind === 'edit').length, 0);
      return;
    }
    assert.equal(result.exitCode, 0, result.message);
    const indexUrl = /Full step summaries: (https:\/\/[^\s_]+)/.exec(data.prs[0].body)?.[1];
    const index = data.comments.find(c => c.html_url === indexUrl && c.user.login === 'publisher');
    assert.ok(index, 'recovery must link to a confirmed same-PR index');
    const links = [...index.body.matchAll(/https:\/\/github\.com\/example\/project\/pull\/23#issuecomment-\d+/g)].map(m => m[0]);
    const chunks = links.map(link => data.comments.find(c => c.html_url === link && c.user.login === 'publisher'));
    assert.ok(chunks.every(Boolean));
    const recovered = chunks.map(c => c.body).join('');
    assert.ok(recovered.includes(late), 'late limitation and complete URL must be readable');
    assert.ok(!recovered.includes('\ufffd'), 'Unicode code points must remain intact');
  });
}

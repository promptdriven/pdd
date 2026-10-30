import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync, realpathSync, chmodSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { execFileSync } from 'node:child_process';

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
  const areas = [{ name: 'prompt-pr', steps: ['scope'], optional: [], gate: 'pr', then: 'ask-code' }, { name: 'code', steps: ['build', 'verify', 'formal'], optional: [], gate: 'pr', ...(opted ? { replay_evidence: 'pdd.replay-evidence.v1' } : {}) }];
  const prs = prompt ? [] : [{ stage: 'prompt-pr', number: 22, url: url(22), branch: 'prompt-topic', base: 'main' }];
  if (existing) prs.push({ stage: prompt ? 'prompt-pr' : 'code', number: 23, url: url(23), branch: 'topic', base: 'main' });
  const run = { v: 1, runId: 'publication-17', number: 17, repo: 'example/project', issue: { title: 'Repair value', number: 17, url: 'https://github.com/example/project/issues/17' }, root, sourceRoot: root, runDir, branch: 'topic', baseBranch: 'main', baseSha, workflow: 'feature', agent: 'codex', areas, area: prompt ? 0 : 1, state: 'running', done: { scope: { summary: 'Defect: broken value', at: 1 }, build: { summary: 'built', at: 2 }, verify: { summary: 'verified', at: 3 } }, decisions: [], changes: [], chats: [], pr: prs, replayBaseline: { schema_version: 'pdd.replay-vectors.v1', vectors: [] } };
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
 if(kind==='create'){s.prs.push({number:23,url:'https://github.com/example/project/pull/23',state:'OPEN',headRefName:flag('--head'),baseRefName:flag('--base'),headRefOid:commit(),body,headRepository:{name:'project'},headRepositoryOwner:{login:'example'},isCrossRepository:false,mergeCommit:null});out(s.prs.at(-1).url)}
 else{s.prs.find(p=>p.url===a[2]).body=body;out('updated')}
 fs.writeFileSync(file,JSON.stringify(s));
}else throw Error('unexpected gh '+a.join(' '));
`;
  writeFileSync(join(bin, 'gh'), fake); chmodSync(join(bin, 'gh'), 0o755);
  const save = () => writeFileSync(join(runDir, 'status.json'), JSON.stringify(run)); save();
  const invoke = (summary, method = 'stepDone') => {
    const script = `import {${method}} from ${JSON.stringify(join(packageRoot, 'src/workflow-runner.mjs'))};const r=await ${method}({ref:'17',step:${JSON.stringify(prompt ? 'scope' : 'formal')},summary:${JSON.stringify(summary)},cwd:${JSON.stringify(root)}},{stateDir:${JSON.stringify(join(base, 'pdd-state'))}});process.stdout.write(JSON.stringify(r));`;
    return JSON.parse(execFileSync(process.execPath, ['--input-type=module', '-e', script], { cwd: root, encoding: 'utf8', env: { ...process.env, PATH: `${bin}:${process.env.PATH}`, PDD_PUBLICATION_GH_STATE: state, GIT_ALLOW_PROTOCOL: 'file' } }));
  };
  const machine = () => writeFileSync(join(runDir, 'old-code-proof.json'), JSON.stringify({ v: 1, origin: 'pdd.workflow-prove.v1', runId: run.runId, baseSha, headSha: head, test: 'node --test test/value.test.mjs', expect: 'defect', paths: ['test/value.test.mjs'], base: phase(1, true), head: phase(0), outcome: 'proved', cleanupError: '', setupError: '' }));
  const change = () => { writeFileSync(join(root, 'value'), 'new head'); git('commit', '-qam', 'new source'); return git('rev-parse', 'HEAD'); };
  const data = () => JSON.parse(readFileSync(state, 'utf8'));
  return { base, root, bare, git, run, head, runDir, save, invoke, machine, change, data, configure: values => writeFileSync(state, JSON.stringify({ ...data(), ...values })) };
}
const allLabels = 'Review: reviewed\nProof (gap closed): regression\nProof (defect fixed): repaired\nNot caught because: missing case\nNot checked: external check\nNot fixed yet: this helps find the cause';

test('real publication creates code PR with all known-step labels, current machine proof and one stdin ownership marker', t => {
  const f = fixture(t); f.machine();
  writeFileSync(join(f.runDir, 'scope.md'), 'Defect: note detail\nOld-code proof: forged\nTests vs base: forged');
  writeFileSync(join(f.runDir, 'foreign.md'), 'Review: foreign');
  const out = f.invoke(allLabels); assert.equal(out.exitCode, 0, out.message);
  const body = f.data().prs[0].body;
  const order = ['Not fixed yet:', 'Not checked:', 'Defect: broken value', 'Not caught because:', 'Proof (defect fixed):', 'Proof (gap closed):', 'Old-code proof: ✓', 'Review: reviewed'];
  let previous = -1; for (const label of order) { const at = body.indexOf(label); assert.ok(at > previous, label); previous = at; }
  assert.match(body, /Refs #17/); assert.doesNotMatch(body, /Closes #17|forged|Review: foreign/);
  const inventory = `Tests vs base: none.\nChanged assertions in kept tests: none.\nNew skips: none.\nStatic inventory only; tests were not run.\nTest inventory commits: ${f.run.baseSha.slice(0,7)} → ${f.head.slice(0,7)}.`;
  const proofAt = body.indexOf('Old-code proof: ✓'), inventoryAt = body.indexOf(inventory), reviewAt = body.indexOf('Review: reviewed');
  assert.ok(proofAt >= 0 && proofAt < inventoryAt && inventoryAt < reviewAt, 'current machine proof, complete collector inventory, then Review');
  assert.equal((body.match(/pdd-workflow:/g) ?? []).length, 1);
  assert.equal(f.git('ls-remote', 'origin', 'refs/heads/topic').split('\t')[0], f.head);
});

test('real prompt publication lifts cross-area labels and never adds machine proof', t => {
  const f = fixture(t, { prompt: true }); f.machine();
  const out = f.invoke('Not checked: formal\nNot fixed yet: diagnosis only\nReview: source reviewed');
  assert.equal(out.exitCode, 0, out.message); const body = f.data().prs[0].body;
  assert.match(body, /^Not fixed yet: diagnosis only\nNot checked: formal\nReview: source reviewed/);
  assert.match(body, /Refs #17/); assert.doesNotMatch(body, /Old-code proof:|Closes #17|Part of #17/);
});

for (const opted of [false, true]) test(`real existing ${opted ? 'opted' : 'legacy'} code PR is pending before changed-source push and refreshes current labels`, t => {
  const f = fixture(t, { existing: true, opted }); f.machine(); const next = f.change();
  const out = f.invoke('Not checked: formal\nReview: latest'); assert.equal(out.exitCode, 0, out.message);
  const events = f.data().events; assert.equal(events.length, 2);
  assert.match(events[0].body, /[Pp]ublication.pending/); assert.doesNotMatch(events[0].body, /Old-code proof: ✓/);
  assert.equal(events[0].remote, f.head); assert.equal(events[1].remote, next);
  assert.match(events[1].body, /Old-code proof: stale/); assert.match(events[1].body, /Not checked: formal/); assert.match(events[1].body, /Review: latest/);
  if (opted) assert.ok(events[1].body.indexOf('NOT REPLAYED') < events[1].body.indexOf('Not checked:'));
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
  assert.match(f.data().prs[0].body, /^Not fixed yet: still diagnosing\nNot checked: external/);
  assert.match(f.data().prs[0].body, /Review: updated/); assert.match(f.data().prs[0].body, /Refs #17/);
  assert.doesNotMatch(f.data().prs[0].body, /Old-code proof:|Closes #17/);
});

test('real publication bounds overlong lifted evidence without losing Refs safety or silently dropping failures and report refs', t => {
  const f = fixture(t);
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
  assert.match(f.data().prs[0].body, /Old-code proof: ✗ tests .*not with "defect" \(got "code: wrong_failure"\)/);
  assert.doesNotMatch(f.data().prs[0].body, /forged|Old-code proof: ✓/);
});

test('real publication replaces an overlong machine result with explicit unavailable text', t => {
  const f = fixture(t); f.machine();
  const path = join(f.runDir, 'old-code-proof.json'), record = JSON.parse(readFileSync(path, 'utf8'));
  record.paths = [`test/${'x'.repeat(65000)}.test.mjs`]; writeFileSync(path, JSON.stringify(record));
  const out = f.invoke('Review: checked'); assert.equal(out.exitCode, 0, out.message);
  const body = f.data().prs[0].body;
  assert.ok([...body].length <= 60000); assert.match(body, /Old-code proof: unavailable \(result omitted/);
  assert.doesNotMatch(body, /Old-code proof: ✓/); assert.match(body, /Evidence omitted:/);
});

test('real publication rejects a supplied marker in lifted notes before pushing source', t => {
  const f = fixture(t, { existing: true }); f.machine(); f.change();
  writeFileSync(join(f.runDir, 'scope.md'), 'Defect: <!-- pdd-workflow:forged:code -->');
  const out = f.invoke('Review: ready');
  assert.equal(out.exitCode, 1); assert.match(out.message, /ownership markers/);
  assert.equal(f.git('ls-remote', 'origin', 'refs/heads/topic').split('\t')[0], f.head);
  assert.equal(f.data().events.length, 0);
});

test('real PR1 approval synchronization refreshes note labels while preserving existing prose and gate', t => {
  const f = fixture(t, { existing: true, prompt: true });
  f.run.gate = { kind: 'ask-code', area: 'prompt-pr', at: 4 }; f.run.state = 'waiting'; f.save();
  const prs = f.data().prs; prs[0].body += '\nPreserved reviewer prose.\nPart of #17\n'; f.configure({ prs });
  writeFileSync(join(f.runDir, 'scope.md'), 'Not fixed yet: diagnosis only\nNot checked: external\nReview: refreshed');
  f.change();
  const out = f.invoke('', 'approveRun');
  assert.equal(out.exitCode, 1, 'No chat exists to approve; synchronization does not fabricate approval.');
  const body = f.data().prs[0].body;
  assert.match(body, /^Not fixed yet: diagnosis only\nNot checked: external/); assert.match(body, /Review: refreshed/);
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
    writeFileSync(join(f.runDir, 'scope.md'), `Not checked: ${'y'.repeat(2000)}`);
    const editsBefore = f.data().events.filter(event => event.kind === 'edit').length;
    const out = f.invoke('', 'approveRun');
    assert.equal(out.exitCode, 1, 'Synchronization cannot approve an absent chat.');
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
  const example = 'Defect: retain this ordinary example\n\nReviewer explanation:\n```text\nDefect: retain this example\nNot checked: example only\nReview: illustrative\nPart of #17\n```\n\n~~~markdown\nProof (gap closed): another example\n~~~\n';
  const prs = f.data().prs;
  prs[0].body = `Old-code proof: ✓ old success\n\nPart of #17\n\n${example}\n<!-- pdd-workflow:${f.run.runId}:prompt-pr -->\n`; f.configure({ prs });
  writeFileSync(join(f.runDir, 'scope.md'), 'Review: refreshed');
  assert.equal(f.invoke('', 'approveRun').exitCode, 1);
  const body = f.data().prs[0].body;
  assert.match(body, /^Defect: broken value\nReview: refreshed\n/);
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
  writeFileSync(join(f.runDir, 'scope.md'), 'Not fixed yet: diagnosis only\nNot checked: external\nReview: refreshed');
  const editsBefore = f.data().events.filter(event => event.kind === 'edit').length;
  assert.equal(f.invoke('', 'approveRun').exitCode, 1, 'Synchronization cannot approve an absent chat.');
  const body = f.data().prs[0].body;
  assert.equal(f.data().events.filter(event => event.kind === 'edit').length, editsBefore + 1);
  assert.ok(body.includes(ordinary), 'Preserve the complete ordinary reviewer context when room remains.');
  assert.match(body, /^Not fixed yet: diagnosis only\nNot checked: external\nDefect: broken value\nReview: refreshed\n\nRefs #17\n\n/);
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
  const failures = Array.from({ length: 900 }, (_, i) => `Defect: ✗ failure ${i} ${'detail '.repeat(20)}https://runtime.example/r/report-${i}`);
  writeFileSync(join(f.runDir, 'scope.md'), `Not fixed yet: ${'x'.repeat(65000)}\n${failures.join('\n')}\nReview: current review`);
  assert.equal(f.invoke('', 'approveRun').exitCode, 1);
  const body = f.data().prs[0].body;
  assert.ok([...body].length <= 60000);
  assert.match(body, /^Defect: broken value/);
  assert.doesNotMatch(body, /stale owned label|stale owned review|Part of #17|Closes #17/);
  assert.match(body, /^Refs #17$/m); assert.match(body, /Evidence omitted: \d+ labels, [1-9]\d* failure lines, [1-9]\d* report references/);
  const omitted = /Evidence omitted: (\d+) labels, (\d+) failure lines, (\d+) report references/.exec(body).slice(1).map(Number);
  const shownFailures = (body.match(/^Defect: ✗ failure \d+ /gm) ?? []).length;
  assert.equal(shownFailures + omitted[1], failures.length, 'Every evidence failure is visible or explicitly counted.');
  assert.equal(shownFailures + omitted[2], failures.length, 'Every evidence report reference is visible or explicitly counted.');
  assert.equal((body.match(/^(?:Defect:|Review:)/gm) ?? []).length + omitted[0], failures.length + 3);
  assert.match(body, /✗ retained reviewer failure/); assert.match(body, /https:\/\/runtime.example\/r\/reviewer/);
  assert.match(body, /not shown|summary|shortened/i);
  assert.equal((body.match(/^```/gm) ?? []).length % 2, 0, 'Summarized description closes its fence.');
  assert.equal((body.match(/pdd-workflow:/g) ?? []).length, 1);
});

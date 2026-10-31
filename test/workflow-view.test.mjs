import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, realpathSync, symlinkSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { proseSha256 } from '../src/runtime-preflight.mjs';

const bin = resolve(import.meta.dirname, '../bin/pdd.mjs');
function fixture(t) {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-view '))); t.after(() => rmSync(root, { recursive: true, force: true }));
  const repo = join(root, 'project'), home = join(root, 'home'); mkdirSync(repo); mkdirSync(home);
  const git = (...args) => { const r = spawnSync('git', args, { cwd: repo, encoding: 'utf8' }); assert.equal(r.status, 0, r.stderr); return r.stdout.trim(); };
  git('init', '-q', '-b', 'main'); git('config', 'user.name', 'Local view proof'); git('config', 'user.email', 'test@example.invalid');
  writeFileSync(join(repo, 'base.txt'), 'base'); git('add', '.'); git('commit', '-qm', 'Base');
  const baseSha = git('rev-parse', 'HEAD'), runDir = join(repo, '.git/pdd/runs/2442'); mkdirSync(runDir, { recursive: true });
  const write = (path, text) => { mkdirSync(join(repo, path, '..'), { recursive: true }); writeFileSync(join(repo, path), text); };
  write('user_stories/greet.md', '# Greet\n\nI can read a greeting.\n\n## Acceptance criteria\n1. The greeting is "Hello".\n');
  write('user_stories/PLAN.md', '# Plan\nReview the greeting.\n');
  const prompt = '# Greet\nReturn Hello.\n\n<details><summary>Runtime interface</summary>\n\n```json\n'+JSON.stringify({ status: 'draft', prose_sha256: '', entries: [], calls: [] })+'\n```\n</details>\n';
  write('prompts/greet.prompt.md', prompt.replace('"prose_sha256":""', '"prose_sha256":"'+proseSha256(prompt)+'"'));
  write('tests/greet.json', JSON.stringify({ schema_version: 'prompt-runtime.program-scenario.v1', story_path: 'user_stories/greet.md', steps: [{ entry_path: 'prompts/greet.prompt.md' }] }));
  writeFileSync(join(runDir, 'verify.md'), '# Verify\nLocal checks passed.\n');
  const run = { v: 1, runId: 'view-proof', repo: 'Acme/Project', number: 2442, workflow: 'feature', agent: 'codex',
    issue: { title: 'Read-only review', url: 'https://github.com/Acme/Project/issues/2442' }, root: repo, sourceRoot: repo,
    commonDir: join(repo, '.git'), runDir, branch: 'main', baseSha, state: 'waiting', area: 1,
    areas: [{ name: 'story', steps: ['understand', 'prompt-story'], optional: [], gate: 'approve' }, { name: 'prompt-pr', steps: ['check', 'try'], optional: ['try'], gate: 'pr', then: 'ask-code' }, { name: 'code', steps: ['build', 'verify'], optional: [], gate: 'pr' }],
    gate: { area: 'prompt-pr', kind: 'approve-pr', at: 2000 }, decisions: [{ stage: 'story', decision: 'approve', via: 'terminal', at: 1000 }],
    done: { check: { summary: 'Runtime check (greet) (DRAFT): ✓ 1 of 1 criterion; Report: https://runtime.example.test/r/report-id' }, try: { summary: 'Try: https://runtime.example.test/s/review-token/' } },
    pr: [{ number: 23, stage: 'prompt-pr', url: 'https://github.com/Acme/Project/pull/23', state: 'open' }], chats: [], updatedAt: 2000 };
  const save = () => writeFileSync(join(runDir, 'status.json'), JSON.stringify(run)); save();
  const env = { ...process.env, HOME: home, CLAUDE_CONFIG_DIR: '' };
  const cli = (...args) => spawnSync(process.execPath, [bin, ...args], { cwd: repo, env, encoding: 'utf8', timeout: 10000 });
  return { root, repo, home, git, runDir, run, save, env, cli };
}

test('VIEW1: view combines saved gates, approvals, issue, authored files, runtime reports, Try and PR links', t => {
  const f = fixture(t), r = f.cli('workflow', 'view', '2442');
  assert.equal(r.status, 0, r.stderr);
  for (const text of ['Read-only review', 'State: waiting', 'Gate: prompt-pr', 'story', 'approved', 'Pending', 'prompt-pr', 'draft',
    f.run.issue.url, f.run.pr[0].url, 'https://runtime.example.test/r/report-id', 'https://runtime.example.test/s/review-token/', 'Runtime check (greet)', f.run.baseSha]) assert.ok(r.stdout.includes(text), text+'\n'+r.stdout);
  for (const path of ['user_stories/greet.md', 'user_stories/PLAN.md', 'prompts/greet.prompt.md', 'tests/greet.json', '.git/pdd/runs/2442/verify.md']) assert.ok(r.stdout.includes(pathToFileURL(join(f.repo, path)).href), path);
  assert.match(r.stdout, /uncommitted/); assert.match(r.stdout, /current files/); assert.match(r.stdout, /(?:gate|approval)[^\n]*draft[^\n]*(?:together|one|cover)|(?:one|together)[^\n]*(?:gate|approval)[^\n]*draft/i);
});

test('VIEW2: view performs only local reads and leaves run, index, HOME and authored files unchanged', t => {
  const f = fixture(t), guard = join(f.root, 'read-only.mjs');
  writeFileSync(guard, `import fs from 'node:fs'; import fp from 'node:fs/promises'; import child from 'node:child_process'; import {syncBuiltinESMExports} from 'node:module'; import {promisify} from 'node:util';
const stop=()=>{throw Error('View attempted an effect');};
for(const key of ['writeFileSync','appendFileSync','mkdirSync','renameSync','unlinkSync','rmSync','copyFileSync','truncateSync'])fs[key]=stop;
for(const key of ['writeFile','appendFile','mkdir','rename','unlink','rm','copyFile','truncate'])fp[key]=stop;
const exec=child.execFile; child.execFile=(file,args,...rest)=>{if(file!=='git'||!['rev-parse','diff','ls-files','--no-optional-locks'].includes(args[0]))stop();return exec(file,args,...rest);};
child.execFile[promisify.custom]=(file,args,options)=>new Promise((resolve,reject)=>child.execFile(file,args,options,(error,stdout,stderr)=>error?reject(error):resolve({stdout,stderr})));
for(const key of ['exec','spawn','spawnSync','execSync','execFileSync','fork'])child[key]=stop;globalThis.fetch=stop;syncBuiltinESMExports();`);
  const status = readFileSync(join(f.runDir, 'status.json')), index = readFileSync(join(f.repo, '.git/index')), story = readFileSync(join(f.repo, 'user_stories/greet.md'));
  const r = spawnSync(process.execPath, ['--import', guard, bin, 'workflow', 'view', '2442'], { cwd: f.repo, env: f.env, encoding: 'utf8', timeout: 10000 });
  assert.equal(r.status, 0, r.stderr); assert.match(r.stdout, /State: waiting/);
  assert.deepEqual(readFileSync(join(f.runDir, 'status.json')), status); assert.deepEqual(readFileSync(join(f.repo, '.git/index')), index);
  assert.deepEqual(readFileSync(join(f.repo, 'user_stories/greet.md')), story); assert.deepEqual(readdirSync(f.home), []);
});

test('VIEW3: completed, cancelled, optional code authorization and absent links stay explicit', t => {
  const f = fixture(t); f.run.done = {}; f.run.pr = []; f.run.decisions = [];
  for (const state of ['completed', 'cancelled']) {
    f.run.state = state; f.run.gate = null; f.save();
    const r = f.cli('workflow', 'view', '2442'); assert.equal(r.status, 0, r.stderr);
    assert.match(r.stdout, /Gate: none/); assert.match(r.stdout, /Try: not recorded/); assert.match(r.stdout, /PRs: none recorded/);
  }
  f.run.state = 'completed'; f.run.gate = { area: 'prompt-pr', kind: 'ask-code' }; f.save();
  assert.match(f.cli('workflow', 'view', '2442').stdout, /code.*authorization/i);
});

test('VIEW4: missing runs and missing worktrees are clear; help and completion advertise the view', t => {
  const f = fixture(t);
  const missing = f.cli('workflow', 'view', '999'); assert.equal(missing.status, 1); assert.match(missing.stderr, /no pdd run/i);
  f.run.root = join(f.root, 'missing'); f.save();
  const r = f.cli('workflow', 'view', '2442'); assert.equal(r.status, 0, r.stderr); assert.match(r.stdout, /unavailable/i);
  assert.match(f.cli('workflow', 'view', '--help').stdout, /pdd workflow view ISSUE/);
  assert.match(f.cli('completion', 'bash').stdout, /view/);
});

test('VIEW5: an area waiting on its PR shows PR review/merge as the pending human action', t => {
  const f = fixture(t); f.run.gate = null; f.save();
  const r = f.cli('workflow', 'view', '2442');
  assert.equal(r.status, 0, r.stderr); assert.match(r.stdout, /Pending:.*review.*merge.*PR/i);
  assert.doesNotMatch(r.stdout, /current area still needs to finish/);
});


test('RELEASE5: ancestor aliases show artifacts and notes; redirected notes are explicitly unavailable', t => {
  const f = fixture(t), alias = join(f.root, 'alias'); symlinkSync(f.root, alias);
  f.run.root = join(alias, 'project'); f.run.commonDir = join(f.run.root, '.git'); f.run.runDir = join(f.run.commonDir, 'pdd/runs/2442'); f.save();
  const view = f.cli('workflow', 'view', '2442'); assert.equal(view.status, 0, view.stderr);
  assert.match(view.stdout, /Prompt status: prompts\/greet.prompt.md — draft/);
  assert.match(view.stdout, /Gate note: .*verify.md/);
  assert.doesNotMatch(view.stdout, /unavailable/);
  const outside = join(f.root, 'outside'); mkdirSync(outside); writeFileSync(join(outside, 'private.md'), 'must not read');
  const redirected = join(f.repo, '.git', 'redirected-notes'); symlinkSync(outside, redirected);
  f.run.runDir = redirected; f.save();
  const blocked = f.cli('workflow', 'view', '2442');
  assert.match(blocked.stdout, /Gate notes unavailable/);
  assert.doesNotMatch(blocked.stdout, /private.md/);
});

// user_stories/prompt-tests-line.md: view shows Prompt tests lines and older Runtime check lines alike, and the Try links.
test('VIEW-PROMPT-TESTS: view shows new and old summary lines, joined with "; " or one per line, and Try links', t => {
  const f = fixture(t);
  f.run.done = { check: { summary: 'Prompt tests (greet) (DRAFT): ✓ 1 of 1 criterion; Runtime check (wave): ✗ 0 of 1 criterion; Report: https://runtime.example.test/r/report-id' },
    verify: { summary: 'Prompt tests (greet): ✓ 1 of 1 criterion\nPrompt tests: ✓ 1 of 1 criterion' },
    try: { summary: 'Try: https://runtime.example.test/s/review-token/' } }; f.save();
  const r = f.cli('workflow', 'view', '2442'); assert.equal(r.status, 0, r.stderr);
  const lines = r.stdout.split('\n');
  for (const start of ['Prompt tests (greet) (DRAFT):', 'Runtime check (wave):', 'Prompt tests (greet):', 'Prompt tests:']) assert.ok(lines.some(line => line.startsWith(start)), start);
  assert.ok(!lines.some(line => /^(?:Prompt tests|Runtime check).*(?:Prompt tests|Runtime check)/.test(line)), 'one line each');
  assert.ok(lines.includes('Try: https://runtime.example.test/s/review-token/'), r.stdout);
});

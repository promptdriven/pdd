import assert from 'node:assert/strict';
import {execFileSync, spawnSync} from 'node:child_process';
import {mkdtempSync, mkdirSync, readFileSync, realpathSync, rmSync, writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath} from 'node:url';

export const packageRoot = resolve(process.env.PDD_TEST_ROOT ?? fileURLToPath(new URL('../..', import.meta.url)));
export const inventory = JSON.parse(readFileSync(new URL('../fixtures/recover-guidance-code-review-cases.json', import.meta.url)));
export const nativeCase = id => inventory.cases.find(row => row.id === id) ?? assert.fail(`Missing approved case ${id}`);

// Real CLI and Git against a local bare origin; executable gh/Herdr transports
// have fixture-owned state. No pane command is executed and no network is used.
export function fixture(t) {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-guidance-review-')));
  t.after(() => rmSync(base, {recursive:true, force:true}));
  const root = join(base, 'project'), remote = join(base, 'remote.git'), bin = join(base, 'bin');
  const transport = join(base, 'transport.json'), herdrState = join(base, 'herdr.json'), race = join(base, 'race.json');
  const home = join(base, 'home'), status = join(root, '.git/pdd/runs/17/status.json');
  for (const dir of [root, bin, join(home, '.codex')]) mkdirSync(dir, {recursive:true});
  const route = `url.file://${remote}.insteadOf=https://github.com/example/project.git`;
  const env = {...process.env, HOME:home, CODEX_HOME:join(home, '.codex'), CLAUDE_CONFIG_DIR:join(home, '.claude'),
    XDG_CONFIG_HOME:join(home, '.config'), PDD_SUITE_QUEUE:join(base, 'suite-queue'), PDD_INTERPRETER_QUEUE:join(base, 'interpreter-queue'), PATH:`${bin}:${dirname(process.execPath)}:/usr/bin:/bin`, PDD_AGENT_SESSION:'1',
    GIT_CONFIG_NOSYSTEM:'1', GIT_CONFIG_GLOBAL:join(base, 'gitconfig')};
  writeFileSync(env.GIT_CONFIG_GLOBAL, '');
  const git = (...args) => execFileSync('/usr/bin/git', ['-c', route, ...args], {cwd:root, env, encoding:'utf8', stdio:['ignore','pipe','pipe']}).trim();
  git('init', '--bare', '-q', remote); git('init', '-qb', 'main');
  git('config', 'user.name', 'Synthetic regression'); git('config', 'user.email', 'test@example.invalid');
  git('remote', 'add', 'origin', 'https://github.com/example/project.git');
  writeFileSync(join(root, 'guidance.md'), 'Original guidance.\n'); git('add', '.'); git('commit', '-qm', 'Base'); git('push', '-q', 'origin', 'main');
  const baseSha = git('rev-parse', 'HEAD'); git('switch', '-qc', 'guidance-topic');
  writeFileSync(join(root, 'guidance.md'), 'Reviewed guidance.\n'); git('commit', '-qam', 'Guidance only');
  const runDir = dirname(status);
  mkdirSync(runDir, {recursive:true});
  writeFileSync(status, JSON.stringify({v:1, runId:'synthetic-guidance-review', repo:'example/project', number:17,
    issue:{title:'Guidance only', number:17, url:'https://github.com/example/project/issues/17'}, workflow:'bug', skill:'pdd-bug', skillDir:join(packageRoot,'skills/pdd-bug'), agent:'codex',
    root, sourceRoot:root, commonDir:join(root, '.git'), runDir, branch:'guidance-topic', baseBranch:'main', baseSha,
    startedAt:1, state:'running', area:0,
    areas:[{name:'prompt-pr', steps:['check','try'], optional:['try'], gate:'pr', before:'approve', then:'ask-code'},
      {name:'code', steps:['build','verify'], optional:[], gate:'pr'}],
    done:{check:{at:1, summary:'Native synthetic setup; no hosted result claimed.'}}, gate:null, decisions:[], changes:[], pr:[],
    chats:[{area:'prompt-pr', agent:'codex', paneId:'synthetic-pane', tabId:'synthetic-tab', startedAt:1, state:'running',
      session:{agent:'codex', id:'00000000-0000-4000-8000-000000000017'}}]}));
  writeFileSync(transport, JSON.stringify({prs:[], events:[]}));
  // Read-command race hooks inject a separately saved record after command
  // selection, before the owned write. They never alter the implementation.
  writeFileSync(join(bin, 'git'), `#!${process.execPath}
const fs=require('node:fs'),cp=require('node:child_process'),a=process.argv.slice(2),file=${JSON.stringify(transport)},s=JSON.parse(fs.readFileSync(file));
s.events.push({program:'git',args:a});fs.writeFileSync(file,JSON.stringify(s));
if(fs.existsSync(${JSON.stringify(race)})){const r=JSON.parse(fs.readFileSync(${JSON.stringify(race)}));if(a[0]===r.trigger){
const p=${JSON.stringify(status)},run=JSON.parse(fs.readFileSync(p));for(const [key,value] of Object.entries(r.patch))run[key]=value;
fs.writeFileSync(p,JSON.stringify(run));fs.writeFileSync(${JSON.stringify(join(base, 'raced-status.json'))},fs.readFileSync(p));fs.unlinkSync(${JSON.stringify(race)});}}
const r=cp.spawnSync('/usr/bin/git',a[0]==='remote'&&a[1]==='get-url'?a:['-c',${JSON.stringify(route)},...a],{stdio:'inherit'});process.exit(r.status??1);
`, {mode:0o755});
  writeFileSync(join(bin, 'gh'), `#!${process.execPath}
const fs=require('node:fs'),cp=require('node:child_process'),file=${JSON.stringify(transport)},s=JSON.parse(fs.readFileSync(file)),a=process.argv.slice(2),flag=n=>a[a.indexOf(n)+1],out=x=>process.stdout.write(typeof x==='string'?x:JSON.stringify(x));
s.events.push({program:'gh',args:a});
if(a[0]==='repo')out({nameWithOwner:'example/project',defaultBranchRef:{name:'main'},url:'https://github.com/example/project'});
else if(a[0]==='pr'&&a[1]==='list')out(s.prs.filter(p=>!a.includes('--head')||p.headRefName===flag('--head')));
else if(a[0]==='pr'&&a[1]==='view')out(s.prs.find(p=>p.url===a[2])||{body:''});
else if(a[0]==='pr'&&a[1]==='create'){const p={number:23,url:'https://github.com/example/project/pull/23',state:'OPEN',headRefName:flag('--head'),baseRefName:flag('--base'),headRefOid:cp.execFileSync('git',['rev-parse','HEAD'],{encoding:'utf8'}).trim(),body:fs.readFileSync(0,'utf8'),title:flag('--title'),headRepository:{name:'project'},headRepositoryOwner:{login:'example'},isCrossRepository:false,mergeCommit:null,statusCheckRollup:[]};s.prs.push(p);out(p.url);}
else if(a[0]==='pr'&&a[1]==='edit'){s.prs.find(p=>p.url===a[2]).body=fs.readFileSync(0,'utf8');out('updated');}
else throw Error('Unexpected synthetic gh route '+a.join(' '));
fs.writeFileSync(file,JSON.stringify(s));
`, {mode:0o755});
  const fakeHerdrPath = fileURLToPath(new URL('./fake-herdr.mjs', import.meta.url));
  writeFileSync(join(bin, 'herdr'), `#!${process.execPath}
import fs from 'node:fs';
import {fakeHerdr} from ${JSON.stringify(fakeHerdrPath)};
const file=${JSON.stringify(herdrState)},h=fakeHerdr();
if(fs.existsSync(file))Object.assign(h,JSON.parse(fs.readFileSync(file)));
else {h.tabs=[{tab_id:'synthetic-tab',workspace_id:'synthetic-workspace'}];h.panes=[{pane_id:'synthetic-pane',tab_id:'synthetic-tab',workspace_id:'synthetic-workspace',terminal_id:'synthetic-terminal',cwd:${JSON.stringify(root)},agent:{agent:'codex',agent_status:'idle',agent_session:{agent:'codex',kind:'id',value:'00000000-0000-4000-8000-000000000017'},prompts:[]}}];}
try{process.stdout.write(JSON.stringify(await h.herdr(process.argv.slice(4))));}
catch(e){process.stdout.write(JSON.stringify({error:{code:e.code??e.message,message:e.message}}));process.exitCode=1;}
finally{fs.writeFileSync(file,JSON.stringify(h));}
`, {mode:0o755});
  // .mjs is unnecessary for shebang scripts when this private package is ESM.
  writeFileSync(join(bin, 'package.json'), '{"type":"module"}');
  // git/gh use CommonJS intentionally, independent of the enclosing package.
  for (const name of ['git','gh']) {
    const code = readFileSync(join(bin, name), 'utf8');
    writeFileSync(join(bin, `${name}.cjs`), code, {mode:0o755});
    writeFileSync(join(bin, name), `#!/bin/sh\nexec ${shell(process.execPath)} ${shell(join(bin, `${name}.cjs`))} "$@"\n`, {mode:0o755});
  }
  const read = () => JSON.parse(readFileSync(status));
  const data = () => JSON.parse(readFileSync(transport));
  const f = {base, root, status, runDir, env, git, read, data, transcript:[],
    bytes:() => readFileSync(status),
    save:run => writeFileSync(status, JSON.stringify(run)),
    patch:patch => writeFileSync(status, JSON.stringify({...read(), ...patch})),
    race:patch => writeFileSync(race, JSON.stringify({trigger:'diff',patch})),
    racedBytes:() => readFileSync(join(base, 'raced-status.json')),
    herdr:() => {try{return JSON.parse(readFileSync(herdrState));}catch{return {calls:[]};}},
    cli(args, input, options={}) {
      const result = spawnSync(process.execPath, [join(packageRoot, 'bin/pdd.mjs'), ...args],
        {cwd:root, env, encoding:'utf8', input, timeout:20000, ...options});
      assert.ifError(result.error);
      const row = {args, input:input??null, status:result.status, stdout:result.stdout, stderr:result.stderr};
      f.transcript.push(row);
      if (process.env.PDD_RECOVERY_TRANSCRIPT) writeFileSync(process.env.PDD_RECOVERY_TRANSCRIPT, JSON.stringify(f.transcript, null, 2));
      return row;
    },
    merge() {
      const remoteState = data(); remoteState.prs[0].state='MERGED'; remoteState.prs[0].mergedAt='2026-11-05T00:00:00Z';
      writeFileSync(transport, JSON.stringify(remoteState)); git('push', '-q', 'origin', 'guidance-topic:main');
    },
    effects() {
      const events = data().events;
      return {commits:events.filter(e=>e.program==='git'&&e.args[0]==='commit').length,
        pushes:events.filter(e=>e.program==='git'&&e.args[0]==='push').length,
        branches:git('for-each-ref', '--format=%(refname)', 'refs/heads'),
        publications:events.filter(e=>e.program==='gh'&&['create','edit'].includes(e.args[1])).length,
        chatAllocations:f.herdr().calls.filter(a=>['create','open','run'].includes(a[1])).length};
    }
  };
  return f;
}
function shell(value) {return "'"+value.replaceAll("'", "'\\''")+"'";}
export function success(result) {assert.equal(result.status, 0, result.stderr || result.stdout);return result;}
export function reviewedPr1(f) {
  const row=nativeCase('reviewed-empty-pr1');
  success(f.cli(row.commands[0])); assert.deepEqual(f.read().gate.promptSnapshot, row.expected.reviewed_selection);
  success(f.cli(row.commands[1], row.approval_input));
  assert.equal(f.read().gate.kind, row.expected.pending_gate);
  assert.equal(f.read().decisions.length, row.expected.pr1_decisions);
  assert.deepEqual(f.read().decisions[0].evidence.prompts, row.expected.pr1_approval_selection);
  return f.read();
}
export function missingCompletedReview(f) {
  reviewedPr1(f);
  const row=nativeCase('invalidate-and-complete');
  success(f.cli(row.commands[0])); assert.equal(Object.hasOwn(f.read().gate, 'promptSnapshot'), row.expected.current_review_present);
  f.merge(); success(f.cli(row.commands[1]));
  assert.equal(f.read().state, row.expected.state); assert.equal(f.read().doneAt, row.expected.done_at);
  return f.read();
}

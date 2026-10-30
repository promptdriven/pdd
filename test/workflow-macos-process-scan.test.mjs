import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile as callbackExec } from 'node:child_process';
import { promisify } from 'node:util';

const exec = promisify(callbackExec);
// Each child changes only its own OS and external-program boundary. The imported
// production scanner, stop lifecycle, runner and real stores are unchanged.
const probe = String.raw`
import assert from 'node:assert/strict';
import childProcess from 'node:child_process';
import { syncBuiltinESMExports } from 'node:module';
import { promisify } from 'node:util';
import { readFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';
const [scenario, operation] = process.argv.slice(1), original = childProcess.execFile;
const ordinary = promisify(original), commands = [], hooks = [];
let root = '/worktree', stopped = false;
Object.defineProperty(process, 'platform', { value: 'darwin' });
const gone = () => Object.assign(Error('process gone'), {code:1, stdout:'', stderr:''});
const execute = async (file, args, ...options) => {
  if(file === 'ps' && args[0] === '-axo') {
    commands.push([file,...args]);
    if(scenario === 'ps-malformed') return {stdout:'unreadable process list',stderr:''};
    const pids = scenario === 'empty-gone' ? [7002] : scenario === 'new-detached' ? [7001] : [7001,7002];
    if(scenario === 'descendant-gone' && !stopped) pids.push(7005);
    return {stdout:pids.map(pid => [pid,scenario === 'descendant-gone' && pid === 7002 ? 7005 : 1,pid,process.getuid()].join(' ')).join('\n')+'\n',stderr:''};
  }
  if(file === 'ps' && args[0] === '-p' && args[1] === '7002') {
    if(['partial-live','identity-error'].includes(scenario)) {
      if(scenario === 'identity-error') throw Object.assign(gone(),{stderr:'permission denied'});
      return {stdout:'7002 Thu Oct 29 12:00:00 2026 S\n',stderr:''};
    }
    throw gone();
  }
  if(file === 'lsof') {
    commands.push([file,...args]);
    let stdout = 'p7001\nfcwd\nn/elsewhere\n';
    if(scenario === 'descendant-gone' && !stopped) stdout += 'p7005\nfcwd\nn/elsewhere\n';
    if(scenario === 'normal') return {stdout:stdout+'p7002\nfcwd\nn/another-directory\n',stderr:''};
    if(scenario === 'empty-gone') stdout = '';
    if(scenario === 'malformed') stdout += 'unrecognized output\n';
    if(scenario === 'incomplete') stdout += 'p7002\nfcwd\n';
    if(scenario === 'relative') stdout = 'p7001\nfcwd\nnunknown\n';
    if(scenario === 'duplicate') stdout += stdout;
    if(scenario === 'detached') stdout += 'p7002\nfcwd\nn'+join(root,'nested')+'\n';
    if(scenario === 'new-detached') stdout += 'p7004\nfcwd\nn'+root+'\n';
    const code = scenario === 'hard-error' ? 2 : 1;
    throw Object.assign(Error('Command failed: lsof '+Array.from({length:500},(_,i)=>i+1).join(',')),
      {code,stdout,stderr:scenario === 'stderr-error' ? 'permission denied' : ''});
  }
  return ordinary(file,args,...options);
};
childProcess.execFile = Object.assign((...args) => original(...args), {[promisify.custom]:execute});
syncBuiltinESMExports();
const {stopChats} = await import('./src/workflow-chat.mjs');
const {cancelRun} = await import('./src/workflow-runner.mjs');
const success = ['normal','partial-gone','empty-gone','descendant-gone'].includes(scenario);
const info = () => scenario === 'descendant-gone' && !stopped
  ? {shell_pid:7001,foreground_process_group_id:7005,foreground_processes:[{pid:7005,argv:['codex'],cwd:root}]}
  : {shell_pid:7001,foreground_process_group_id:7001,foreground_processes:[]};
const nativePorts = scenario === 'descendant-gone' ? {nativeIdentity:async pid=>pid === 7005 && !stopped ? {group:7005,birth:'owned'} : null,
  stopProcessGroup:async group=>{assert.equal(group,7005);stopped=true;}} : {};
try {
  if(operation === 'stop') {
    const out = await stopChats({root,agent:'codex',state:'running',chats:[{paneId:'pane',tabId:'tab'}]}, {...nativePorts,
      herdr:async args => args[0] === 'pane' ? {result:{process_info:info()}} : {}});
    assert.equal(out.stopped,success,JSON.stringify(out));
    if(!success) { assert.ok(out.warnings.join('').length < 400); assert.doesNotMatch(out.warnings.join(''),/Command failed|1,2,3,4/); }
  } else {
    const {cancellationFixture} = await import('./test/helpers/cancellation-fixture.mjs');
    const f = await cancellationFixture({after:fn=>hooks.push(fn)});
    root = f.old.root;
    if(scenario === 'descendant-gone') { Object.assign(f.ports,nativePorts); const herdr=f.ports.herdr; f.ports.herdr=async args=>args[0]==='pane' && args[1]==='process-info'?{result:{process_info:info()}}:herdr(args); }
    const status = readFileSync(join(f.runDir,'status.json'),'utf8'), claim = readFileSync(f.claim,'utf8');
    if(scenario.startsWith('herdr-')) f.ports.herdr = async () => {throw Object.assign(Error(scenario.slice(6)),{code:scenario.slice(6)});};
    const out = operation === 'cancel' ? await cancelRun({ref:f.old.runId,cwd:f.source},f.ports)
      : await f.start({name:'feature',replace:f.old.runId});
    assert.equal(out.exitCode,success ? 0 : 1,out.message);
    if(success) {
      assert.equal(operation === 'cancel' ? f.read().state : JSON.parse(readFileSync(join(f.runDir+'-cancelled-'+f.old.runId.slice(0,8),'status.json'),'utf8')).state,'cancelled');
      assert.equal(existsSync(f.claim),operation !== 'cancel');
      if(operation === 'replace') assert.notEqual(f.read().runId,f.old.runId);
    } else {
      assert.equal(readFileSync(join(f.runDir,'status.json'),'utf8'),status);
      assert.equal(readFileSync(f.claim,'utf8'),claim);
      assert.equal(f.chats.length,1);
      assert.ok(!f.events.some(event=>['save','release','allocate','start'].includes(event[0])));
      if(scenario.startsWith('herdr-')) assert.match(out.message,new RegExp(scenario.slice(6)));
    }
  }
  if(commands.some(command=>command[0] === 'lsof')) {
    for(const command of commands.filter(command=>command[0] === 'lsof')) {
      assert.equal(command.includes('-p'),false,'Do not pass every user PID to lsof');
      assert.ok(command.includes('-u'),'Whole-user cwd inspection retains detached writers');
    }
  }
} finally { for(const hook of hooks.reverse()) await hook(); }
`;

const scenarios = ['descendant-gone','normal','ps-malformed','partial-gone','empty-gone','partial-live','identity-error','malformed','incomplete','relative','duplicate','hard-error','stderr-error','detached','new-detached'];
for (const scenario of scenarios) test(`MACSCAN: ${scenario} through production non-Linux stop and cancellation`, async () => {
  for (const operation of ['stop','cancel','replace']) {
    try { await exec(process.execPath, ['--input-type=module','-e',probe,scenario,operation], { cwd: new URL('..',import.meta.url), maxBuffer: 1024*1024 }); }
    catch(error) { assert.fail(`${scenario}/${operation}: ${error.stderr || error.message}`); }
  }
});
for (const code of ['pane_not_found','server_not_running']) test(`MACSCAN D1 hold: ${code} still refuses cancel and replacement`, async () => {
  for (const operation of ['cancel','replace']) {
    try { await exec(process.execPath, ['--input-type=module','-e',probe,`herdr-${code}`,operation], { cwd: new URL('..',import.meta.url), maxBuffer: 1024*1024 }); }
    catch(error) { assert.fail(`${code}/${operation}: ${error.stderr || error.message}`); }
  }
});

import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync, spawnSync } from 'node:child_process';
import { EventEmitter } from 'node:events';
import { chatCommand, herdrCommand, startChat } from '../src/workflow-chat.mjs';

const temp = t => { const path = realpathSync(mkdtempSync(join(tmpdir(), "pdd-chat 'q' "))); t.after(() => rmSync(path, { recursive: true, force: true })); return path; };
// A fake native CLI that prints its argv and the marker the chat gets.
const nativeScript = `#!${process.execPath}\nprocess.stdout.write(JSON.stringify({argv:process.argv.slice(2),marker:process.env.PDD_AGENT_SESSION??null,config:process.env.CLAUDE_CONFIG_DIR??process.env.CODEX_HOME??null}));process.exitCode=Number(process.env.PDD_FIXTURE_EXIT??0);\n`;

test('the shell line gives the native CLI the whole first message as one argument, with full access and the person config folder', t => {
  const root = temp(t), bin = join(root, 'bin'), cwd = join(root, 'work tree "x"');
  mkdirSync(bin); mkdirSync(cwd);
  for (const name of ['claude', 'codex']) writeFileSync(join(bin, name), nativeScript, { mode: 0o755 });
  const message = "Use the pdd-bug skill.\nIssue: o/r#3 \"it's $(touch broken) `x`\"\n";
  const file = join(root, "plan 'start'.md"); writeFileSync(file, message);
  const id = '11111111-1111-4111-8111-111111111111';
  for (const [agent, line] of [['claude', chatCommand({ agent: 'claude', cwd, messageFile: file, sessionId: id, configDir: join(root, "cfg 'c'") })],
    ['codex', chatCommand({ agent: 'codex', cwd, messageFile: file })]]) {
    const out = JSON.parse(execFileSync('/bin/sh', ['-c', line], { cwd: root, env: { PATH: `${bin}:/usr/bin:/bin` }, encoding: 'utf8' }));
    assert.equal(out.argv.at(-1), message.replace(/\n+$/, ''), agent);
    assert.equal(out.marker, '1');
    if (agent === 'claude') { assert.deepEqual(out.argv.slice(0, -1), ['--dangerously-skip-permissions', '--session-id', id]); assert.equal(out.config, join(root, "cfg 'c'")); }
    else assert.deepEqual(out.argv.slice(0, -1), ['--no-daemon', '--dangerously-bypass-approvals-and-sandbox', '-c', `projects={${JSON.stringify(cwd)}={trust_level="trusted"}}`]);
  }
  assert.equal(execFileSync('/bin/sh', ['-c', `ls ${JSON.stringify(root)}`], { encoding: 'utf8' }).includes('broken'), false);
  assert.match(chatCommand({ agent: 'claude', cwd, resumeId: id }), new RegExp(`claude --dangerously-skip-permissions --resume '${id}'$`));
  assert.match(chatCommand({ agent: 'codex', cwd, resumeId: id }), new RegExp(`codex resume '${id}' --no-daemon --dangerously-bypass-approvals-and-sandbox -c `));
});

test('PIPE1: native launch preserves more than 64 KiB of guidance and zero/nonzero exit status', t => {
  const root = temp(t), bin = join(root, 'bin'), file = join(root, 'large-start.md'); mkdirSync(bin);
  const message = 'Use the pdd-bug skill.\n' + 'x'.repeat(85_000);
  writeFileSync(file, message);
  for (const [agent, status] of [['codex', 0], ['claude', 7]]) {
    writeFileSync(join(bin, agent), nativeScript, { mode: 0o755 });
    const command = chatCommand({ agent, cwd: root, messageFile: file, sessionId: '11111111-1111-4111-8111-111111111111', configDir: root });
    const r = spawnSync('/bin/sh', ['-c', command], { cwd: root, env: { PATH: `${bin}:/usr/bin:/bin`, PDD_FIXTURE_EXIT: String(status) }, encoding: 'utf8' });
    assert.equal(r.status, status, r.stderr); assert.ok(Buffer.byteLength(r.stdout) > 65_536);
    const captured = JSON.parse(r.stdout);
    assert.equal(captured.argv.at(-1), message); assert.equal(captured.marker, '1'); assert.equal(captured.config, root);
    assert.ok(captured.argv.includes(agent === 'codex' ? '--dangerously-bypass-approvals-and-sandbox' : '--dangerously-skip-permissions'));
  }
});

test('the real Herdr transport always targets session pdd and reports Herdr JSON errors by code', async t => {
  const root = temp(t), bin = join(root, 'bin'), log = join(root, 'calls.jsonl');
  const padding = 'x'.repeat(1024 * 1024), errorMessage = 'tab missing not found: ' + padding;
  mkdirSync(bin);
  writeFileSync(join(bin, 'herdr'), `#!${process.execPath}\nconst fs=require('node:fs');const args=process.argv.slice(2);fs.appendFileSync(${JSON.stringify(log)},JSON.stringify(args)+'\\n');
if(args.includes('missing')){process.stderr.write(JSON.stringify({error:{code:'tab_not_found',message:${JSON.stringify(errorMessage)}}}));process.exitCode=1;}
else process.stdout.write(args.includes('run')?'':JSON.stringify({result:{ok:true,padding:${JSON.stringify(padding)}}}));\n`, { mode: 0o755 });
  const path = process.env.PATH; process.env.PATH = `${bin}:${path}`; t.after(() => { process.env.PATH = path; });
  const herdr = herdrCommand();
  assert.deepEqual(await herdr(['tab', 'get', 'w1:t1']), { result: { ok: true, padding } });
  assert.deepEqual(await herdr(['pane', 'run', 'w1:p1', 'claude']), {});
  await assert.rejects(herdr(['tab', 'get', 'missing']), error => error.code === 'tab_not_found' && error.message === errorMessage);
  const failed = spawnSync(join(bin, 'herdr'), ['--session', 'pdd', 'missing'], { encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 });
  assert.equal(failed.status, 1);
  assert.ok(Buffer.byteLength(failed.stderr) > 65_536);
  assert.equal(Buffer.byteLength(failed.stderr), Buffer.byteLength(JSON.stringify({ error: { code: 'tab_not_found', message: errorMessage } })));
  assert.equal(JSON.parse(failed.stderr).error.message, errorMessage);
  for (const args of readFileSync(log, 'utf8').trim().split('\n').map(JSON.parse)) assert.deepEqual(args.slice(0, 2), ['--session', 'pdd']);
});

test('a stopped pdd server starts without agent-session markers, and pdd waits only while that server lives', async t => {
  const root = temp(t);
  const run = { repo: 'o/r', number: 3, runId: '22222222-2222-4222-8222-222222222222', workflow: 'bug', sourceRoot: root, root, commonDir: join(root, '.git'), runDir: join(root, 'run'), agent: 'claude' };
  mkdirSync(run.runDir);
  const env = { HOME: root, PATH: '/bin', CLAUDECODE: '1', CLAUDE_CODE_CHILD_SESSION: '1', CLAUDE_CODE_SESSION_ID: 'x', HERDR_ENV: '1', HERDR_SOCKET_PATH: '/default.sock', CODEX_THREAD_ID: 't', PDD_AGENT_SESSION: '1', CLAUDE_CONFIG_DIR: '/cfg' };
  let statusCalls = 0; const spawned = [];
  const herdr = async args => {
    if (args[0] === 'status') return { running: ++statusCalls > 2 };
    throw Object.assign(Error('stop here'), { code: 'stop_here' });
  };
  await assert.rejects(startChat({ run, area: 'solution', message: 'hi' }, { herdr, env, layoutDirectory: join(root, 'layout'),
    spawnServer: async serverEnv => { spawned.push(serverEnv); return new EventEmitter(); } }), error => error.code === 'stop_here');
  assert.equal(spawned.length, 1);
  assert.deepEqual(Object.keys(spawned[0]).sort(), ['CLAUDE_CONFIG_DIR', 'HOME', 'PATH']);
  const dead = new EventEmitter();
  await assert.rejects(startChat({ run, area: 'solution', message: 'hi' }, { herdr: async () => ({ running: false }), env, layoutDirectory: join(root, 'layout'),
    spawnServer: async () => { setImmediate(() => dead.emit('exit', 1)); return dead; } }), error => error.code === 'herdr_server_exited');
});

test('R9: chatCommand refuses a resume id that is not a UUID and quotes a valid one', () => {
  const id = '11111111-1111-4111-8111-111111111111';
  assert.match(chatCommand({ agent: 'codex', cwd: '/w', resumeId: id }), new RegExp(`codex resume '${id}' `));
  for (const bad of ['$(touch x)', "x'; rm -rf ~; '", '']) assert.throws(() => chatCommand({ agent: 'claude', cwd: '/w', resumeId: bad }), /session id/);
});

test('STOP1: native process liveness proves a disposable writer stopped before tab cleanup, without a live Herdr service', async t => {
  const { spawn } = await import('node:child_process');
  const { statSync } = await import('node:fs');
  const { stopChats } = await import('../src/workflow-chat.mjs');
  const root = temp(t), script = join(root, 'codex.mjs'), writes = join(root, 'writes');
  writeFileSync(script, `import {appendFileSync} from 'node:fs';setInterval(()=>appendFileSync(${JSON.stringify(writes)},'tick\\n'),10);`);
  const child = spawn(process.execPath, [script], { cwd: root, detached: true, stdio: 'ignore' });
  t.after(() => { try { process.kill(-child.pid, 'SIGKILL'); } catch {} });
  let exited = false; child.on('exit', () => { exited = true; });
  while (!exited) { try { if (statSync(writes).size > 0) break; } catch {} await new Promise(r => setTimeout(r, 10)); }
  assert.equal(exited, false);
  const calls = [], run = { runId: 'native-test', root, agent: 'codex', state: 'running', chats: [{ paneId: 'only-owned-pane', tabId: 'only-owned-tab', area: 'build' }] };
  const stopped = await stopChats(run, { herdr: async args => {
    calls.push(args);
    if (args[0] === 'pane') return { result: { process_info: { shell_pid: process.pid, foreground_process_group_id: exited ? process.pid : child.pid,
      foreground_processes: exited ? [] : [{ pid: child.pid, name: 'node', argv: [process.execPath, script], cwd: root }] } } };
    assert.deepEqual(args, ['tab', 'close', 'only-owned-tab']); assert.equal(exited, true); return {};
  } });
  assert.equal(stopped.stopped, true, stopped.warnings.join('\n')); assert.equal(exited, true);
  const finalSize = statSync(writes).size; await new Promise(r => setTimeout(r, 80)); assert.equal(statSync(writes).size, finalSize);
  assert.throws(() => process.kill(child.pid, 0), { code: 'ESRCH' });
  assert.deepEqual(calls[0], ['pane','process-info','--pane','only-owned-pane']); assert.equal(calls.at(-1)[0], 'tab');
});

for (const mode of ['unavailable','missing-pane','unconfirmed','other-worktree','changed-native','lost-stop']) {
  test(`STOP2: ${mode} cannot establish quiescence or close tabs`, async () => {
    const { stopChats } = await import('../src/workflow-chat.mjs');
    let closed = false, signals = 0, reads = 0;
    const chat = { paneId: 'owned-pane', tabId: 'owned-tab', ...(mode === 'unconfirmed' ? { startUnconfirmed: true } : {}) };
    const out = await stopChats({ root: '/owned', agent: 'codex', state: 'running', chats: [chat] }, {
      herdr: async args => {
        if (args[0] === 'tab') { closed = true; return {}; }
        if (['unavailable','missing-pane'].includes(mode)) throw Object.assign(Error(mode), { code: mode });
        return { result: { process_info: mode === 'unconfirmed' ? { shell_pid: 10, foreground_process_group_id: 10, foreground_processes: [] }
          : { shell_pid: 10, foreground_process_group_id: 20, foreground_processes: [{ pid: 20, name: 'codex', argv: ['codex'], cwd: mode === 'other-worktree' ? '/other' : '/owned' }] } } };
      },
      nativeIdentity: async () => ({ group: 20, birth: mode === 'changed-native' ? String(++reads) : 'stable' }),
      stopProcessGroup: async () => { signals++; if (mode === 'lost-stop') throw Error('lost stop receipt'); },
    });
    assert.equal(out.stopped, false); assert.equal(closed, false); assert.equal(signals, mode === 'lost-stop' ? 1 : 0);
  });
}

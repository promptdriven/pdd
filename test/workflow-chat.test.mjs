import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { EventEmitter } from 'node:events';
import { chatCommand, herdrCommand, startChat } from '../src/workflow-chat.mjs';

const temp = t => { const path = realpathSync(mkdtempSync(join(tmpdir(), "pdd-chat 'q' "))); t.after(() => rmSync(path, { recursive: true, force: true })); return path; };
// A fake native CLI that prints its argv and the marker the chat gets.
const nativeScript = `#!${process.execPath}\nprocess.stdout.write(JSON.stringify({argv:process.argv.slice(2),marker:process.env.PDD_AGENT_SESSION??null,config:process.env.CLAUDE_CONFIG_DIR??process.env.CODEX_HOME??null}));\n`;

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
  assert.match(chatCommand({ agent: 'claude', cwd, resumeId: id }), new RegExp(`claude --dangerously-skip-permissions --resume ${id}$`));
  assert.match(chatCommand({ agent: 'codex', cwd, resumeId: id }), new RegExp(`codex resume ${id} --no-daemon --dangerously-bypass-approvals-and-sandbox -c `));
});

test('the real Herdr transport always targets session pdd and reports Herdr JSON errors by code', async t => {
  const root = temp(t), bin = join(root, 'bin'), log = join(root, 'calls.jsonl');
  mkdirSync(bin);
  writeFileSync(join(bin, 'herdr'), `#!${process.execPath}\nconst fs=require('node:fs');const args=process.argv.slice(2);fs.appendFileSync(${JSON.stringify(log)},JSON.stringify(args)+'\\n');
if(args.includes('missing')){process.stderr.write(JSON.stringify({error:{code:'tab_not_found',message:'tab missing not found'}}));process.exit(1);}
process.stdout.write(args.includes('run')?'':JSON.stringify({result:{ok:true}}));\n`, { mode: 0o755 });
  const path = process.env.PATH; process.env.PATH = `${bin}:${path}`; t.after(() => { process.env.PATH = path; });
  const herdr = herdrCommand();
  assert.deepEqual(await herdr(['tab', 'get', 'w1:t1']), { result: { ok: true } });
  assert.deepEqual(await herdr(['pane', 'run', 'w1:p1', 'claude']), {});
  await assert.rejects(herdr(['tab', 'get', 'missing']), error => error.code === 'tab_not_found');
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

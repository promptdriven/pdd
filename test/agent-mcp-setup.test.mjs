import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, existsSync, symlinkSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { PassThrough } from 'node:stream';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';
import { cpSync, chmodSync } from 'node:fs';
const packageRoot = fileURLToPath(new URL('..', import.meta.url));
const pinned = { command: process.execPath, args: [join(packageRoot, 'bin/pdd.mjs'), 'mcp'] };
import { join } from 'node:path';
import { parse } from '../src/vendor/smol-toml/parse.js';
import { setupAgentMcp } from '../src/agent-mcp-setup.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

function fixture(t) {
  const home = mkdtempSync(join(tmpdir(), 'pdd-mcp-setup-'));
  t.after(() => rmSync(home, { recursive: true, force: true }));
  const env = { HOME: home, PATH: '', CODEX_HOME: join(home, 'custom-codex'), CLAUDE_CONFIG_DIR: join(home, 'custom-claude') };
  mkdirSync(env.CODEX_HOME); mkdirSync(env.CLAUDE_CONFIG_DIR); mkdirSync(join(home, '.gemini'));
  const files = [join(env.CODEX_HOME, 'config.toml'), join(env.CLAUDE_CONFIG_DIR, '.claude.json'), join(home, '.gemini/settings.json')];
  let out = '', err = '';
  const ports = { stdout: { write: text => { out += text; } }, stderr: { write: text => { err += text; } }, stdin: { isTTY: false } };
  return { home, env, files, ports, output: () => out, errors: () => err };
}
test('MCP setup previews exact scoped registrations before one explicit consent, preserving settings and repeat setup', async t => {
  const f = fixture(t);
  writeFileSync(f.files[0], '# Keep this comment\nmodel = "custom"\n[mcp_servers.other]\ncommand = "other"\n');
  writeFileSync(f.files[1], '{"theme":"dark","mcpServers":{"other":{"command":"other"}}}\n');
  writeFileSync(f.files[2], '{"theme":"light","mcpServers":{"other":{"command":"other"}}}\n');
  let asked = 0;
  assert.equal(await setupAgentMcp({ env: f.env }, { ...f.ports, confirm: () => {
    asked++;
    for (const path of f.files) assert.ok(f.output().includes(path));
    assert.ok(f.output().includes('default_tools_approval_mode = "approve"'));
    assert.ok(f.output().includes('/mcpServers/pdd'));
    assert.equal(parse(readFileSync(f.files[0], 'utf8')).mcp_servers.pdd, undefined);
    return 'y';
  } }), 0);
  assert.equal(asked, 1);
  const toml = readFileSync(f.files[0], 'utf8');
  assert.ok(toml.startsWith('# Keep this comment\nmodel = "custom"'));
  const codex = parse(toml);
  assert.equal(codex.model, 'custom'); assert.equal(codex.mcp_servers.other.command, 'other');
  assert.deepEqual({ ...codex.mcp_servers.pdd }, { ...pinned, default_tools_approval_mode: 'approve', tool_timeout_sec: 600 });
  assert.equal(codex.approval_policy, undefined);
  const claude = JSON.parse(readFileSync(f.files[1]));
  assert.equal(claude.theme, 'dark'); assert.equal(claude.mcpServers.other.command, 'other');
  assert.deepEqual(claude.mcpServers.pdd, { type: 'stdio', ...pinned });
  const gemini = JSON.parse(readFileSync(f.files[2]));
  assert.equal(gemini.theme, 'light'); assert.equal(gemini.mcpServers.pdd.trust, true);
  const before = f.files.map(path => readFileSync(path, 'utf8'));
  assert.equal(await setupAgentMcp({ env: f.env }, { ...f.ports, confirm: () => { throw Error('must not ask twice'); } }), 0);
  assert.deepEqual(f.files.map(path => readFileSync(path, 'utf8')), before);
});
test('MCP setup declines empty, n, yes, EOF and noninteractive input without creating configs', async t => {
  const f = fixture(t);
  for (const answer of ['', 'n', 'yes', undefined]) {
    assert.equal(await setupAgentMcp({ env: f.env }, { ...f.ports, confirm: () => answer }), 0);
    assert.ok(f.files.every(path => !existsSync(path)));
  }
  assert.equal(await setupAgentMcp({ env: f.env }, f.ports), 0);
  assert.ok(f.files.every(path => !existsSync(path)));
});
test('MCP setup safely refuses malformed configs, wrong roots, conflicts and symlinks before consent', async t => {
  const f = fixture(t);
  for (const [file, text] of [[f.files[0], '[broken'], [f.files[1], '{broken'], [f.files[1], '[]'], [f.files[1], '{"mcpServers":[]}'], [f.files[0], '[mcp_servers.pdd]\ncommand="different"']]) {
    writeFileSync(file, text);
    assert.equal(await setupAgentMcp({ env: f.env }, { ...f.ports, confirm: () => { throw Error('must not ask'); } }), 1);
    assert.equal(readFileSync(file, 'utf8'), text);
    rmSync(file);
  }
  const target = join(f.home, 'target'); writeFileSync(target, '{}'); symlinkSync(target, f.files[1]);
  assert.equal(await setupAgentMcp({ env: f.env }, { ...f.ports, confirm: () => 'y' }), 1);
  assert.equal(readFileSync(target, 'utf8'), '{}');
  assert.match(f.errors(), /malformed TOML/); assert.match(f.errors(), /symlink/);
  assert.equal(existsSync(f.files[0]), false);
});
test('MCP setup detects intervening config edits and applies none of its previews', async t => {
  const f = fixture(t);
  assert.equal(await setupAgentMcp({ env: f.env }, { ...f.ports, confirm: () => {
    writeFileSync(f.files[1], '{"concurrent":true}'); return 'y';
  } }), 1);
  assert.equal(existsSync(f.files[0]), false);
  assert.deepEqual(JSON.parse(readFileSync(f.files[1])), { concurrent: true });
  assert.match(f.errors(), /changed after the preview/);
});
test('pdd mcp dispatches current repo and streams without stdout diagnostics', async () => {
  let out = '', err = ''; const stdin = {}; const env = { HOME: '/unused', PATH: '' };
  const stdout = { write: text => { out += text; } }, stderr = { write: text => { err += text; } };
  assert.equal(await runPdd(['mcp'], { cwd: '/repo', env, stdin, stdout, stderr, mcpServer: { runMcp(input, ports) {
    assert.deepEqual(input, { cwd: '/repo', env }); assert.deepEqual(ports, { stdin, stdout, stderr }); return 0;
  } } }), 0);
  assert.equal(out, ''); assert.equal(err, '');
  assert.equal(await runPdd(['mcp', 'extra'], { stdout, stderr }), 2);
  assert.equal(out, '');
});

test('MCP setup respects normal agent homes and detects executables without running them', async t => {
  const f = fixture(t);
  const bin = join(f.home, 'bin'); mkdirSync(bin);
  const { chmodSync } = await import('node:fs');
  for (const name of ['codex', 'claude', 'gemini']) {
    const file = join(bin, name); writeFileSync(file, '#!/bin/sh\nexit 99\n'); chmodSync(file, 0o755);
  }
  const env = { HOME: f.home, PATH: bin };
  assert.equal(await setupAgentMcp({ env }, { ...f.ports, confirm: () => ' Y ' }), 0);
  assert.ok(existsSync(join(f.home, '.codex/config.toml')));
  assert.ok(existsSync(join(f.home, '.claude.json')));
  assert.ok(existsSync(join(f.home, '.gemini/settings.json')));
  assert.equal(existsSync(join(f.home, 'custom-codex/config.toml')), false);
});
test('MCP setup terminal EOF defaults to no without hanging or writing', async t => {
  const f = fixture(t), stdin = new PassThrough(), stdout = new PassThrough();
  stdin.isTTY = true; stdout.isTTY = true;
  const pending = setupAgentMcp({ env: f.env }, { ...f.ports, stdin, stdout });
  stdin.end();
  assert.equal(await pending, 0);
  assert.ok(f.files.every(path => !existsSync(path)));
});

test('registration pins this package with spaces despite an older pdd on PATH and serves its MCP tools', async t => {
  const f = fixture(t), bin = join(f.home, 'old bin'), pkg = join(f.home, 'alpha package');
  mkdirSync(bin); mkdirSync(pkg);
  for (const name of ['src', 'bin', 'package.json']) cpSync(join(packageRoot, name), join(pkg, name), { recursive: true });
  const old = join(bin, 'pdd'); writeFileSync(old, '#!/bin/sh\necho OLD-PDD >&2\nexit 99\n'); chmodSync(old, 0o755);
  const env = { ...f.env, PATH: bin };
  assert.equal(await setupAgentMcp({ env, packageRoot: pkg }, { ...f.ports, confirm: () => 'y' }), 0);
  const config = parse(readFileSync(f.files[0], 'utf8')).mcp_servers.pdd;
  assert.equal(config.command, process.execPath);
  assert.deepEqual(config.args, [join(pkg, 'bin/pdd.mjs'), 'mcp']);
  assert.ok(f.output().includes(JSON.stringify(join(pkg, 'bin/pdd.mjs'))));
  const child = spawn(config.command, config.args, { cwd: packageRoot, env, stdio: ['pipe', 'pipe', 'pipe'] });
  t.after(() => child.kill());
  let output = '', errors = '';
  child.stderr.on('data', value => { errors += value; });
  const received = new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(Error('MCP tools/list timed out: ' + errors)), 5000);
    child.stdout.on('data', value => {
      output += value;
      for (const line of output.split('\n').filter(Boolean)) {
        const message = JSON.parse(line);
        if (message.id === 2) { clearTimeout(timer); resolve(message); }
      }
    });
    child.on('error', error => { clearTimeout(timer); reject(error); });
    child.on('exit', code => { if (code && !output) { clearTimeout(timer); reject(Error(errors)); } });
  });
  child.stdin.write(JSON.stringify({jsonrpc:'2.0',id:1,method:'initialize',params:{protocolVersion:'2024-11-05',capabilities:{},clientInfo:{name:'pin-test',version:'1'}}}) + '\n');
  child.stdin.write(JSON.stringify({jsonrpc:'2.0',method:'notifications/initialized'}) + '\n');
  child.stdin.write(JSON.stringify({jsonrpc:'2.0',id:2,method:'tools/list',params:{}}) + '\n');
  const result = await received;
  assert.deepEqual(result.result.tools.map(tool => tool.name), ['try_open','try_state','try_run','try_check','try_save_case']);
  assert.equal(errors.includes('OLD-PDD'), false);
  child.stdin.end();
});

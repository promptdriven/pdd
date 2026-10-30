import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn, spawnSync } from 'node:child_process';
import { once } from 'node:events';
import { createConnection, createServer } from 'node:net';
import { mkdirSync, readFileSync, readdirSync, readlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { fakeRuntime, harbor, root, TOKEN } from './runtime-fake.mjs';

const supported = process.platform === 'linux' && (() => {
  try { return readlinkSync('/proc/self/fd/0') !== undefined; } catch { return false; }
})();
const options = { skip: supported ? false : 'requires Linux /proc descriptor inode inspection', timeout: 30000 };
const holders = inode => readdirSync('/proc').filter(p => /^\d+$/.test(p)).flatMap(pid => {
  try { return readdirSync(`/proc/${pid}/fd`).flatMap(fd => {
    try { return readlinkSync(`/proc/${pid}/fd/${fd}`) === inode ? [`${pid}/fd/${fd}`] : []; } catch { return []; }
  }); } catch { return []; } // Unreadable processes are outside this unprivileged test's observation.
});
async function socketInput(t) {
  const server = createServer();
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  const accepted = once(server, 'connection');
  const peer = createConnection(server.address().port, '127.0.0.1');
  const [input] = await accepted;
  t.after(() => { input.destroy(); peer.destroy(); server.close(); });
  const inode = readlinkSync(`/proc/self/fd/${input._handle.fd}`);
  assert.match(inode, /^socket:\[\d+\]$/);
  return { input, inode, close: async () => {
    const closed = once(input, 'close'); input.destroy(); await closed;
  } };
}
async function finish(child) {
  let out = '', err = '';
  child.stdout?.on('data', data => { out += data; });
  child.stderr?.on('data', data => { err += data; });
  const timer = setTimeout(() => child.kill('SIGKILL'), 20000);
  try { const [code, signal] = await once(child, 'close'); return { code, signal, out, err }; }
  finally { clearTimeout(timer); }
}
const stop = pid => { try { process.kill(pid, 'SIGKILL'); } catch (error) { if (error.code !== 'ESRCH') throw error; } };

// Warning light: current alpha already passes. This does not establish the historical SSH cause.
for (const lint of [true, false]) test(`check${lint ? ' --lint' : ''} releases caller socket despite surviving native helper`, options, async t => {
  const { sandbox, repo, home, state } = harbor(t);
  const fake = await fakeRuntime(t, entry => fake.normal(entry));
  const bin = join(sandbox, 'bin'), log = join(sandbox, 'helpers'); mkdirSync(bin);
  const git = spawnSync('which', ['git'], { encoding: 'utf8' }).stdout.trim();
  assert.ok(git);
  const prefix = `#!${process.execPath}\n`;
  // The native git boundary keeps its real argv/output. Its child deliberately survives CLI exit.
  writeFileSync(join(bin, 'git'), prefix + `
import { spawn, spawnSync } from 'node:child_process';
import { appendFileSync } from 'node:fs';
// Every git call (repo root, file list, HEAD) starts a helper that keeps whatever stdin git got.
const helper = spawn(process.execPath, ['-e', 'setTimeout(()=>{},25000)'], { stdio: [0,'ignore','ignore'], detached: true });
appendFileSync(${JSON.stringify(log)}, helper.pid+'\\n'); helper.unref();
const r = spawnSync(${JSON.stringify(git)}, process.argv.slice(2), { stdio: [0,1,2] });
process.exit(r.status ?? 1);
`, { mode: 0o755 });
  // The gh port also starts a helper that keeps whatever stdin gh got.
  writeFileSync(join(bin, 'gh'), prefix + `
import { spawn } from 'node:child_process';
import { appendFileSync } from 'node:fs';
const helper = spawn(process.execPath, ['-e', 'setTimeout(()=>{},25000)'], { stdio: [0,'ignore','ignore'], detached: true });
appendFileSync(${JSON.stringify(log)}, helper.pid+'\\n'); helper.unref();
console.log(process.argv[2] === 'auth' ? ${JSON.stringify(TOKEN)} : 'octo 4242');
`, { mode: 0o755 });
  const helpers = () => { try { return readFileSync(log, 'utf8').trim().split('\n').filter(Boolean).map(Number); } catch { return []; } };
  try {
    const socket = await socketInput(t);
    const child = spawn(process.execPath, [process.env.PDD_STDIN_TEST_CLI || join(root, 'bin/pdd.mjs'), 'check', 'place-order', ...(lint ? ['--lint'] : ['--timeout', '10'])], {
      cwd: repo, env: { ...process.env, HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: fake.origin, PATH: `${bin}:${process.env.PATH}` },
      stdio: [socket.input, 'pipe', 'pipe'],
    });
    t.after(() => { if (child.exitCode === null) child.kill('SIGKILL'); });
    const result = await finish(child);
    assert.equal(result.signal, null); assert.equal(result.code, 0, result.err);
    assert.match(result.out, lint ? /Lint: 1 of 1 tests pass/ : /Runtime check \(place-order\): ✓ 1 of 1 criterion/);
    assert.ok(helpers().length, 'native git boundary started a surviving helper');
    for (const pid of helpers()) process.kill(pid, 0);
    await socket.close();
    assert.deepEqual(holders(socket.inode), [], 'no process retains the exact original caller socket after CLI exit');
    assert.equal(fake.posts.filter(p => p.command === 'check').length, lint ? 0 : 1);
  } finally { helpers().forEach(stop); }
});

test('caller socket detector finds a deliberate original-inode holder, then clears after cleanup', options, async t => {
  const socket = await socketInput(t);
  const child = spawn(process.execPath, ['-e', "process.stdout.write('ready\\n');setTimeout(()=>{},25000)"], { stdio: [socket.input, 'pipe', 'ignore'] });
  t.after(() => { if (child.exitCode === null) child.kill('SIGKILL'); });
  await once(child.stdout, 'data');
  await socket.close();
  assert.ok(holders(socket.inode).includes(`${child.pid}/fd/0`), 'same detector sees the intentionally inherited socket');
  const closed = once(child, 'close'); child.kill('SIGKILL'); await closed;
  assert.deepEqual(holders(socket.inode), []);
});

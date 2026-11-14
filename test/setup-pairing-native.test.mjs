import { test } from 'node:test';
import assert from 'node:assert/strict';
import { generateKeyPairSync, sign } from 'node:crypto';
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runSetupPairing, pairStatus, pairOffer } from '../src/setup-pairing.mjs';
const sorted = x => x && typeof x === 'object' ? Object.fromEntries(Object.keys(x).sort().map(k => [k, sorted(x[k])])) : x;
function signed(code, privateKey, publicKey) { const body = { v: 1, login: 'ana', code, keyId: 'key1', deviceName: 'Phone', publicKey }; return { ...body, signature: sign('sha256', Buffer.from(JSON.stringify(sorted(body))), { key: privateKey, dsaEncoding: 'ieee-p1363' }).toString('base64url') }; }
test('signed offer requires confirmation and expires at ten minutes', async () => {
 const dir = mkdtempSync(join(tmpdir(), 'pdd-pair-')), env = { HOME: dir }, { privateKey, publicKey } = generateKeyPairSync('ec', { namedCurve: 'prime256v1' });
 const publicJwk = publicKey.export({ format: 'jwk' }); let time = 0, answer = true, visible = '';
 try {
  const ports = { now: () => time, login: () => 'ana', stdout: { write(x) { visible += x; } }, confirm: () => answer ? 'y' : 'n', wait: async ({ pending }) => { const file = join(dir, 'offer.json'); writeFileSync(file, JSON.stringify(signed(pending.code, privateKey, publicJwk))); assert.equal((await pairOffer({ env, messageFile: file }, ports)).exitCode, 0); } };
  const result = await runSetupPairing({ cwd: dir, env, code: 'K7Q2-9MXD', interactive: true }, ports);
  assert.equal(result.exitCode, 0); assert.match(visible, /K7Q2-9MXD/); assert.equal(JSON.parse((await pairStatus({ env }, ports)).message).paired.length, 1);
  answer = false; assert.equal((await runSetupPairing({ cwd: dir, env, code: 'NEXT-123', interactive: true }, ports)).exitCode, 1);
  assert.equal(JSON.parse((await pairStatus({ env }, ports)).message).paired.length, 1);
  answer = true; ports.confirm = () => { time = 600000; return 'y'; }; time = 0;
  assert.equal((await runSetupPairing({ cwd: dir, env, code: 'LATE-123', interactive: true }, ports)).exitCode, 1);
  assert.equal(JSON.parse((await pairStatus({ env }, ports)).message).paired.length, 1);
 } finally { rmSync(dir, { recursive: true, force: true }); }
});
test('declining optional pairing does not look up login', async () => {
 let login = false; const result = await runSetupPairing({ cwd: '.', env: {}, interactive: true }, { confirm: () => 'n', login: () => { login = true; } });
 assert.equal(result.exitCode, 0); assert.equal(login, false);
});
test('ordinary accepted pairing generates and shows a code and confirms it', async () => {
 const dir = mkdtempSync(join(tmpdir(), 'pdd-pair-')), env = { HOME: dir }, { privateKey, publicKey } = generateKeyPairSync('ec', { namedCurve: 'prime256v1' });
 let questions = 0, shown = '';
 try {
  const ports = { login: () => 'ana', random: n => Buffer.alloc(n, 0xab), stdout: { write(x) { shown += x; } }, confirm: () => { questions++; return 'y'; }, wait: async ({ pending }) => { const file = join(dir, 'offer.json'); writeFileSync(file, JSON.stringify(signed(pending.code, privateKey, publicKey.export({ format: 'jwk' })))); assert.equal((await pairOffer({ env, messageFile: file }, ports)).exitCode, 0); } };
  const result = await runSetupPairing({ cwd: dir, env, interactive: true }, ports);
  assert.equal(result.exitCode, 0); assert.equal(questions, 2); assert.match(shown, /ABABABAB/);
 } finally { rmSync(dir, { recursive: true, force: true }); }
});
test('invalid signatures are refused without storing a key', async () => {
 const dir = mkdtempSync(join(tmpdir(), 'pdd-pair-')), env = { HOME: dir }, { privateKey, publicKey } = generateKeyPairSync('ec', { namedCurve: 'prime256v1' }); let time = 0;
 try {
  const ports = { now: () => time, login: () => 'ana', wait: async ({ pending }) => { const file = join(dir, 'offer.json'), offer = signed(pending.code, privateKey, publicKey.export({ format: 'jwk' })); offer.deviceName = 'tampered'; writeFileSync(file, JSON.stringify(offer)); assert.equal((await pairOffer({ env, messageFile: file }, ports)).exitCode, 1); time = 600000; } };
  assert.equal((await runSetupPairing({ cwd: dir, env, code: 'TEST-123', interactive: true }, ports)).exitCode, 1);
  assert.deepEqual(JSON.parse((await pairStatus({ env }, ports)).message).paired, []);
 } finally { rmSync(dir, { recursive: true, force: true }); }
});
test('a separate CLI process delivers a signed offer to waiting setup', async () => {
 const { spawn, spawnSync } = await import('node:child_process');
 const dir = mkdtempSync(join(tmpdir(), 'pdd-pair-child-')), env = { ...process.env, HOME: dir, XDG_STATE_HOME: join(dir, 'state') }, { privateKey, publicKey } = generateKeyPairSync('ec', { namedCurve: 'prime256v1' });
 const module = new URL('../src/setup-pairing.mjs', import.meta.url).href, bin = new URL('../bin/pdd.mjs', import.meta.url).pathname;
 const script = `import {runSetupPairing} from ${JSON.stringify(module)}; const r=await runSetupPairing({cwd:process.cwd(),env:process.env,code:'K7Q2-9MXD',interactive:true},{stdout:process.stdout,login:()=> 'ana',confirm:()=> 'y'}); console.log(JSON.stringify(r)); process.exitCode=r.exitCode;`;
 let child;
 try {
  child = spawn(process.execPath, ['--input-type=module', '-e', script], { env, stdio: ['ignore', 'pipe', 'pipe'] });
  await new Promise((resolve, reject) => { child.stdout.once('data', resolve); child.once('error', reject); child.once('exit', code => reject(Error(`setup exited early ${code}`))); });
  const file = join(dir, 'offer.json'); writeFileSync(file, JSON.stringify(signed('K7Q2-9MXD', privateKey, publicKey.export({ format: 'jwk' }))));
  const delivered = spawnSync(process.execPath, [bin, 'pair', 'offer', '--message', file], { env, encoding: 'utf8' }); assert.equal(delivered.status, 0, delivered.stderr);
  const result = await new Promise(resolve => child.once('exit', resolve)); assert.equal(result, 0);
  const status = spawnSync(process.execPath, [bin, 'pair', 'status', '--json'], { env, encoding: 'utf8' }); assert.equal(status.status, 0, status.stderr); assert.equal(JSON.parse(status.stdout).paired.length, 1);
 } finally { child?.kill(); rmSync(dir, { recursive: true, force: true }); }
});
test('status excludes private and malformed stored key data', async () => {
 const { mkdirSync } = await import('node:fs'); const dir = mkdtempSync(join(tmpdir(), 'pdd-pair-state-')), env = { HOME: dir };
 try {
  const state = join(dir, '.local/state/pdd/pairing'); mkdirSync(state, { recursive: true });
  writeFileSync(join(state, 'keys.json'), JSON.stringify([{ login: 'ana', keyId: 'a', deviceName: 'Phone', publicKey: { kty: 'EC', crv: 'P-256', x: 'a'.repeat(43), y: 'b'.repeat(43), d: 'secret' }, token: 'secret' }]));
  const result = await pairStatus({ env }); assert.doesNotMatch(result.message, /secret|token|"d"/); assert.deepEqual(JSON.parse(result.message).paired, []);
 } finally { rmSync(dir, { recursive: true, force: true }); }
});
test('interrupt clears only the waiting invitation', async () => {
 const dir = mkdtempSync(join(tmpdir(), 'pdd-pair-int-')), env = { HOME: dir };
 try {
  const result = await runSetupPairing({ cwd: dir, env, code: 'STOP-123', interactive: true }, { login: () => 'ana', wait: async () => process.emit('SIGINT') });
  assert.equal(result.exitCode, 1); assert.deepEqual(JSON.parse((await pairStatus({ env })).message), { pending: null, paired: [] });
 } finally { rmSync(dir, { recursive: true, force: true }); }
});
test('interrupt during confirmation removes invitation without saving key', async () => {
 const dir = mkdtempSync(join(tmpdir(), 'pdd-pair-confirm-int-')), env = { HOME: dir }, { privateKey, publicKey } = generateKeyPairSync('ec', { namedCurve: 'prime256v1' });
 try {
  const ports = { login: () => 'ana', confirm: () => { process.emit('SIGINT'); return new Promise(() => {}); }, wait: async ({ pending }) => { const file = join(dir, 'offer.json'); writeFileSync(file, JSON.stringify(signed(pending.code, privateKey, publicKey.export({ format: 'jwk' })))); assert.equal((await pairOffer({ env, messageFile: file }, ports)).exitCode, 0); } };
  assert.equal((await runSetupPairing({ cwd: dir, env, code: 'STOP-123', interactive: true }, ports)).exitCode, 1);
  assert.deepEqual(JSON.parse((await pairStatus({ env })).message), { pending: null, paired: [] });
 } finally { rmSync(dir, { recursive: true, force: true }); }
});

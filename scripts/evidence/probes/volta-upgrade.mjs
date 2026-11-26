#!/usr/bin/env node
// Real Volta install + real `pdd upgrade` verification (#3628) for `release-set`.
import { execFileSync, spawn, spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { copyFileSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import http from 'node:http';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';

const [candArg] = process.argv.slice(2);
if (!candArg || !existsSync(candArg)) { console.error('Usage: volta-upgrade.mjs <candidate.tgz>'); process.exit(2); }
const candTarball = resolve(candArg);

const smokeDir = mkdtempSync(join(tmpdir(), 'pdd-volta-upgrade-'));
const home = join(smokeDir, 'home');
const state = join(smokeDir, 'state');
const voltaHome = join(smokeDir, 'volta');
mkdirSync(join(home, '.gemini', 'config'), { recursive: true });
mkdirSync(state, { recursive: true });
mkdirSync(voltaHome, { recursive: true });

const baseEnv = { ...process.env, HOME: home, PDD_STATE_DIR: state, VOLTA_HOME: voltaHome, PDD_NO_UPDATE_CHECK: '1', PATH: `${join(voltaHome, 'bin')}:${process.env.PATH}` };
const run = (cmd, args, env = baseEnv) => {
  const r = spawnSync(cmd, args, { env, encoding: 'utf8', timeout: 180_000 });
  if (r.status !== 0) throw new Error(`${cmd} ${args.join(' ')} failed (${r.status}):\n${r.stderr}\n${r.stdout}`);
  return r;
};
const runAsync = (cmd, args, env = baseEnv) => new Promise((resolvePromise, rejectPromise) => {
  const child = spawn(cmd, args, { env, stdio: ['ignore', 'pipe', 'pipe'] });
  let stdout = '', stderr = '';
  child.stdout.on('data', d => { stdout += d; });
  child.stderr.on('data', d => { stderr += d; });
  const timer = setTimeout(() => { child.kill('SIGKILL'); rejectPromise(new Error(`${cmd} ${args.join(' ')} timed out`)); }, 180_000);
  child.on('error', err => { clearTimeout(timer); rejectPromise(err); });
  child.on('close', status => {
    clearTimeout(timer);
    if (status !== 0) rejectPromise(new Error(`${cmd} ${args.join(' ')} failed (${status}):\n${stderr}\n${stdout}`));
    else resolvePromise({ status, stdout, stderr });
  });
});

let server;
try {
  run('bash', ['-c', 'curl -fsSL https://get.volta.sh | bash -s -- --skip-setup']);
  run(join(voltaHome, 'bin', 'volta'), ['install', 'node@22']);
  run(join(voltaHome, 'bin', 'volta'), ['install', '@promptdriven/pdd@latest']);

  const pddBin = join(voltaHome, 'bin', 'pdd');
  const oldVer = run(pddBin, ['--version']).stdout.trim().split(/\r?\n/)[0];
  writeFileSync(join(home, '.gemini', 'config', 'mcp_config.json'), '');
  run(pddBin, ['setup', '--yes']);

  const parse = v => String(v || '').match(/(\d+)\.(\d+)\.(\d+)/)?.slice(1).map(Number) || [0, 0, 0];
  const pkg = JSON.parse(execFileSync('tar', ['-xOf', candTarball, 'package/package.json'], { encoding: 'utf8' }));
  const [a, b] = [parse(pkg.version), parse(oldVer)];
  const newer = a[0] > b[0] || (a[0] === b[0] && (a[1] > b[1] || (a[1] === b[1] && a[2] > b[2])));
  const targetVer = newer ? pkg.version : `${b[0]}.${b[1]}.${b[2] + 1}`;
  const servedTarball = join(smokeDir, 'cand-upgrade.tgz');
  if (newer) copyFileSync(candTarball, servedTarball);
  else {
    const work = join(smokeDir, 'repack');
    mkdirSync(work, { recursive: true });
    execFileSync('tar', ['-xzf', candTarball, '-C', work]);
    pkg.version = targetVer;
    writeFileSync(join(work, 'package', 'package.json'), JSON.stringify(pkg, null, 2) + '\n');
    const skillMd = join(work, 'package', 'skills', 'pdd', 'SKILL.md');
    if (existsSync(skillMd)) {
      writeFileSync(skillMd, readFileSync(skillMd, 'utf8').replace(/^(  pdd-skills:\s*).+$/m, `$1${targetVer}`));
    }
    execFileSync('tar', ['-czf', servedTarball, '-C', work, 'package']);
  }

  const tgz = readFileSync(servedTarball);
  const shasum = createHash('sha1').update(tgz).digest('hex');
  const integrity = `sha512-${createHash('sha512').update(tgz).digest('base64')}`;
  server = http.createServer((req, res) => {
    const rawPath = (req.url || '/').split('?')[0];
    if (rawPath === '/pkg.tgz') { res.writeHead(200, { 'content-type': 'application/octet-stream' }); res.end(tgz); return; }
    const decoded = decodeURIComponent(rawPath);
    if (decoded !== '/@promptdriven/pdd' && decoded !== `/@promptdriven/pdd/${targetVer}`) {
      res.writeHead(302, { location: `https://registry.npmjs.org${req.url}` }); res.end(); return;
    }
    const { port } = server.address();
    const doc = { name: '@promptdriven/pdd', version: targetVer, dependencies: pkg.dependencies || {}, bin: pkg.bin, dist: { shasum, integrity, tarball: `http://127.0.0.1:${port}/pkg.tgz` } };
    const body = decoded === `/@promptdriven/pdd/${targetVer}` ? doc : { name: '@promptdriven/pdd', 'dist-tags': { latest: targetVer }, versions: { [targetVer]: doc } };
    res.writeHead(200, { 'content-type': 'application/json' }); res.end(JSON.stringify(body));
  });
  await new Promise(done => server.listen(0, '127.0.0.1', done));
  const { port } = server.address();
  writeFileSync(join(home, '.npmrc'), `registry=http://127.0.0.1:${port}/\n`);

  const fetchShim = join(smokeDir, 'fetch-shim.mjs');
  writeFileSync(fetchShim, `const orig = globalThis.fetch; globalThis.fetch = async (u, i) => String(u).includes('api.github.com/repos/promptdriven/pdd/releases') ? new Response(JSON.stringify([{ tag_name: 'alpha-v${targetVer}', draft: false, prerelease: false, published_at: '2026-11-25T00:00:00Z' }]), { status: 200, headers: { 'content-type': 'application/json' } }) : orig(u, i);\n`);
  const upgEnv = { ...baseEnv, NODE_OPTIONS: `--import=${fetchShim}`, npm_config_registry: `http://127.0.0.1:${port}` };
  delete upgEnv.PDD_NO_UPDATE_CHECK;

  await runAsync(pddBin, ['upgrade'], upgEnv);
  const ver = run(pddBin, ['--version']);
  if (ver.stdout.trim() !== targetVer || ver.stderr.trim() !== '') {
    throw new Error(`Volta post-upgrade --version mismatch: out=${JSON.stringify(ver.stdout)} err=${JSON.stringify(ver.stderr)} expected=${targetVer}`);
  }
  JSON.parse(readFileSync(join(home, '.gemini', 'config', 'mcp_config.json'), 'utf8'));
  const postSetup = run(pddBin, ['setup', '--upgrade']);
  if (postSetup.stdout.trim() !== '') throw new Error(`Expected empty setup --upgrade stdout, got: ${postSetup.stdout}`);
  console.log(`Volta upgrade verified: ${oldVer} -> ${targetVer}`);
} finally {
  if (server) server.close();
  rmSync(smokeDir, { recursive: true, force: true });
}

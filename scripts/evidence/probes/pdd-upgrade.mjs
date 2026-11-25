#!/usr/bin/env node
// Runs unmodified `old pdd upgrade` inside the shared sandbox, redirecting ONLY GitHub release
// metadata + npm install spec to the exact local candidate tarball. When candidate version <= old
// version (normal PR before version bump), bumps only `package/package.json` patch+1 in a temp
// copy so `old pdd upgrade` exercises the real upgrade & post-upgrade skill sync path (#3645).
import { execFileSync, spawnSync } from 'node:child_process';
import { chmodSync, existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join, resolve } from 'node:path';

const [oldCmd, candSpec, sbx] = process.argv.slice(2);
if (!oldCmd || !candSpec || !sbx) { console.error('Usage: pdd-upgrade.mjs <old-cmd> <cand-art> <sandbox>'); process.exit(2); }

if (!/\.(?:tgz|tar\.gz)$/i.test(candSpec) || !existsSync(candSpec)) {
  console.error('not-proved: in-place npm upgrade requires a .tgz candidate artifact');
  process.exit(3);
}

const parseTriple = v => String(v || '').trim().match(/(\d+)\.(\d+)\.(\d+)/)?.slice(1).map(Number) || [0, 0, 0];
const isNewer = (cand, old) => {
  const a = parseTriple(cand), b = parseTriple(old);
  return a[0] > b[0] || (a[0] === b[0] && (a[1] > b[1] || (a[1] === b[1] && a[2] > b[2])));
};

const oldVerRes = spawnSync(oldCmd, ['--version'], { encoding: 'utf8', timeout: 30_000 });
const oldVersion = (oldVerRes.stdout || '').trim().split(/\r?\n/)[0] || '0.0.0';
const pkgJson = JSON.parse(execFileSync('tar', ['-xOf', candSpec, 'package/package.json'], { encoding: 'utf8' }));
const shimDir = join(sbx, 'upgrade-shim');
mkdirSync(shimDir, { recursive: true });

let targetVersion = pkgJson.version;
let targetTarball = resolve(candSpec);
if (!isNewer(targetVersion, oldVersion)) {
  const [maj, min, pat] = parseTriple(oldVersion);
  targetVersion = `${maj}.${min}.${pat + 1}`;
  const workDir = join(shimDir, 'repack');
  mkdirSync(workDir, { recursive: true });
  execFileSync('tar', ['-xzf', candSpec, '-C', workDir]);
  pkgJson.version = targetVersion;
  writeFileSync(join(workDir, 'package', 'package.json'), JSON.stringify(pkgJson, null, 2) + '\n');
  const skillMd = join(workDir, 'package', 'skills', 'pdd', 'SKILL.md');
  if (existsSync(skillMd)) {
    const rawSkill = readFileSync(skillMd, 'utf8');
    writeFileSync(skillMd, rawSkill.replace(/^(  pdd-skills:\s*).+$/m, `$1${targetVersion}`));
  }
  targetTarball = join(shimDir, `cand-bumped-${targetVersion}.tgz`);
  execFileSync('tar', ['-czf', targetTarball, '-C', workDir, 'package']);
}
writeFileSync(join(shimDir, 'target-version.txt'), `${targetVersion}\n`);

const realNpm = execFileSync('which', ['npm'], { encoding: 'utf8' }).trim();
const npmShim = join(shimDir, 'npm');
writeFileSync(npmShim, `#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
const args = process.argv.slice(2).map(a =>
  /^(?:github:promptdriven\\/pdd|@promptdriven\\/pdd(?:@|$))/.test(a) ? ${JSON.stringify(targetTarball)} : a
);
const r = spawnSync(${JSON.stringify(realNpm)}, args, { stdio: 'inherit', env: process.env });
process.exit(r.status ?? 1);
`);
chmodSync(npmShim, 0o755);

const fetchShim = join(shimDir, 'fetch-shim.mjs');
writeFileSync(fetchShim, `
const origFetch = globalThis.fetch;
globalThis.fetch = async (url, init) => {
  if (String(url).includes('api.github.com/repos/promptdriven/pdd/releases')) {
    return new Response(JSON.stringify([{
      tag_name: 'alpha-v${targetVersion}',
      draft: false,
      prerelease: false,
      published_at: '2026-11-25T00:00:00Z',
    }]), { status: 200, headers: { 'content-type': 'application/json' } });
  }
  return origFetch(url, init);
};
`);

const env = { ...process.env, PATH: `${shimDir}:${process.env.PATH}`, NODE_OPTIONS: `--import=${fetchShim}` };
delete env.PDD_NO_UPDATE_CHECK;

const res = spawnSync(oldCmd, ['upgrade'], { env, encoding: 'utf8', timeout: 180_000 });
if (res.stdout) process.stdout.write(res.stdout);
if (res.stderr) process.stderr.write(res.stderr);
process.exit(res.status ?? 1);

#!/usr/bin/env node
// Verifies the upgraded binary reports the exact target version with clean stderr,
// synced skills, valid mcp_config.json, and a working `status --json`.
import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, readFileSync, symlinkSync } from 'node:fs';
import { delimiter, dirname, join, resolve } from 'node:path';

const [cmd, sbx] = process.argv.slice(2);
if (!cmd || !sbx) { console.error('Usage: verify-post-upgrade.mjs <pdd-cmd> <sandbox>'); process.exit(2); }

const binDir = dirname(resolve(cmd));
const nodeBinDir = join(sbx, 'upgrade-shim', 'node-bin');
mkdirSync(nodeBinDir, { recursive: true });
const nodeLink = join(nodeBinDir, 'node');
if (!existsSync(nodeLink)) symlinkSync(process.execPath, nodeLink);
const filteredPath = [binDir, nodeBinDir, ...(process.env.PATH || '').split(delimiter).filter(dir => {
  if (!dir) return false;
  const r = resolve(dir);
  if (r === binDir || r === nodeBinDir) return false;
  return !existsSync(join(dir, 'pdd')) && !existsSync(join(dir, 'pdd.cmd'));
})].join(delimiter);
const cleanEnv = { ...process.env, PATH: filteredPath, PDD_NO_UPDATE_CHECK: '1' };

const expectedVersion = readFileSync(join(sbx, 'upgrade-shim', 'target-version.txt'), 'utf8').trim();
const ver = spawnSync(cmd, ['--version'], { env: cleanEnv, encoding: 'utf8', timeout: 30_000 });
if (ver.status !== 0 || ver.stdout.trim() !== expectedVersion || ver.stderr.trim() !== '') {
  console.error(`post-upgrade --version mismatch: exit=${ver.status} out=${JSON.stringify(ver.stdout)} err=${JSON.stringify(ver.stderr)} expected=${expectedVersion}`);
  process.exit(1);
}

const home = join(sbx, 'home');
if (!existsSync(join(home, '.agents/skills/pdd/SKILL.md'))) {
  console.error('post-upgrade missing .agents/skills/pdd/SKILL.md');
  process.exit(1);
}
try {
  JSON.parse(readFileSync(join(home, '.gemini/config/mcp_config.json'), 'utf8'));
} catch (err) {
  console.error(`post-upgrade mcp_config.json invalid JSON: ${err.message}`);
  process.exit(1);
}

const st = spawnSync(cmd, ['status', '--json'], { env: cleanEnv, encoding: 'utf8', timeout: 30_000 });
if (st.status !== 0) {
  console.error(`post-upgrade status --json failed (exit ${st.status}): ${(st.stderr || '').trim()}`);
  process.exit(st.status ?? 1);
}
console.log(JSON.stringify({ upgradedTo: expectedVersion, ok: true }));

#!/usr/bin/env node
// Verifies `pdd setup --yes` on a messy HOME (0-byte mcp_config.json + retired 0.1.39 skill, #3646).
import { spawnSync } from 'node:child_process';
import { existsSync, readFileSync } from 'node:fs';
import { join } from 'node:path';

const [cmd, sbx] = process.argv.slice(2);
if (!cmd || !sbx) { console.error('Usage: setup-messy.mjs <pdd-cmd> <sandbox>'); process.exit(2); }

const home = join(sbx, 'home');
const res = spawnSync(cmd, ['setup', '--yes'], { encoding: 'utf8', timeout: 60_000 });
if (res.status !== 0) {
  console.error(`setup --yes failed (exit ${res.status}): ${(res.stderr || res.stdout || '').trim()}`);
  process.exit(res.status ?? 1);
}
if (!String(res.stdout).includes('Done!')) {
  console.error(`setup --yes missing Done! marker: ${res.stdout}`);
  process.exit(1);
}
if (!existsSync(join(home, '.agents/skills/pdd/SKILL.md'))) {
  console.error('setup --yes did not install consolidated .agents/skills/pdd/SKILL.md');
  process.exit(1);
}
if (existsSync(join(home, '.agents/skills/pdd-bug'))) {
  console.error('setup --yes did not remove retired .agents/skills/pdd-bug');
  process.exit(1);
}
try {
  JSON.parse(readFileSync(join(home, '.gemini/config/mcp_config.json'), 'utf8'));
} catch (err) {
  console.error(`mcp_config.json invalid JSON after setup: ${err.message}`);
  process.exit(1);
}
const upg = spawnSync(cmd, ['setup', '--upgrade'], { encoding: 'utf8', timeout: 60_000 });
if (upg.status !== 0) {
  console.error(`setup --upgrade failed (exit ${upg.status}): ${(upg.stderr || upg.stdout || '').trim()}`);
  process.exit(upg.status ?? 1);
}
console.log('MESSY_HOME_OK');

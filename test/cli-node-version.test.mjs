import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const bin = fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url));

// Wrong: an old Node loads pdd's modules first and fails with a raw syntax or import error.
test('NODE1: on Node older than 22 pdd prints one plain line, exits 1 and loads nothing else', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-node-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const home = join(dir, 'home'), preload = join(dir, 'old-node.mjs');
  writeFileSync(preload, `Object.defineProperty(process, 'versions', { value: { ...process.versions, node: '20.11.1' } });
Object.defineProperty(process, 'version', { value: 'v20.11.1' });\n`);
  const env = { ...process.env, HOME: home };
  delete env.CLAUDE_CONFIG_DIR;
  for (const args of [['--version'], ['workflow', 'list'], ['setup']]) {
    const result = spawnSync(process.execPath, ['--import', preload, bin, ...args], { cwd: dir, env, encoding: 'utf8', timeout: 10000 });
    assert.equal(result.status, 1, args.join(' '));
    assert.equal(result.stdout, '');
    assert.equal(result.stderr, 'pdd needs Node.js 22 or newer. You have v20.11.1. Update Node from https://nodejs.org, then run pdd again.\n');
  }
  // Nothing past the check ran: no skills were copied and setup wrote no file.
  assert.deepEqual(readdirSync(dir).sort(), ['old-node.mjs']);
  // Static imports would load before the check, so the entry may only import dynamically.
  const source = readFileSync(bin, 'utf8');
  assert.doesNotMatch(source, /^\s*import\s[^(]/m);
  assert.doesNotMatch(source, /\?\?|\?\.|^await\s/m);
});

// Wrong: the check refuses a supported Node.
test('NODE2: on Node 22 or newer pdd runs as usual', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-node-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const env = { ...process.env, HOME: join(dir, 'home') };
  delete env.CLAUDE_CONFIG_DIR;
  const result = spawnSync(process.execPath, [bin, '--version'], { cwd: dir, env, encoding: 'utf8', timeout: 10000 });
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stdout, `${JSON.parse(readFileSync(new URL('../package.json', import.meta.url), 'utf8')).version}\n`);
});

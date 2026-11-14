import { test } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, statSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { runPdd } from '../src/pdd-cli.mjs';
import { setupProject } from '../src/project-setup.mjs';
const packageRoot = resolve('.');
function stream() { return { text: '', isTTY: false, write(x) { this.text += x; } }; }
test('readiness is read-only and follows the selected block and ignore rule', async () => {
  const cwd = mkdtempSync(join(tmpdir(), 'pdd-ready-'));
  try {
    spawnSync('git', ['init', '-q', cwd]);
    const run = async () => { const stdout = stream(), stderr = stream(); const exit = await runPdd(['setup','--check','--json'], { cwd, packageRoot, stdout, stderr }); assert.equal(exit, 0); return JSON.parse(stdout.text).ready; };
    assert.equal(await run(), false);
    setupProject({ cwd, packageRoot }); writeFileSync(join(cwd, '.gitignore'), '!/.pdd/config.json\n');
    const paths = ['AGENTS.md', '.gitignore'].map(x => join(cwd, x));
    const before = paths.map(x => [readFileSync(x), statSync(x).mtimeMs]);
    assert.equal(await run(), true);
    assert.deepEqual(paths.map(x => [readFileSync(x), statSync(x).mtimeMs]), before);
    writeFileSync(paths[0], readFileSync(paths[0], 'utf8') + '<!-- pdd:start -->\n');
    assert.equal(await run(), false);
  } finally { rmSync(cwd, { recursive: true, force: true }); }
});
test('invalid setup options are refused before any setup effects', async () => {
  for (const argv of [['setup','--pair-code','bad!'], ['setup','--json']]) {
    const stdout = stream(), stderr = stream(); let called = false;
    const exit = await runPdd(argv, { stdout, stderr, stdin: stream(), checkProjectReady() { called = true; }, pathDiagnostic() { called = true; return []; }, setupSkills() { called = true; return []; } });
    assert.equal(exit, 2); assert.equal(called, false);
  }
});
test('unattended setup in a child process initializes once and repeats without writes', () => {
 const cwd = mkdtempSync(join(tmpdir(), 'pdd-unattended-'));
 try {
  spawnSync('git', ['init', '-q', cwd]);
  const cli = new URL('../src/pdd-cli.mjs', import.meta.url).href;
  const script = `import { runPdd } from ${JSON.stringify(cli)}; process.exitCode = await runPdd(['setup','--yes','--no-pair'], {cwd:process.cwd(), packageRoot:${JSON.stringify(packageRoot)}, env:process.env, pathDiagnostic:()=>[], workflowAgents:{checkWorkflowAgents:async()=>({ok:true,agent:'codex'})}, setupSkills:()=>[], setupAgentMcp:async()=>0, autopilot:{runAutopilot:async()=>({exitCode:0,message:''})}});`;
  const run = () => spawnSync(process.execPath, ['--input-type=module', '-e', script], { cwd, encoding: 'utf8', env: { ...process.env, HOME: cwd } });
  const first = run(); assert.equal(first.status, 0, first.stderr); assert.doesNotMatch(first.stdout, /\[y\/N\]|pairing code/i);
  const paths = ['AGENTS.md', '.gitignore'].map(x => join(cwd, x)), before = paths.map(x => [readFileSync(x), statSync(x).mtimeMs]);
  const second = run(); assert.equal(second.status, 0, second.stderr); assert.equal(second.stdout, ''); assert.deepEqual(paths.map(x => [readFileSync(x), statSync(x).mtimeMs]), before);
 } finally { rmSync(cwd, { recursive: true, force: true }); }
});

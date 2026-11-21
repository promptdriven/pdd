import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  analyzeArchitecture,
  checkArchitecture,
  classifyLayer,
  formatFailureDiagnostic,
  parseJsModuleEdges,
  resolveImportSpecifier,
} from '../scripts/check-architecture.mjs';
import { parseOfflineLintPayload, replaceRequired } from '../scripts/corpus-check.mjs';

const REPO_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const CHECKER_SCRIPT = join(REPO_ROOT, 'scripts/check-architecture.mjs');

function writeRepoFile(root, rel, content) {
  const abs = join(root, rel);
  mkdirSync(dirname(abs), { recursive: true });
  writeFileSync(abs, content, 'utf8');
}

function runChecker(args) {
  return spawnSync(process.execPath, [CHECKER_SCRIPT, ...args], {
    cwd: REPO_ROOT,
    encoding: 'utf8',
  });
}

test('G7 parser extracts static imports, re-exports, dynamic import(), createRequire, and path-string spawns while ignoring comments, regexes, and interpolated templates', () => {
  const sample = [
    '#!/usr/bin/env node',
    "import a from './a.mjs';",
    "import {\n  b,\n  c,\n} from '../shared/util.mjs';",
    "export * from './reexp-star.mjs';",
    "export { x } from './reexp-named.mjs';",
    "import { createRequire } from 'node:module';",
    "import { spawn, execFileSync } from 'node:child_process';",
    "import { join } from 'node:path';",
    'const req = createRequire(import.meta.url);',
    "const mod1 = req('./cjs-helper.mjs');",
    "const mod2 = createRequire(import.meta.url)('./direct-req.mjs');",
    "const dyn = await import('./lazy.mjs');",
    'const dynTpl = await import(`./static-tpl.mjs`);',
    'const ignoredDyn = await import(`./${name}.mjs`);',
    '// import fake from "./commented.mjs";',
    '/* export * from "./block-comment.mjs"; */',
    'const re = /import "not-a-dep.mjs"/g;',
    'const doc = `import x from "./template-prose-${a}.mjs"`;',
    "const entryPath = join(root, 'src', 'autopilot', 'worker.mjs');",
    "spawn(process.execPath, [entryPath]);",
    "execFileSync('node', ['bin/pdd.mjs', 'status']);",
    'void a; void b; void c; void mod1; void mod2; void dyn; void dynTpl; void ignoredDyn; void re; void doc;',
  ].join('\n');

  const { imports, spawns } = parseJsModuleEdges(sample, 'src/core/sample.mjs');
  assert.deepEqual(
    imports.map(e => [e.kind, e.specifier]),
    [
      ['static-import', './a.mjs'],
      ['static-import', '../shared/util.mjs'],
      ['reexport', './reexp-star.mjs'],
      ['reexport', './reexp-named.mjs'],
      ['static-import', 'node:module'],
      ['static-import', 'node:child_process'],
      ['static-import', 'node:path'],
      ['create-require', './cjs-helper.mjs'],
      ['create-require', './direct-req.mjs'],
      ['dynamic-import', './lazy.mjs'],
      ['dynamic-import', './static-tpl.mjs'],
    ],
  );
  assert.deepEqual(
    spawns.map(s => [s.fn, s.target]),
    [
      ['spawn', 'src/autopilot/worker.mjs'],
      ['execFileSync', 'bin/pdd.mjs'],
    ],
  );
});

test('G7 real repository check passes cleanly against scripts/architecture-ratchet.json and --report outputs live layer LOC & cycles', () => {
  const result = checkArchitecture({ root: REPO_ROOT });
  assert.equal(result.ok, true, result.failures.map(f => formatFailureDiagnostic(f)).join('\n\n'));
  assert.equal(result.ratchetExists, true);
  assert.equal(result.failures.length, 0);
  assert.equal(result.analysis.findings.filter(f => f.rule === 'unmapped-layer').length, 0);
  assert.equal(classifyLayer('src/shared/git-context.mjs'), 'shared');
  assert.equal(classifyLayer('src/core/lint/project-lint.mjs'), 'core');
  assert.equal(classifyLayer('src/cli/pdd-cli.mjs'), 'cli');
  assert.equal(classifyLayer('src/autopilot/ai-lint.mjs'), 'autopilot');
  assert.equal(classifyLayer('bin/pdd-codex.mjs'), 'accounts');

  const cliCheck = runChecker([]);
  assert.equal(cliCheck.status, 0, cliCheck.stderr);
  assert.match(cliCheck.stdout, /Architecture check PASSED: 0 new violations/);

  const cliReport = runChecker(['--report']);
  assert.equal(cliReport.status, 0, cliReport.stderr);
  assert.match(cliReport.stdout, /G7 Architecture Report/);
  assert.match(cliReport.stdout, /Cycles \(Tarjan SCCs\):/);
  assert.match(cliReport.stdout, /Legacy-workflow imports:/);
  assert.match(cliReport.stdout, /Ratchet baseline -> current:/);

  const reportJson = JSON.parse(execFileSync(process.execPath, [CHECKER_SCRIPT, '--report', '--json'], { cwd: REPO_ROOT, encoding: 'utf8' }));
  assert.equal(reportJson.ok, true);
  assert.ok(reportJson.files >= 100);
  assert.ok(reportJson.totalLoc > 50000);
  assert.equal(reportJson.newFailureCount, 0);
});

test('G7 Ratchet Control 1: existing baseline debt passes (and remains stable across benign line shifts)', (t) => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-g7-ctrl1-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const ratchetPath = join(dir, 'ratchet.json');

  writeRepoFile(dir, 'package.json', JSON.stringify({ name: 'fixture', dependencies: {} }));
  writeRepoFile(dir, 'src/shared/util.mjs', 'export const id = x => x;\n');
  writeRepoFile(dir, 'src/autopilot/worker.mjs', "import { id } from '../shared/util.mjs';\nexport const run = () => id(1);\n");
  // Existing debt: upward layer import core -> autopilot
  writeRepoFile(dir, 'src/core/engine.mjs', "import { run } from '../autopilot/worker.mjs';\nexport const exec = () => run();\n");
  // Existing debt: circular import in core
  writeRepoFile(dir, 'src/core/cyc-a.mjs', "import { b } from './cyc-b.mjs';\nexport const a = () => b;\n");
  writeRepoFile(dir, 'src/core/cyc-b.mjs', "import { a } from './cyc-a.mjs';\nexport const b = () => a;\n");

  const writeRes = runChecker(['--root', dir, '--ratchet', ratchetPath, '--write-ratchet']);
  assert.equal(writeRes.status, 0, writeRes.stderr);
  const ratchet = JSON.parse(readFileSync(ratchetPath, 'utf8'));
  assert.equal(ratchet.entries.length, 2);

  // Check mode passes cleanly on baseline debt.
  const pass1 = runChecker(['--root', dir, '--ratchet', ratchetPath]);
  assert.equal(pass1.status, 0, pass1.stderr);

  // Adding blank lines/comments shifts line numbers without altering semantic anchors -> still passes!
  writeRepoFile(dir, 'src/core/engine.mjs', "\n\n// benign comment\nimport { run } from '../autopilot/worker.mjs';\nexport const exec = () => run();\n");
  const pass2 = runChecker(['--root', dir, '--ratchet', ratchetPath]);
  assert.equal(pass2.status, 0, pass2.stderr);
});

test('G7 Ratchet Control 2: new upward import, cycle, dynamic/reexport/createRequire, path-string spawn, or semantic-anchor swap HARD FAILS exit 1 with 4-part diagnostic', (t) => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-g7-ctrl2-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const ratchetPath = join(dir, 'ratchet.json');

  writeRepoFile(dir, 'package.json', JSON.stringify({ name: 'fixture', dependencies: {} }));
  writeRepoFile(dir, 'src/shared/util.mjs', 'export const id = x => x;\n');
  writeRepoFile(dir, 'src/autopilot/worker.mjs', 'export const run = () => 1;\n');
  writeRepoFile(dir, 'src/autopilot/other.mjs', 'export const other = () => 2;\n');
  writeRepoFile(dir, 'src/core/engine.mjs', "import { run } from '../autopilot/worker.mjs';\nexport const exec = () => run();\n");
  writeRepoFile(dir, 'src/cli/main.mjs', "import { exec } from '../core/engine.mjs';\nexport const main = () => exec();\n");

  assert.equal(runChecker(['--root', dir, '--ratchet', ratchetPath, '--write-ratchet']).status, 0);

  // 2A. Semantic-anchor swap: fix worker import in engine.mjs while adding OTHER illegal import (same total count 1 -> 1) MUST FAIL!
  writeRepoFile(dir, 'src/core/engine.mjs', "import { other } from '../autopilot/other.mjs';\nexport const exec = () => other();\n");
  const swapRes = runChecker(['--root', dir, '--ratchet', ratchetPath]);
  assert.equal(swapRes.status, 1, 'swapping one violation for a different semantic anchor must HARD FAIL exit 1');
  assert.match(swapRes.stderr, /ERROR \[layer-boundary\] src\/core\/engine\.mjs:1/);
  assert.match(swapRes.stderr, /Invariant:/);
  assert.match(swapRes.stderr, /Fix:/);
  assert.match(swapRes.stderr, /Rerun: node scripts\/check-architecture\.mjs/);

  // Restore baseline engine.mjs, then introduce new upward import shared -> core + new cycle + createRequire + path-string spawn!
  writeRepoFile(dir, 'src/core/engine.mjs', "import { run } from '../autopilot/worker.mjs';\nexport const exec = () => run();\n");
  writeRepoFile(dir, 'src/shared/util.mjs', [
    "import { exec } from '../core/engine.mjs';",
    "import { spawn } from 'node:child_process';",
    "spawn(process.execPath, ['src/autopilot/worker.mjs']);",
    'export const id = () => exec();',
  ].join('\n') + '\n');
  writeRepoFile(dir, 'src/core/alpha.mjs', "export { beta } from './beta.mjs';\nexport const alpha = 1;\n");
  writeRepoFile(dir, 'src/core/beta.mjs', "import { createRequire } from 'node:module';\nconst req = createRequire(import.meta.url);\nexport const beta = req('./alpha.mjs');\n");

  const failRes = runChecker(['--root', dir, '--ratchet', ratchetPath]);
  assert.equal(failRes.status, 1);
  assert.match(failRes.stderr, /ERROR \[layer-boundary\] src\/shared\/util\.mjs:1/);
  assert.match(failRes.stderr, /ERROR \[path-string-spawn\] src\/shared\/util\.mjs:3/);
  assert.match(failRes.stderr, /ERROR \[circular-import\] src\/core\/alpha\.mjs:1/);
  assert.match(failRes.stderr, /Rerun: node scripts\/check-architecture\.mjs/);
});

test('G7 Ratchet Control 3: shrinking the ratchet locks in resolved debt so reintroducing a fixed violation HARD FAILS exit 1', (t) => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-g7-ctrl3-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const ratchetPath = join(dir, 'ratchet.json');

  writeRepoFile(dir, 'package.json', JSON.stringify({ name: 'fixture', dependencies: {} }));
  writeRepoFile(dir, 'src/shared/util.mjs', 'export const id = x => x;\n');
  writeRepoFile(dir, 'src/autopilot/worker.mjs', 'export const run = () => 1;\n');
  writeRepoFile(dir, 'src/core/engine.mjs', "import { run } from '../autopilot/worker.mjs';\nexport const exec = () => run();\n");

  // 1. Freeze baseline debt (1 violation)
  assert.equal(runChecker(['--root', dir, '--ratchet', ratchetPath, '--write-ratchet']).status, 0);
  assert.equal(checkArchitecture({ root: dir, ratchetPath }).ratchetTotal, 1);

  // 2. Fix the upward import -> check passes AND reports shrinkage of 1!
  writeRepoFile(dir, 'src/core/engine.mjs', "import { id } from '../shared/util.mjs';\nexport const exec = () => id(1);\n");
  const shrunkCheck = checkArchitecture({ root: dir, ratchetPath });
  assert.equal(shrunkCheck.ok, true);
  assert.equal(shrunkCheck.shrunkCount, 1);
  const shrunkCli = runChecker(['--root', dir, '--ratchet', ratchetPath]);
  assert.equal(shrunkCli.status, 0, shrunkCli.stderr);
  assert.match(shrunkCli.stdout, /Ratchet can shrink by 1 resolved item/);

  // 3. Shrink the ratchet monotonically to 0 debt entries
  assert.equal(runChecker(['--root', dir, '--ratchet', ratchetPath, '--write-ratchet']).status, 0);
  assert.equal(checkArchitecture({ root: dir, ratchetPath }).ratchetTotal, 0);

  // 4. Reintroduce the exact same upward import -> MUST HARD FAIL exit 1!
  writeRepoFile(dir, 'src/core/engine.mjs', "import { run } from '../autopilot/worker.mjs';\nexport const exec = () => run();\n");
  const reintroRes = runChecker(['--root', dir, '--ratchet', ratchetPath]);
  assert.equal(reintroRes.status, 1, 'reintroducing a previously fixed violation after ratchet shrink must fail exit 1');
  assert.match(reintroRes.stderr, /ERROR \[layer-boundary\] src\/core\/engine\.mjs:1/);
  assert.match(reintroRes.stderr, /Invariant:/);
  assert.match(reintroRes.stderr, /Fix:/);
  assert.match(reintroRes.stderr, /Rerun: node scripts\/check-architecture\.mjs/);
  assert.equal(analyzeArchitecture({ root: dir }).findings.length, 1);
});

test('G7 + corpus-check cross-family review regressions (Astra #5-#8): semicolon-free export, aliases, git non-spawn, query/hash + unresolved fail-closed, ratchet growth refusal, intra-SCC edge/self-import, and corpus fail-closed', (t) => {
  // #5: Semicolon-free `export { f }\nawait import('./x.mjs')`, aliased createRequire/fork, and git diff non-spawn.
  const edgeCases = [
    "import { createRequire as mkReq } from 'node:module'",
    "import { fork as spawnChild, execFileSync } from 'node:child_process'",
    'const r = mkReq(import.meta.url)',
    "r('./via-alias.mjs')",
    "mkReq(import.meta.url)('./via-direct-alias.mjs')",
    'const f = 1',
    'export { f }',
    "await import('./after-local-export.mjs')",
    "spawnChild('src/autopilot/worker.mjs')",
    "execFileSync('git', ['diff', '--', 'src/core/foo.mjs'])",
    "execFileSync(process.execPath, ['bin/pdd.mjs', 'status'])",
  ].join('\n');
  const parsed = parseJsModuleEdges(edgeCases, 'src/core/edge.mjs');
  assert.deepEqual(
    parsed.imports.map(e => [e.kind, e.specifier]),
    [
      ['static-import', 'node:module'],
      ['static-import', 'node:child_process'],
      ['create-require', './via-alias.mjs'],
      ['create-require', './via-direct-alias.mjs'],
      ['dynamic-import', './after-local-export.mjs'],
    ],
  );
  assert.deepEqual(
    parsed.spawns.map(s => [s.fn, s.target]),
    [
      ['fork', 'src/autopilot/worker.mjs'],
      ['execFileSync', 'bin/pdd.mjs'],
    ],
    'git diff -- src/... must NEVER be flagged while aliased fork and node spawn ARE caught',
  );

  // #6: Strip ?query and #hash on relative imports, and fail closed on unresolved local relative imports!
  const fileSet = new Set(['src/core/a.mjs', 'src/shared/util.mjs']);
  assert.deepEqual(resolveImportSpecifier('src/core/a.mjs', '../shared/util.mjs?bust=1', fileSet), { kind: 'repo', target: 'src/shared/util.mjs' });
  assert.deepEqual(resolveImportSpecifier('src/core/a.mjs', '../shared/util.mjs#frag', fileSet), { kind: 'repo', target: 'src/shared/util.mjs' });
  assert.deepEqual(resolveImportSpecifier('src/core/a.mjs', './missing.mjs', fileSet), { kind: 'missing-local', target: 'src/core/missing.mjs' });

  // #6 & #7 end-to-end on temp fixture: unresolved local import fails closed, --write-ratchet refuses growth without --allow-growth,
  // and adding an intra-SCC edge OR self-import inside an already-ratcheted SCC fails exit 1!
  const dir = mkdtempSync(join(tmpdir(), 'pdd-g7-astra-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const ratchetPath = join(dir, 'ratchet.json');

  writeRepoFile(dir, 'package.json', JSON.stringify({ name: 'fixture', dependencies: {} }));
  writeRepoFile(dir, 'src/shared/util.mjs', 'export const ok = 1;\n');
  writeRepoFile(dir, 'src/core/a.mjs', "import { b } from './b.mjs?v=1';\nexport const a = b;\n");
  writeRepoFile(dir, 'src/core/b.mjs', "import { c } from './c.mjs#hash';\nexport const b = c;\n");
  writeRepoFile(dir, 'src/core/c.mjs', "import { a } from './a.mjs';\nexport const c = a;\n");

  // Initial ratchet captures the 3-node SCC (a->b, b->c, c->a)
  assert.equal(runChecker(['--root', dir, '--ratchet', ratchetPath, '--write-ratchet']).status, 0);
  assert.equal(runChecker(['--root', dir, '--ratchet', ratchetPath]).status, 0);

  // Adding a NEW intra-SCC edge (b -> a) inside the ALREADY-ratcheted SCC MUST FAIL exit 1!
  writeRepoFile(dir, 'src/core/b.mjs', "import { c } from './c.mjs#hash';\nimport { a } from './a.mjs';\nexport const b = c + a;\n");
  const intraRes = runChecker(['--root', dir, '--ratchet', ratchetPath]);
  assert.equal(intraRes.status, 1, 'adding a new intra-SCC edge must fail exit 1');
  assert.match(intraRes.stderr, /ERROR \[circular-import\]/);

  // --write-ratchet WITHOUT --allow-growth MUST REFUSE to grow the ratchet (exit 1) and keep ratchet unchanged!
  const beforeRatchet = readFileSync(ratchetPath, 'utf8');
  const growRefused = runChecker(['--root', dir, '--ratchet', ratchetPath, '--write-ratchet']);
  assert.equal(growRefused.status, 1, '--write-ratchet must refuse growth unless --allow-growth is passed');
  assert.match(growRefused.stderr, /ERROR \[ratchet-growth\]/);
  assert.equal(readFileSync(ratchetPath, 'utf8'), beforeRatchet);

  // Restore b.mjs, then add a self-import inside c.mjs -> MUST FAIL exit 1!
  writeRepoFile(dir, 'src/core/b.mjs', "import { c } from './c.mjs#hash';\nexport const b = c;\n");
  writeRepoFile(dir, 'src/core/c.mjs', "import { a } from './a.mjs';\nimport './c.mjs';\nexport const c = a;\n");
  const selfRes = runChecker(['--root', dir, '--ratchet', ratchetPath]);
  assert.equal(selfRes.status, 1, 'self-import inside existing SCC must fail exit 1');
  assert.match(selfRes.stderr, /Self-import cycle detected/);

  // Restore c.mjs, then add an unresolved local relative import -> MUST FAIL CLOSED exit 1!
  writeRepoFile(dir, 'src/core/c.mjs', "import { a } from './a.mjs';\nexport const c = a;\n");
  writeRepoFile(dir, 'src/shared/util.mjs', "import './does-not-exist.mjs';\nexport const ok = 1;\n");
  const unresolvedRes = runChecker(['--root', dir, '--ratchet', ratchetPath]);
  assert.equal(unresolvedRes.status, 1, 'unresolved relative import must fail closed exit 1');
  assert.match(unresolvedRes.stderr, /ERROR \[unresolved-local-import\] src\/shared\/util\.mjs:1/);

  // #8: corpus-check fail-closed payload validation & non-zero seed replacement guard.
  assert.equal(parseOfflineLintPayload('', 0).parsedOk, false);
  assert.equal(parseOfflineLintPayload('not json', 0).parsedOk, false);
  assert.equal(parseOfflineLintPayload('{"exit_code":0}', 0).parsedOk, false);
  assert.equal(parseOfflineLintPayload('{"exit_code":1,"problems":[],"warnings":[]}', 0).parsedOk, false);
  assert.equal(parseOfflineLintPayload('{"exit_code":0,"problems":[],"warnings":[]}', 0).parsedOk, true);
  assert.throws(() => replaceRequired('hello world', '`missing`', '`replacement`', 'missing-seed'), /matched 0 times/);
  assert.deepEqual(replaceRequired('use `foo` and `foo`', /`foo`/g, '`bar`', 'foo-seed'), { text: 'use `bar` and `bar`', count: 2 });
});

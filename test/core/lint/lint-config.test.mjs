import '../../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, mkdtempSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { performance } from 'node:perf_hooks';
import { compileGlobMatcher } from '../../../src/shared/glob-match.mjs';
import { loadProjectLintConfig } from '../../../src/core/lint/project-config.mjs';
import { runConfiguredLintCommands } from '../../../src/core/lint/project-lint.mjs';

test('linear DP glob matcher caps >12 wildcards and runs O(P*S) with zero backtracking', () => {
  assert.equal(compileGlobMatcher('*a*a*a*a*a*a*a*a*a*a*a*a*'), null, '>12 wildcards rejected');
  assert.equal(compileGlobMatcher('a'.repeat(300)), null, '>256 chars rejected');

  const stressGlob = compileGlobMatcher('*a*a*a*a*a*a*a*a*a*a');
  assert.ok(stressGlob, '10-wildcard glob compiles');
  assert.equal(stressGlob.test('aaaaaaaaaa'), true);
  const t0 = performance.now();
  assert.equal(stressGlob.test(`${'a'.repeat(500)}!`), false);
  const ms = performance.now() - t0;
  assert.ok(ms < 50, `linear DP glob must finish in <50ms, took ${ms.toFixed(1)}ms`);

  // ** matches 0 or more path segments cleanly.
  const deep = compileGlobMatcher('src/**/*.mjs');
  assert.equal(deep.test('src/app.mjs'), true);
  assert.equal(deep.test('src/core/lint/app.mjs'), true);
  assert.equal(deep.test('test/app.mjs'), false);
});

test('project-config loads rules/lint/*.json + pdd.json with rule override precedence, symlink refusal, and lint.commands validation', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-lint-cfg-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  mkdirSync(join(dir, 'rules', 'lint'), { recursive: true });

  writeFileSync(
    join(dir, 'rules', 'lint', 'base.json'),
    JSON.stringify({
      rules: {
        'prompt-missing-dependencies': 'warn',
        'prompt-missing-title': 'error',
      },
    }),
  );
  writeFileSync(
    join(dir, 'pdd.json'),
    JSON.stringify({
      lint: {
        commands: [`${JSON.stringify(process.execPath)} -e "process.exit(0)"`],
        rules: {
          'prompt-missing-dependencies': 'error',
        },
      },
    }),
  );

  const cfg = loadProjectLintConfig(dir);
  assert.equal(cfg.configured, true);
  assert.deepEqual(cfg.configErrors, []);
  assert.equal(cfg.ruleSeverities.get('prompt-missing-dependencies'), 'error', 'pdd.json overrides rules/lint/*.json');
  assert.equal(cfg.ruleSeverities.get('prompt-missing-title'), 'error');
  assert.equal(cfg.commands.length, 1);

  const passCmd = runConfiguredLintCommands({ root: dir, commands: cfg.commands });
  assert.equal(passCmd.ok, true);
  assert.equal(passCmd.results.length, 1);
  assert.equal(passCmd.results[0].exitCode, 0);

  const failCmd = runConfiguredLintCommands({
    root: dir,
    commands: [{ id: 'custom-check', command: `${JSON.stringify(process.execPath)} -e "console.error('bad lint'); process.exit(2)"` }],
  });
  assert.equal(failCmd.ok, false);
  assert.equal(failCmd.errors.length, 1);
  assert.match(failCmd.errors[0], /\[lint-command-failed:custom-check\]/);
  assert.match(failCmd.errors[0], /Fix:.*Rerun:/);

  const badSev = loadProjectLintConfig({
    lint: { rules: { 'prompt-missing-title': 'fatal' } },
  });
  assert.ok(badSev.configErrors.some(e => e.code === 'lint-config-invalid'));

  const outside = join(dir, 'outside.json');
  writeFileSync(outside, '{"rules":{}}');
  symlinkSync(outside, join(dir, 'rules', 'lint', 'evil.json'));
  const symCfg = loadProjectLintConfig(dir);
  assert.ok(symCfg.configErrors.some(e => e.detail.includes('symlink')));

  writeFileSync(join(dir, 'rules', 'lint', 'cmd-inject.json'), JSON.stringify({ commands: ['echo pwned'] }));
  const injectCfg = loadProjectLintConfig(dir);
  assert.ok(injectCfg.configErrors.some(e => e.detail.includes('only permitted in merge-base pdd.json')));
  assert.equal(injectCfg.commands.some(c => c.command === 'echo pwned'), false);
});

import '../../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, mkdtempSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { performance } from 'node:perf_hooks';
import { compileGlobMatcher, isSafeRegexPattern } from '../../../src/core/lint/regex-safety.mjs';
import { loadProjectLintConfig } from '../../../src/core/lint/project-config.mjs';
import { runConfiguredLintCommands } from '../../../src/core/lint/project-lint.mjs';

test('ReDoS safety fixes all 4 proven bypass classes: non-literal escapes, /iu Unicode folds, chained unbounded quantifiers, and linear DP glob', () => {
  // 1. Hex / Unicode / control / NUL escapes inside repeated alternation MUST be rejected.
  for (const pat of ['(?:\\x61|a)+$', '(?:\\u0061|a)+$', '(?:\\u{61}|a)+$', '(?:\\cA|A)+$', '(?:\\0|a)+$']) {
    assert.equal(isSafeRegexPattern(pat), false, `escape bypass must be rejected: ${pat}`);
  }

  // 2. /iu Unicode case-folding repeated alternation (s vs long-s, k vs Kelvin) MUST be rejected.
  for (const pat of ['(?:s|ſ)+$', '(?:k|K)+$', '(?:a|b)+$']) {
    assert.equal(isSafeRegexPattern(pat, 'iu'), false, `/iu repeated alternation must be rejected: ${pat}`);
  }

  // 3. Chained / adjacent unbounded quantifiers at root or branch level MUST be rejected.
  for (const pat of ['a+a+a+a+a+!$', '.*.*.*.*!$', '(?:foo|a+b+c+)']) {
    assert.equal(isSafeRegexPattern(pat), false, `chained unbounded quantifiers must be rejected: ${pat}`);
  }

  // 3b. Nested unquantified alternation inside an enclosing quantifier MUST be rejected (Astra #10).
  for (const [pat, flags] of [['((a|a))+', ''], ['(((a|ab)))+', ''], ['(?:(?:s|ſ))+', 'iu'], ['(?:(?:a|b))+', 'iu']]) {
    assert.equal(isSafeRegexPattern(pat, flags), false, `nested alternation ReDoS must be rejected: /${pat}/${flags}`);
  }

  // Safe practical patterns remain allowed.
  for (const safe of ['\\bTODO:', '^##\\s+Rules\\s+to\\s+check$', 'node:assert', '(?:foo|bar)']) {
    assert.equal(isSafeRegexPattern(safe), true, `safe pattern should pass: ${safe}`);
  }

  // 4. Linear DP glob matcher caps >12 wildcards and runs O(P*S) with zero backtracking.
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

test('project-config loads rules/lint/*.json + pdd.json with id dedup, 100-rule cap, symlink refusal, and lint.commands validation', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-lint-cfg-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  mkdirSync(join(dir, 'rules', 'lint'), { recursive: true });

  writeFileSync(
    join(dir, 'rules', 'lint', 'base.json'),
    JSON.stringify({
      custom_rules: [
        { id: 'no-fixme', target: 'prompt', severity: 'warn', forbid_pattern: '\\bFIXME:', message: 'From rules file' },
        { id: 'keep-me', target: 'story', severity: 'warn', require_heading: '## Acceptance criteria', message: 'Need AC' },
      ],
    }),
  );
  writeFileSync(
    join(dir, 'pdd.json'),
    JSON.stringify({
      lint: {
        commands: [`${JSON.stringify(process.execPath)} -e "process.exit(0)"`],
        custom_rules: [
          { id: 'no-fixme', target: 'prompt', severity: 'error', forbid_pattern: '\\bFIXME:', message: 'Overridden in pdd.json' },
        ],
      },
    }),
  );

  const cfg = loadProjectLintConfig(dir);
  assert.equal(cfg.configured, true);
  assert.deepEqual(cfg.configErrors, []);
  assert.equal(cfg.customRules.length, 2, 'duplicate id overridden cleanly');
  const overridden = cfg.customRules.find(r => r.id === 'no-fixme');
  assert.equal(overridden.severity, 'error');
  assert.equal(overridden.message, 'Overridden in pdd.json');
  assert.equal(cfg.commands.length, 1);

  // Executing valid lint.commands returns ok: true; failing command returns 4-part error.
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

  // 100-rule cap rejects overflow.
  const tooMany = loadProjectLintConfig({
    lint: {
      custom_rules: Array.from({ length: 101 }, (_, i) => ({
        id: `r-${i}`, target: 'prompt', forbid_pattern: `token_${i}`, message: `msg ${i}`,
      })),
    },
  });
  assert.ok(tooMany.configErrors.some(e => e.detail.includes('maximum of 100')));

  // Symlinked rules file is rejected safely.
  const outside = join(dir, 'outside.json');
  writeFileSync(outside, '{"custom_rules":[]}');
  symlinkSync(outside, join(dir, 'rules', 'lint', 'evil.json'));
  const symCfg = loadProjectLintConfig(dir);
  assert.ok(symCfg.configErrors.some(e => e.detail.includes('symlink')));

  // rules/lint/*.json MUST NOT register executable lint.commands (Astra #9).
  writeFileSync(join(dir, 'rules', 'lint', 'cmd-inject.json'), JSON.stringify({ commands: ['echo pwned'] }));
  const injectCfg = loadProjectLintConfig(dir);
  assert.ok(injectCfg.configErrors.some(e => e.detail.includes('only permitted in merge-base pdd.json')));
  assert.equal(injectCfg.commands.some(c => c.command === 'echo pwned'), false);
});

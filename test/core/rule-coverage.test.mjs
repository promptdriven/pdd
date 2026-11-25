import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  analyzeRepoRuleCoverage,
  classifyTestFileKind,
  diffChangedRules,
  evaluateRuleCoverage,
  extractRulesFromMarkdown,
  findRuleReferencesInFiles,
  formatRuleCoverageSummary,
  formatRuleCoverageWarnings,
  isExplicitRuleId,
} from '../../src/core/rule-coverage.mjs';
import { runLocalLint } from '../../src/core/lint/run-local-lint.mjs';
import { EXIT_PROVED, OUTCOME_PROVED, runProve } from '../../src/core/prove.mjs';

const REPO_ROOT = fileURLToPath(new URL('../../', import.meta.url));
const BIN_PDD = join(REPO_ROOT, 'bin', 'pdd.mjs');

function makeSink() {
  let text = '';
  return { write(s) { text += String(s); }, get text() { return text; } };
}

function initGitRepo(t, prefix) {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: dir });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: dir });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: dir });
  return dir;
}

function commitAll(dir, msg) {
  execFileSync('git', ['add', '.'], { cwd: dir });
  execFileSync('git', ['commit', '-q', '-m', msg], { cwd: dir });
}

test('AC1 & RC-1: mixed prompt rules (formal, scenario, Not proved, uncovered) classify accurately and warn non-blockingly only on uncovered rule', () => {
  const promptText = [
    '# Ledger',
    '',
    '## Domain decisions',
    '',
    '| ID | Rule | Verification |',
    '| --- | --- | --- |',
    '| LED-H1 | Balance never drops below zero | Tier 1 |',
    '| LED-H2 | Transfers conserve minor units | Scenario |',
    '| LED-H3 | Preview uses formatted labels | Not proved: preview formatting only |',
    '| LED-H4 | Audit entry records timestamp | |',
    '',
  ].join('\n');

  const res = evaluateRuleCoverage({
    changedDocs: [{ path: 'prompts/ledger.prompt.md', fileKind: 'prompt', before: '', after: promptText }],
    testFiles: [
      {
        path: 'test/ledger.formal.test.mjs',
        content: "import test from 'node:test';\ntest('LED-H1 non-negative balance', () => {});\n",
      },
      {
        path: 'test/runtime/ledger.json',
        content: JSON.stringify({
          entry_path: 'prompts/ledger.prompt.md',
          steps: [
            {
              id: 'LED-H2-clamp',
              op: 'transfer',
              input: {},
              checks: { '1': [['result', '/ok', '=', true]] },
            },
          ],
        }, null, 2),
      },
    ],
  });

  assert.deepEqual(res.summary, { total: 4, covered: 2, not_proved: 1, uncovered: 1 });
  assert.equal(res.rules[0].id, 'LED-H1');
  assert.equal(res.rules[0].status, 'covered');
  assert.deepEqual(res.rules[0].tiers, ['formal']);
  assert.deepEqual(res.rules[0].evidence, [{ path: 'test/ledger.formal.test.mjs', line: 2, kind: 'formal' }]);

  assert.equal(res.rules[1].id, 'LED-H2');
  assert.equal(res.rules[1].status, 'covered');
  assert.deepEqual(res.rules[1].tiers, ['scenario']);
  assert.equal(res.rules[1].evidence.length, 1);
  assert.equal(res.rules[1].evidence[0].path, 'test/runtime/ledger.json');
  assert.equal(res.rules[1].evidence[0].kind, 'scenario');

  assert.equal(res.rules[2].id, 'LED-H3');
  assert.equal(res.rules[2].status, 'not_proved');
  assert.equal(res.rules[2].not_proved_reason, 'preview formatting only');
  assert.deepEqual(res.rules[2].tiers, []);

  assert.equal(res.rules[3].id, 'LED-H4');
  assert.equal(res.rules[3].status, 'uncovered');
  assert.deepEqual(res.rules[3].tiers, []);
  assert.deepEqual(res.rules[3].evidence, []);
  assert.equal(res.rules[3].not_proved_reason, null);

  assert.equal(res.warnings.length, 1);
  assert.match(res.warnings[0], /^Warning: rule coverage: prompts\/ledger\.prompt\.md:10 \[rule-coverage-uncovered\]/);
  assert.match(res.warnings[0], /"LED-H4"/);
  assert.match(res.warnings[0], /Fix:.*Rerun: `pdd lint --diff`/);
  assert.equal(
    formatRuleCoverageSummary(res),
    'Rule coverage: 3/4 traced (2 covered, 1 not proved, 1 uncovered: LED-H4)',
  );
});

test('AC2 & RC-2: modified Story ## Rules to check traces to native test while unchanged merge-base rules are omitted even when line numbers shift', () => {
  const beforeStory = [
    '# Revoke token',
    '',
    '## Rules to check',
    '',
    '- **TR-H1:** Sessions expire after 24 hours.',
    '- **TR-C1:** Revoked tokens cannot refresh.',
    '',
  ].join('\n');

  const afterStory = [
    '# Revoke token',
    '',
    'As a security engineer, I want revoked tokens blocked immediately, so that compromised sessions end.',
    '',
    '## Rules to check',
    '',
    '- **TR-H1:** Sessions expire after 24 hours.',
    '- **TR-C1:** Revoked tokens cannot refresh or issue new sessions.',
    '',
  ].join('\n');

  const res = evaluateRuleCoverage({
    changedDocs: [{ path: 'user_stories/tokens.md', before: beforeStory, after: afterStory }],
    testFiles: [
      {
        path: 'test/tokens.test.mjs',
        content: "import test from 'node:test';\ntest('TR-C1: revoked token cannot issue session', () => {});\n",
      },
    ],
  });

  assert.equal(res.rules.length, 1);
  assert.equal(res.rules[0].id, 'TR-C1');
  assert.equal(res.rules[0].section, 'Rules to check');
  assert.equal(res.rules[0].status, 'covered');
  assert.deepEqual(res.rules[0].tiers, ['native']);
  assert.deepEqual(res.warnings, []);
  assert.equal(formatRuleCoverageSummary(res), 'Rule coverage: 1/1 traced (1 covered, 0 not proved, 0 uncovered)');
});

test('AC3 & RC-2: plain-prose ## Domain decisions, SCREAMING_SNAKE_CASE constants, standard tokens, and fenced code blocks emit zero rules and zero warnings', () => {
  const prosePrompt = [
    '# Sample CLI',
    '',
    '## Domain decisions',
    '',
    '- **Codex:** Reads config from home directory.',
    '- `PDD_SKILL_NAMES`: lists bundled skills.',
    '- `RETIRED_SKILL_NAMES`: lists retired skills.',
    '- **NON-EMPTY:** Rejects blank inputs.',
    '- **READ-ONLY:** Never mutates state.',
    '- **UTF-8:** Uses UTF-8 encoding and SHA-256 hashes with ISO-8601 dates.',
    '',
    '```markdown',
    '| LED-H9 | Fenced table rule |',
    '| --- | --- |',
    '- **TR-H9:** Fenced bullet rule.',
    '```',
    '',
    '~~~markdown',
    '- R9: Tilde fenced rule.',
    '~~~',
    '',
    '<!-- - **LED-H8:** Commented rule -->',
    '',
  ].join('\n');

  const res = evaluateRuleCoverage({
    changedDocs: [{ path: 'prompts/cli/sample.prompt.md', before: '', after: prosePrompt }],
    testFiles: [],
  });
  assert.deepEqual(res.rules, []);
  assert.deepEqual(res.summary, { total: 0, covered: 0, not_proved: 0, uncovered: 0 });
  assert.deepEqual(res.warnings, []);
  assert.equal(formatRuleCoverageSummary(res), '');

  // Verify real plain-prose pdd prompts produce 0 false rule extractions.
  for (const rel of ['prompts/cli/prove.prompt.md', 'prompts/cli/repo-hygiene-lint.prompt.md', 'prompts/cli/skills-install.prompt.md']) {
    const raw = readFileSync(join(REPO_ROOT, rel), 'utf8');
    assert.deepEqual(extractRulesFromMarkdown(raw, { sourcePath: rel }), [], `expected 0 false rules in ${rel}`);
  }
});

test('AC4 & RC-3: production code, fixtures, and substring/case spoofs never count as coverage', () => {
  const prompt = '# Ledger\n\n## Domain decisions\n\n- **LED-H4:** Audit entry records timestamp.\n- R1: Amounts use integer cents.\n';

  const res = evaluateRuleCoverage({
    changedDocs: [{ path: 'prompts/ledger.prompt.md', before: '', after: prompt }],
    testFiles: [
      { path: 'src/ledger.mjs', content: '// LED-H4 and R1 enforced here\n' },
      { path: 'test/fixtures/ledger.test.mjs', content: '// LED-H4 and R1 in fixture\n' },
      { path: 'test/ledger.test.mjs', content: "const r1 = 100;\ntest('LED-H40, XLED-H4, LED-H4a, R10, TR1 are unrelated', () => {});\n" },
    ],
  });

  assert.equal(res.rules.length, 2);
  assert.equal(res.rules[0].id, 'LED-H4');
  assert.equal(res.rules[0].status, 'uncovered');
  assert.deepEqual(res.rules[0].evidence, []);
  assert.equal(res.rules[1].id, 'R1');
  assert.equal(res.rules[1].status, 'uncovered');
  assert.deepEqual(res.rules[1].evidence, []);
  assert.equal(res.warnings.length, 2);

  assert.equal(classifyTestFileKind('src/ledger.mjs'), null);
  assert.equal(classifyTestFileKind('prompts/ledger.prompt.md'), null);
  assert.equal(classifyTestFileKind('test/fixtures/ledger.test.mjs'), null);
  assert.equal(classifyTestFileKind('test/ledger.formal.test.mjs'), 'formal');
  assert.equal(classifyTestFileKind('tests/test_formal_ledger.py'), 'formal');
  assert.equal(classifyTestFileKind('test/runtime/ledger.json'), 'scenario');
  assert.equal(classifyTestFileKind('test/ledger.test.mjs'), 'native');
});

test('AC5 & RC-4: empty/punctuation-only Not proved stays uncovered while inline, indented continuation, and doc-level Not proved reasons classify as not_proved', () => {
  const prompt = [
    '# Rules',
    '',
    '## Domain decisions',
    '',
    '- **LED-H5:** Closing balance reconciles daily. Not proved:',
    '- **LED-H6:** Empty punctuation disclosure. Not proved: ---',
    '- **LED-H8:** Mentions `Not proved:` and "Not proved: example" in syntax prose without excusing the rule.',
    '- **LED-H7:** Indented disclosure bullet.',
    '  - Not proved: requires external bank settlement webhook.',
    '- `TR-M` — Multi-currency conversion preview.',
    '- [R2] Display-only badge text. (Not proved: purely cosmetic label)',
    '',
    '## Verification notes',
    '',
    '- Not proved: TR-M (external FX feed unavailable offline)',
    '',
  ].join('\n');

  const res = evaluateRuleCoverage({
    changedDocs: [{ path: 'prompts/rules.prompt.md', before: '', after: prompt }],
    testFiles: [],
  });

  const byId = Object.fromEntries(res.rules.map(r => [r.id, r]));
  assert.equal(byId['LED-H5'].status, 'uncovered');
  assert.equal(byId['LED-H5'].not_proved_reason, null);
  assert.equal(byId['LED-H6'].status, 'uncovered');
  assert.equal(byId['LED-H6'].not_proved_reason, null);
  assert.equal(byId['LED-H8'].status, 'uncovered');
  assert.equal(byId['LED-H8'].not_proved_reason, null);

  assert.equal(byId['LED-H7'].status, 'not_proved');
  assert.equal(byId['LED-H7'].not_proved_reason, 'requires external bank settlement webhook');
  assert.equal(byId['TR-M'].status, 'not_proved');
  assert.equal(byId['TR-M'].not_proved_reason, 'external FX feed unavailable offline');
  assert.equal(byId['R2'].status, 'not_proved');
  assert.equal(byId['R2'].not_proved_reason, 'purely cosmetic label');
  assert.equal(res.warnings.length, 3);
});

test('table column detection, polyglot formal matching (Python/Go/Rust), and scenario checks keys work accurately', () => {
  const prompt = [
    '# Auth',
    '',
    '## Domain decisions',
    '',
    '### Token invariants',
    '',
    '| Area | Rule ID | Invariant |',
    '| --- | --- | --- |',
    '| Auth | `TR-C1` | Revoked token rejected |',
    '| Auth | TR-H2 | Expiry monotonic |',
    '| Auth | TR-H3 | Nonce unique |',
    '',
  ].join('\n');

  const res = evaluateRuleCoverage({
    changedDocs: [{ path: 'prompts/auth.prompt.md', before: '', after: prompt }],
    testFiles: [
      { path: 'tests/test_formal_auth.py', content: 'def test_tr_c1_revoked_rejected():\n    assert True\n' },
      { path: 'pkg/auth_formal_test.go', content: 'package auth\n// TR-H2 monotonic expiry\nfunc TestTRH2(t *testing.T) {}\n' },
      {
        path: 'tests/auth.json',
        content: JSON.stringify({
          entry_path: 'prompts/auth.prompt.md',
          steps: [{ id: 'nonce-check', op: 'verify', input: {}, checks: { '1:TR-H3': [['result', '/ok', '=', true]] } }],
        }, null, 2),
      },
    ],
  });

  assert.deepEqual(res.summary, { total: 3, covered: 3, not_proved: 0, uncovered: 0 });
  assert.deepEqual(res.rules[0].tiers, ['formal']);
  assert.deepEqual(res.rules[1].tiers, ['formal']);
  assert.deepEqual(res.rules[2].tiers, ['scenario']);
  assert.deepEqual(res.warnings, []);
});

test('Real CLI subprocess E2E: pdd lint --diff and pdd prove --json report rule_coverage non-blockingly and clear warning once linked', t => {
  const repo = initGitRepo(t, 'pdd-rule-coverage-e2e-');
  const nodeBin = JSON.stringify(process.execPath);
  mkdirSync(join(repo, 'prompts'), { recursive: true });
  mkdirSync(join(repo, 'src'), { recursive: true });
  mkdirSync(join(repo, 'test', 'runtime'), { recursive: true });
  mkdirSync(join(repo, 'user_stories'), { recursive: true });

  writeFileSync(
    join(repo, 'package.json'),
    JSON.stringify({ name: 'ledger-demo', type: 'module', scripts: { test: `${nodeBin} --test test/ledger.test.mjs` } }, null, 2) + '\n',
  );
  writeFileSync(
    join(repo, 'pdd.json'),
    JSON.stringify({
      verify: {
        test: `${nodeBin} --test test/ledger.test.mjs`,
        paths: [{ id: 'ledger', when: ['src/**'], run: `${nodeBin} --test test/ledger.test.mjs` }],
      },
    }, null, 2) + '\n',
  );
  writeFileSync(
    join(repo, 'prompts', 'ledger.prompt.md'),
    [
      '# Ledger',
      '',
      'Own `src/ledger.mjs`.',
      '',
      '## Domain decisions',
      '',
      '| ID | Rule | Verification |',
      '| --- | --- | --- |',
      '| LED-BASE | Base invariant already on main | Existing |',
      '',
      '## Dependencies',
      '',
      'None.',
      '',
    ].join('\n'),
  );
  writeFileSync(join(repo, 'src', 'ledger.mjs'), '// Prompt: prompts/ledger.prompt.md\n\nexport const clamp = n => Math.max(0, n);\n');
  writeFileSync(
    join(repo, 'test', 'ledger.test.mjs'),
    "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { clamp } from '../src/ledger.mjs';\ntest('clamp', () => assert.equal(clamp(-5), 0));\n",
  );
  writeFileSync(
    join(repo, 'user_stories', 'ledger.md'),
    '# Clamp balance\n\nAs an accountant, I want negative balances clamped to 0, so that ledger totals stay non-negative.\n\n## Acceptance criteria\n\n1. Clamping -5 returns 0.\n',
  );
  commitAll(repo, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-rules'], { cwd: repo });

  // Add mixed rules: LED-H1 (formal), LED-H2 (scenario), LED-H3 (Not proved), LED-H4 (uncovered); keep LED-BASE unchanged!
  writeFileSync(
    join(repo, 'prompts', 'ledger.prompt.md'),
    [
      '# Ledger',
      '',
      'Own `src/ledger.mjs`.',
      '',
      '## Domain decisions',
      '',
      '| ID | Rule | Verification |',
      '| --- | --- | --- |',
      '| LED-BASE | Base invariant already on main | Existing |',
      '| LED-H1 | Balance never drops below zero | Tier 1 |',
      '| LED-H2 | Transfers conserve minor units | Scenario |',
      '| LED-H3 | Preview uses formatted labels | Not proved: preview formatting only |',
      '| LED-H4 | Audit entry records timestamp | |',
      '',
      '## Dependencies',
      '',
      'None.',
      '',
    ].join('\n'),
  );
  writeFileSync(
    join(repo, 'test', 'ledger.formal.test.mjs'),
    "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { clamp } from '../src/ledger.mjs';\ntest('LED-H1: non-negative balance', () => {\n  for (let i = -50; i <= 50; i++) assert.ok(clamp(i) >= 0);\n});\n",
  );
  writeFileSync(
    join(repo, 'test', 'runtime', 'ledger.json'),
    JSON.stringify({
      entry_path: 'prompts/ledger.prompt.md',
      steps: [{ id: 'LED-H2-clamp', op: 'clamp', input: { n: -5 }, checks: { '1': [['result', '', '=', 0]] } }],
    }, null, 2) + '\n',
  );

  // Symlinked test file referencing LED-H4 must be refused by readSafeUtf8!
  const outsideDir = mkdtempSync(join(tmpdir(), 'pdd-outside-'));
  t.after(() => rmSync(outsideDir, { recursive: true, force: true }));
  writeFileSync(join(outsideDir, 'spoof.test.mjs'), "test('LED-H4 spoof via symlink', () => {});\n");
  symlinkSync(join(outsideDir, 'spoof.test.mjs'), join(repo, 'test', 'spoof.test.mjs'));

  // 1. Real CLI `pdd lint --diff --json` exits 0 with warning ONLY for LED-H4 (never LED-BASE, LED-H1, LED-H2, LED-H3).
  const lintCli = spawnSync(process.execPath, [BIN_PDD, 'lint', '--diff', 'main', '--json'], { cwd: repo, encoding: 'utf8' });
  assert.equal(lintCli.status, 0, `pdd lint --diff must be non-blocking (exit 0), got ${lintCli.status}: ${lintCli.stderr}`);
  const lintJson = JSON.parse(lintCli.stdout);
  assert.equal(lintJson.ok, true);
  assert.equal(lintJson.rule_coverage.length, 4, JSON.stringify(lintJson.rule_coverage));
  assert.deepEqual(lintJson.rule_coverage.map(r => [r.id, r.status]), [
    ['LED-H1', 'covered'],
    ['LED-H2', 'covered'],
    ['LED-H3', 'not_proved'],
    ['LED-H4', 'uncovered'],
  ]);
  const rcWarnings = lintJson.warnings.filter(w => w.includes('[rule-coverage-uncovered]'));
  assert.equal(rcWarnings.length, 1, JSON.stringify(rcWarnings));
  assert.match(rcWarnings[0], /"LED-H4"/);

  // Remove symlink before `pdd prove` so checkout stays clean of test symlinks.
  rmSync(join(repo, 'test', 'spoof.test.mjs'));

  // 2. Real CLI `pdd prove --base main --json` stays Proved (exit 0) and outputs structured `rule_coverage`.
  const proveCli = spawnSync(process.execPath, [BIN_PDD, 'prove', '--base', 'main', '--json'], { cwd: repo, encoding: 'utf8' });
  assert.equal(proveCli.status, EXIT_PROVED, `pdd prove must stay Proved (exit 0): ${proveCli.stdout}\n${proveCli.stderr}`);
  const proveJson = JSON.parse(proveCli.stdout);
  assert.equal(proveJson.outcome, OUTCOME_PROVED);
  assert.equal(proveJson.rule_coverage.length, 4);
  assert.deepEqual(proveJson.rule_coverage.find(r => r.id === 'LED-H1').tiers, ['formal']);
  assert.deepEqual(proveJson.rule_coverage.find(r => r.id === 'LED-H2').tiers, ['scenario']);
  assert.equal(proveJson.rule_coverage.find(r => r.id === 'LED-H3').not_proved_reason, 'preview formatting only');
  assert.equal(proveJson.rule_coverage.find(r => r.id === 'LED-H4').status, 'uncovered');

  // 3. Human-readable `pdd prove --base main` prints concise Rule coverage summary line.
  const proveHuman = spawnSync(process.execPath, [BIN_PDD, 'prove', '--base', 'main'], { cwd: repo, encoding: 'utf8' });
  assert.equal(proveHuman.status, EXIT_PROVED, proveHuman.stderr);
  assert.match(proveHuman.stdout, /Rule coverage: 3\/4 traced \(2 covered, 1 not proved, 1 uncovered: LED-H4\)/);

  // 4. Link LED-H4 in native test (preserving existing 'clamp' test!) -> warning vanishes completely!
  writeFileSync(
    join(repo, 'test', 'ledger.test.mjs'),
    [
      "import test from 'node:test';",
      "import assert from 'node:assert/strict';",
      "import { clamp } from '../src/ledger.mjs';",
      "test('clamp', () => assert.equal(clamp(-5), 0));",
      "test('LED-H4: audit timestamp', () => assert.equal(clamp(10), 10));",
    ].join('\n') + '\n',
  );
  const lintAfterOut = makeSink(), lintAfterErr = makeSink();
  const lintAfterCode = runLocalLint({ cwd: repo, diff: 'main', json: true }, { stdout: lintAfterOut, stderr: lintAfterErr });
  assert.equal(lintAfterCode, 0);
  const lintAfterJson = JSON.parse(lintAfterOut.text);
  assert.equal(lintAfterJson.warnings.filter(w => w.includes('[rule-coverage-uncovered]')).length, 0);
  assert.equal(lintAfterJson.rule_coverage.find(r => r.id === 'LED-H4').status, 'covered');
  assert.deepEqual(lintAfterJson.rule_coverage.find(r => r.id === 'LED-H4').tiers, ['native']);

  const proveAfter = runProve({ cwd: repo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(proveAfter.exitCode, EXIT_PROVED);
  assert.equal(proveAfter.receipt.rule_coverage.every(r => r.status !== 'uncovered'), true);
});

test('Zero false warnings when editing plain-prose ## Domain decisions in a git repo', t => {
  const repo = initGitRepo(t, 'pdd-rule-coverage-plain-');
  const nodeBin = JSON.stringify(process.execPath);
  mkdirSync(join(repo, 'prompts'), { recursive: true });
  mkdirSync(join(repo, 'src'), { recursive: true });
  mkdirSync(join(repo, 'test'), { recursive: true });
  writeFileSync(join(repo, 'package.json'), JSON.stringify({ name: 'plain-demo', type: 'module', scripts: { test: `${nodeBin} -e "process.exit(0)"` } }) + '\n');
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({ verify: { test: `${nodeBin} -e "process.exit(0)"` } }) + '\n');
  writeFileSync(join(repo, 'prompts', 'app.prompt.md'), '# App\n\n## Domain decisions\n\n- **Startup:** Loads config once.\n\n## Dependencies\n\nNone.\n');
  commitAll(repo, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'edit-prose'], { cwd: repo });
  writeFileSync(
    join(repo, 'prompts', 'app.prompt.md'),
    '# App\n\n## Domain decisions\n\n- **Startup:** Loads config once and validates `MAX_RETRY_COUNT`.\n- **Fail-closed:** Refuses malformed inputs.\n\n## Dependencies\n\nNone.\n',
  );

  const lintOut = makeSink(), lintErr = makeSink();
  const lintCode = runLocalLint({ cwd: repo, diff: 'main', json: true }, { stdout: lintOut, stderr: lintErr });
  assert.equal(lintCode, 0);
  const lintJson = JSON.parse(lintOut.text);
  assert.deepEqual(lintJson.rule_coverage, []);
  assert.deepEqual(lintJson.warnings, []);

  const proveHumanOut = makeSink();
  const proveRes = runProve({ cwd: repo, base: 'main', json: false }, { stdout: proveHumanOut, stderr: makeSink() });
  assert.equal(proveRes.exitCode, EXIT_PROVED);
  assert.deepEqual(proveRes.receipt.rule_coverage, []);
  assert.doesNotMatch(proveHumanOut.text, /Rule coverage:/);

  // Helper smoke assertions for direct exports
  assert.equal(isExplicitRuleId('LED-H1'), true);
  assert.equal(isExplicitRuleId('PDD_SKILL_NAMES'), false);
  assert.deepEqual(diffChangedRules([]), []);
  assert.deepEqual(findRuleReferencesInFiles([], []), {});
  assert.deepEqual(formatRuleCoverageWarnings([]), []);
  assert.deepEqual(analyzeRepoRuleCoverage({ root: '' }).rules, []);
});

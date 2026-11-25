import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {
  classifyTestFileKind,
  diffChangedRules,
  evaluateRuleCoverage,
  extractRulesFromMarkdown,
  isExplicitRuleId,
} from '../../src/core/rule-coverage.mjs';

function mulberry32(seed) {
  let a = seed >>> 0;
  return () => {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const PREFIXES = ['LED', 'TR', 'AUTH', 'PAY', 'RC', 'INV', 'SEC', 'RULE'];
const SUFFIXES = ['H1', 'H2', 'C1', 'C2', 'M', '01', '99'];
const PROSE_WORDS = ['Codex', 'Startup', 'NON-EMPTY', 'READ-ONLY', 'FAIL-CLOSED', 'PDD_SKILL_NAMES', 'MAX_FILE_BYTES', 'UTF-8', 'SHA-256', 'ISO-8601', 'api-server', 'web-ui'];

function pick(rng, arr) {
  return arr[Math.floor(rng() * arr.length)];
}

test('Formal RC-1, RC-2, RC-3, RC-4: 300 seeded PRNG worlds preserve conservation, non-blocking warnings, fence/shift invariance, monotonicity, and permutation determinism', () => {
  const rng = mulberry32(0x3702beef);

  for (let world = 0; world < 300; world++) {
    const ruleCount = 1 + Math.floor(rng() * 6);
    const ids = [];
    while (ids.length < ruleCount) {
      const candidate = rng() < 0.25
        ? `R${1 + Math.floor(rng() * 9)}`
        : `${pick(rng, PREFIXES)}-${pick(rng, SUFFIXES)}`;
      if (!ids.includes(candidate)) ids.push(candidate);
    }

    const beforeLines = ['# Generated prompt', '', '## Domain decisions', ''];
    const afterLines = ['# Generated prompt', ''];
    // Shift line numbers by 0..4 extra prose lines above ## Domain decisions (RC-2 shift invariance).
    const shiftCount = Math.floor(rng() * 5);
    for (let s = 0; s < shiftCount; s++) afterLines.push(`Context note ${s}.`);
    afterLines.push('', '## Domain decisions', '');

    const expectedChangedIds = new Set();
    const hasSubstantiveNotProved = new Set();

    for (const id of ids) {
      const mode = Math.floor(rng() * 4); // 0=unchanged, 1=added, 2=modified, 3=added+not_proved
      const baseDesc = `Invariant for ${id} check ${world}`;
      const bulletStyle = Math.floor(rng() * 3);
      const formatBullet = (desc) => {
        if (bulletStyle === 0) return `- **${id}:** ${desc}`;
        if (bulletStyle === 1) return `- \`${id}\` — ${desc}`;
        return `- [${id}] ${desc}`;
      };

      if (mode === 0) {
        beforeLines.push(formatBullet(baseDesc));
        afterLines.push(formatBullet(baseDesc));
      } else if (mode === 1) {
        afterLines.push(formatBullet(baseDesc));
        expectedChangedIds.add(id);
      } else if (mode === 2) {
        const longPad = rng() < 0.35 ? ` ${'x'.repeat(250)}` : '';
        beforeLines.push(formatBullet(`${baseDesc}${longPad} baseline`));
        afterLines.push(formatBullet(`${baseDesc}${longPad} tightened`));
        expectedChangedIds.add(id);
      } else {
        const emptyMarker = rng() < 0.3;
        const quotedOnly = !emptyMarker && rng() < 0.25;
        const doubleBacktick = quotedOnly && rng() < 0.5;
        const suffix = emptyMarker
          ? ' Not proved:'
          : (quotedOnly
            ? (doubleBacktick ? ' Rejects ``Not proved: fake`` syntax.' : ' Rejects `Not proved:` markers in prose.')
            : ` Not proved: external sandbox reason ${world}`);
        afterLines.push(formatBullet(`${baseDesc}.${suffix}`));
        expectedChangedIds.add(id);
        if (!emptyMarker && !quotedOnly) hasSubstantiveNotProved.add(id);
      }
    }

    // Inject plain-prose bullets + fenced code block containing fake rule IDs (RC-2 must ignore all of these).
    afterLines.push(`- **${pick(rng, PROSE_WORDS)}:** plain prose bullet.`);
    afterLines.push('```markdown');
    afterLines.push('| FAKE-99 | Must never be extracted inside fence |');
    afterLines.push('- **FAKE-98:** Must never be extracted inside fence.');
    afterLines.push('```');

    const testFiles = [];
    const coveredByRealTest = new Set();

    // Always add a production file and substring spoof file referencing EVERY ID (RC-3 must reject all of these!).
    testFiles.push({
      path: 'src/core/impl.mjs',
      content: ids.map(id => `// ${id} production comment`).join('\n'),
    });
    testFiles.push({
      path: 'test/spoofs.test.mjs',
      content: ids.map(id => `test('${id}0 X${id} ${id}A ${id.includes('-') ? '' : id.toLowerCase()}', () => {});`).join('\n'),
    });

    for (const id of ids) {
      if (rng() < 0.45) {
        const tierRoll = rng();
        coveredByRealTest.add(id);
        if (tierRoll < 0.34) {
          testFiles.push({
            path: `test/w${world}_${id.toLowerCase()}.formal.test.mjs`,
            content: `test('${id}: formal invariant', () => {});\n`,
          });
        } else if (tierRoll < 0.67) {
          testFiles.push({
            path: `test/runtime/w${world}_${id.toLowerCase()}.json`,
            content: JSON.stringify({
              entry_path: 'prompts/gen.prompt.md',
              steps: [{ id: `${id}-step`, op: 'run', input: {}, checks: { '1': [['result', '/ok', '=', true]] } }],
            }),
          });
        } else {
          testFiles.push({
            path: `test/w${world}_${id.toLowerCase()}.test.mjs`,
            content: `test('verifies ${id}', () => {});\n`,
          });
        }
      }
    }

    const changedDocs = [{ path: 'prompts/gen.prompt.md', before: beforeLines.join('\n'), after: afterLines.join('\n') }];
    const res = evaluateRuleCoverage({ changedDocs, testFiles });

    // RC-2: exact changed rule set (unchanged shifted rules & fenced fake rules strictly excluded).
    const observedIds = new Set(res.rules.map(r => r.id));
    assert.deepEqual([...observedIds].sort(), [...expectedChangedIds].sort(), `world ${world} changed rule mismatch`);
    assert.equal(observedIds.has('FAKE-99'), false);
    assert.equal(observedIds.has('FAKE-98'), false);

    // RC-1: exact integer conservation & warning parity (never emits blocking Error: lines).
    assert.equal(res.summary.total, res.rules.length);
    assert.equal(res.summary.covered + res.summary.not_proved + res.summary.uncovered, res.summary.total);
    assert.equal(res.warnings.length, res.summary.uncovered);
    for (const w of res.warnings) {
      assert.ok(w.startsWith('Warning: rule coverage:'), `must be non-blocking Warning:, got: ${w}`);
    }

    // RC-3 & RC-4: exact classification against oracle.
    for (const row of res.rules) {
      if (coveredByRealTest.has(row.id)) {
        assert.equal(row.status, 'covered', `world ${world} ${row.id} should be covered`);
        assert.ok(row.tiers.length >= 1 && row.evidence.length >= 1);
        for (const ev of row.evidence) {
          assert.notEqual(ev.path, 'src/core/impl.mjs');
          assert.notEqual(ev.path, 'test/spoofs.test.mjs');
        }
      } else if (hasSubstantiveNotProved.has(row.id)) {
        assert.equal(row.status, 'not_proved', `world ${world} ${row.id} should be not_proved`);
        assert.ok(typeof row.not_proved_reason === 'string' && row.not_proved_reason.length >= 2);
      } else {
        assert.equal(row.status, 'uncovered', `world ${world} ${row.id} should be uncovered`);
        assert.equal(row.not_proved_reason, null);
        assert.deepEqual(row.evidence, []);
      }
    }

    // Permutation determinism: reversing testFiles yields identical output.
    const reversed = evaluateRuleCoverage({ changedDocs, testFiles: [...testFiles].reverse() });
    assert.deepEqual(reversed, res, `world ${world} permutation broke determinism`);

    // Monotonicity (RC-3): adding an extra native test for an uncovered rule upgrades it to covered without breaking any covered rule.
    const firstUncovered = res.rules.find(r => r.status === 'uncovered');
    if (firstUncovered) {
      const upgraded = evaluateRuleCoverage({
        changedDocs,
        testFiles: [...testFiles, { path: `test/extra_${world}.test.mjs`, content: `// covers ${firstUncovered.id}\n` }],
      });
      assert.equal(upgraded.rules.find(r => r.id === firstUncovered.id).status, 'covered');
      assert.equal(upgraded.summary.uncovered, res.summary.uncovered - 1);
      assert.equal(upgraded.warnings.length, res.warnings.length - 1);
    }
  }
});

test('Formal RC-2 & RC-3 finite grid: explicit rule ID classifier and test file kind classifier satisfy exact boundaries', () => {
  const validIds = ['LED-H1', 'LED-M', 'TR-C1', 'TR-M', 'RC-1', 'RULE-01', 'PAY-H1-A', 'LED_H1', 'R1', 'R01', 'AC1', 'INV2'];
  const invalidIds = ['', ' ', 'A', 'ABC', '123', 'Codex', 'web-ui', 'api-server', 'NON-EMPTY', 'READ-ONLY', 'FAIL-CLOSED', 'PDD_SKILL_NAMES', 'RETIRED_SKILL_NAMES', 'UTF-8', 'SHA-256', 'ISO-8601', 'RFC-7396', 'TLS-1'];

  for (const id of validIds) {
    assert.equal(isExplicitRuleId(id), true, `expected valid rule ID: ${id}`);
    assert.equal(isExplicitRuleId(`**${id}:**`), true, `expected valid wrapped rule ID: ${id}`);
    assert.equal(isExplicitRuleId(`\`${id}\``), true, `expected valid backtick rule ID: ${id}`);
    assert.equal(isExplicitRuleId(`[${id}]`), true, `expected valid bracketed rule ID: ${id}`);
  }
  for (const bad of invalidIds) {
    assert.equal(isExplicitRuleId(bad), false, `expected rejected non-rule token: ${bad}`);
  }

  // Exact file classification grid.
  const grid = [
    ['test/a.formal.test.mjs', 'formal'],
    ['tests/test_formal_ledger.py', 'formal'],
    ['tests/ledger_formal_test.py', 'formal'],
    ['formal/test_ledger.py', 'formal'],
    ['pkg/ledger_formal_test.go', 'formal'],
    ['tests/formal_ledger.rs', 'formal'],
    ['test/runtime/ledger.json', 'scenario'],
    ['tests/ledger.json', 'scenario'],
    ['test/ledger.test.mjs', 'native'],
    ['tests/test_ledger.py', 'native'],
    ['pkg/ledger_test.go', 'native'],
    ['tests/ledger.rs', 'native'],
    ['src/ledger.mjs', null],
    ['prompts/ledger.prompt.md', null],
    ['user_stories/ledger.md', null],
    ['docs/cli.md', null],
    ['test/fixtures/ledger.test.mjs', null],
    ['test/mocks/ledger.test.mjs', null],
    ['test/helpers/ledger.mjs', null],
    ['test/package.json', null],
    ['../escape/test.mjs', null],
  ];
  for (const [path, expected] of grid) {
    assert.equal(classifyTestFileKind(path), expected, `classifyTestFileKind(${path})`);
  }

  // Diff idempotence grid: identical before/after always gives 0 changed rules.
  const sample = '# Spec\n\n## Domain decisions\n\n- **LED-H1:** Stay >= 0.\n- **LED-H2:** Conserve units.\n';
  assert.deepEqual(diffChangedRules([{ path: 'prompts/spec.prompt.md', before: sample, after: sample }]), []);
  assert.equal(extractRulesFromMarkdown(sample, { sourcePath: 'prompts/spec.prompt.md' }).length, 2);
});

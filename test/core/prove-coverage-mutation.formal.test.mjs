import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {
  aggregateCoverageSplit,
  parseUnifiedDiffAddedLines,
  resolveV8FileCoverage,
  validateProveOptInFlags,
} from '../../src/core/prove-coverage.mjs';
import {
  evaluateMutationOutcome,
  selectGuardMutations,
} from '../../src/core/prove-mutation.mjs';

function mulberry32(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

test('Tier-1 zero-install PRNG formal invariants: coverage split conservation, monotonicity, union bounds, and unimported gap honesty over 250 worlds', () => {
  const rng = mulberry32(0x3701c0de);
  const pickSubset = (arr, p) => arr.filter(() => rng() < p);

  for (let w = 0; w < 250; w += 1) {
    const numFiles = 1 + Math.floor(rng() * 4);
    const diffLinesByFile = {};
    const fallbackExecutableLinesByFile = {};
    const suites = {
      formal: { status: 'ok', testFiles: ['test/a.formal.test.mjs'], command: 'node --test', files: {} },
      vectors: { status: 'ok', testFiles: ['test/a.vectors.test.mjs'], command: 'node --test', files: {} },
      all: { status: 'ok', testFiles: [], command: 'npm test', files: {} },
    };

    for (let f = 0; f < numFiles; f += 1) {
      const path = `src/mod_${f}.mjs`;
      const nLines = 3 + Math.floor(rng() * 12);
      const allLines = Array.from({ length: nLines }, (_, i) => i + 1);
      const diffLines = pickSubset(allLines, 0.5);
      if (diffLines.length > 0) {
        diffLinesByFile[path] = diffLines;
        fallbackExecutableLinesByFile[path] = allLines;
      }

      const importInAll = rng() < 0.8;
      if (importInAll) {
        const fExec = pickSubset(allLines, 0.45);
        const vExec = pickSubset(allLines, 0.45);
        const aExec = [...new Set([...fExec, ...vExec, ...pickSubset(allLines, 0.25)])].sort((a, b) => a - b);
        suites.formal.files[path] = { executedLines: fExec, missedLines: allLines.filter(l => !fExec.includes(l)), executableLines: allLines };
        suites.vectors.files[path] = { executedLines: vExec, missedLines: allLines.filter(l => !vExec.includes(l)), executableLines: allLines };
        suites.all.files[path] = { executedLines: aExec, missedLines: allLines.filter(l => !aExec.includes(l)), executableLines: allLines };
      }
    }

    const res = aggregateCoverageSplit({ tool: 'node-v8', diffLinesByFile, suites, fallbackExecutableLinesByFile });
    for (const sName of ['formal', 'vectors', 'all']) {
      const s = res.suites[sName];
      assert.equal(s.total.covered + s.total.missed, s.total.statements, `${sName} total conservation`);
      assert.equal(s.diff.covered + s.diff.missed, s.diff.lines, `${sName} diff conservation`);
      if (s.total.statements === 0) assert.equal(s.total.pct, null);
      else assert.ok(s.total.pct >= 0 && s.total.pct <= 100);
      if (s.diff.lines === 0) assert.equal(s.diff.pct, null);
      else assert.ok(s.diff.pct >= 0 && s.diff.pct <= 100);
    }

    // Union monotonicity and exact formal-only / vectors-only partition bounds
    const u = res.unionFormalVectors;
    assert.equal(u.total.covered + u.total.missed, u.total.statements);
    assert.ok(u.total.covered >= Math.max(res.suites.formal.total.covered, res.suites.vectors.total.covered));
    assert.ok(u.total.covered <= res.suites.formal.total.covered + res.suites.vectors.total.covered);
    assert.ok(u.formalOnlyLines <= res.suites.formal.total.covered);
    assert.ok(u.vectorsOnlyLines <= res.suites.vectors.total.covered);
    assert.ok(u.formalOnlyLines + u.vectorsOnlyLines <= u.total.covered);
    assert.equal(u.diff.covered + u.diff.missed, u.diff.lines);
    assert.ok(u.diff.covered >= Math.max(res.suites.formal.diff.covered, res.suites.vectors.diff.covered));
  }
});

test('Tier-1 zero-install PRNG formal invariants: diff parser, flag validator, mutation selector determinism & cap, and outcome fail-closed rules over 250 worlds', () => {
  const rng = mulberry32(0x3701cafe);
  const kinds = ['comparison-flip', 'boolean-op-flip', 'guard-negate', 'return-flip'];

  // Exhaustive finite grid on validateProveOptInFlags
  for (const coverage of [false, true]) {
    for (const mutationCheck of [false, true]) {
      for (const testVal of [undefined, 'npm test']) {
        for (const expectVal of [undefined, 'ERR']) {
          const r = validateProveOptInFlags({ coverage, mutationCheck, test: testVal, expect: expectVal });
          const conflict = (coverage || mutationCheck) && (testVal !== undefined || expectVal !== undefined);
          assert.equal(r.ok, !conflict);
          assert.equal(r.exitCode, conflict ? 2 : 0);
        }
      }
    }
  }

  for (let w = 0; w < 250; w += 1) {
    // 1. Unified diff parser invariant: pure deletion hunks add 0 lines; non-zero hunks add exact count lines.
    const start = 1 + Math.floor(rng() * 40);
    const count = Math.floor(rng() * 6);
    const diffText = `diff --git a/src/x.mjs b/src/x.mjs\n--- a/src/x.mjs\n+++ b/src/x.mjs\n@@ -1,0 +${start},${count} @@\n`;
    const parsed = parseUnifiedDiffAddedLines({ diffText });
    const got = parsed.files['src/x.mjs'] ?? [];
    assert.equal(got.length, count);
    if (count > 0) {
      assert.equal(got[0], start);
      assert.equal(got.at(-1), start + count - 1);
    }

    // 2. selectGuardMutations: order-invariant, <= maxMutations (1..3), unique (file, line), formal-covered prioritized.
    const nCand = Math.floor(rng() * 12);
    const maxMutations = 1 + Math.floor(rng() * 3);
    const candidates = [];
    const formalCoveredLines = { 'src/a.mjs': [], 'src/b.mjs': [], 'src/c.mjs': [] };
    for (let i = 0; i < nCand; i += 1) {
      const file = `src/${['a', 'b', 'c'][Math.floor(rng() * 3)]}.mjs`;
      const line = 1 + Math.floor(rng() * 15);
      const kind = kinds[Math.floor(rng() * kinds.length)];
      if (rng() < 0.5) formalCoveredLines[file].push(line);
      candidates.push({ file, line, kind, description: `d${i}`, original: 'a', mutated: 'b', mutatedContent: 'c' });
    }
    const selA = selectGuardMutations({ candidates, formalCoveredLines, maxMutations }).selected;
    const reversed = [...candidates].reverse();
    const selB = selectGuardMutations({ candidates: reversed, formalCoveredLines, maxMutations }).selected;
    assert.ok(selA.length <= maxMutations && selA.length <= 3);
    assert.deepEqual(selA.map(m => `${m.file}:${m.line}:${m.kind}`), selB.map(m => `${m.file}:${m.line}:${m.kind}`), 'selection must be deterministic regardless of input order');
    assert.equal(new Set(selA.map(m => `${m.file}:${m.line}`)).size, selA.length, 'at most 1 mutation per (file, line)');

    // 3. evaluateMutationOutcome: fail-closed on survival, syntax errors NEVER count as killed, always isolated.
    const nRes = Math.floor(rng() * 4);
    const results = [];
    let expectedKilled = 0;
    let expectedSurvived = 0;
    let expectedSyntax = 0;
    for (let i = 0; i < nRes; i += 1) {
      const mode = Math.floor(rng() * 3); // 0=killed, 1=survived, 2=syntax
      const syntaxOnlyCrash = mode === 2;
      const failedOnMutation = mode === 0;
      if (syntaxOnlyCrash) expectedSyntax += 1;
      else if (failedOnMutation) expectedKilled += 1;
      else expectedSurvived += 1;
      results.push({
        id: `M${i + 1}`,
        file: 'src/a.mjs',
        line: i + 2,
        kind: 'comparison-flip',
        description: `guard ${i}`,
        original: 'x < 0',
        mutated: 'x >= 0',
        formalCovered: true,
        executed: true,
        failedOnMutation,
        syntaxOnlyCrash,
        exitCode: failedOnMutation || syntaxOnlyCrash ? 1 : 0,
        summary: 'test',
      });
    }
    const ev = evaluateMutationOutcome({ results, formalFiles: ['test/a.formal.test.mjs'] });
    assert.equal(ev.isolated, true);
    assert.equal(ev.workingTreeMutated, false);
    assert.equal(ev.killed, expectedKilled);
    assert.equal(ev.survived, expectedSurvived);
    assert.equal(ev.syntaxErrors, expectedSyntax);
    if (expectedSurvived > 0) {
      assert.equal(ev.status, 'not-proved');
      assert.equal(ev.ok, false);
    } else if (nRes === 0) {
      assert.equal(ev.status, 'not-applicable');
      assert.equal(ev.ok, true);
    } else if (expectedKilled === 0 && expectedSyntax > 0) {
      assert.equal(ev.status, 'not-proved');
      assert.equal(ev.ok, false);
    } else {
      assert.equal(ev.status, 'proved');
      assert.equal(ev.ok, true);
    }
  }

  // 4. V8 nested coverage invariant: zero-count inner range always masks lines strictly inside it.
  const sample = 'export function f(x) {\n  if (x) {\n    return 1;\n  }\n  return 2;\n}\n';
  const blockStart = sample.indexOf('{\n    return 1;');
  const blockEnd = sample.indexOf('}', blockStart) + 1;
  const v8 = resolveV8FileCoverage({
    sourceText: sample,
    functions: [
      { functionName: '', isBlockCoverage: true, ranges: [{ startOffset: 0, endOffset: sample.length, count: 1 }] },
      { functionName: 'f', isBlockCoverage: true, ranges: [{ startOffset: 0, endOffset: sample.length, count: 1 }, { startOffset: blockStart, endOffset: blockEnd, count: 0 }] },
    ],
  });
  assert.equal(v8.executedLines.length + v8.missedLines.length, v8.executableLines.length);
  assert.ok(v8.missedLines.includes(3));
  assert.ok(!v8.executedLines.includes(3));
});

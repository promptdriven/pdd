import test from 'node:test';
import assert from 'node:assert/strict';
import { inventoryModule } from './workflow-inventory-replay-helper.mjs';

// Story-derived finite models, not a second parser. Source is rendered from
// named cases and line lists; expected identities and deltas use those models.
const words = (alphabet, limit) => {
  const out = [[]];
  for (let n = 1; n <= limit; n++) {
    for (const prefix of out.filter(value => value.length === n - 1)) {
      for (const letter of alphabet) out.push([...prefix, letter]);
    }
  }
  return out;
};
const quote = value => {
  const entities = { '&': '&#38;', '<': '&#60;', '>': '&#62;', '`': '&#96;', '|': '&#124;', ':': '&#58;' };
  return [...JSON.stringify(value)].map(char => entities[char] ??
    (/[\u061c\u200e\u200f\u202a-\u202e\u2066-\u2069]/u.test(char)
      ? `\\u${char.codePointAt(0).toString(16).padStart(4, '0')}` : char)).join('');
};
const label = item => quote(item.name) + (item.occurrence > 1 ? ` [${item.occurrence}]` : '');
const identify = cases => cases.map((item, index) => ({
  ...item, occurrence: 1 + cases.slice(0, index).filter(previous => previous.name === item.name).length,
}));
const sameIdentity = (a, b) => a.name === b.name && a.occurrence === b.occurrence;

// Exhaustively enumerate all increasing equal-line matchings, then select the
// longest; lexicographic pair order expresses earliest old, then earliest new.
// This is intentionally exponential and independent of dynamic-programming LCS.
function assertionDelta(oldLines, newLines) {
  const matchings = [[]];
  function extend(prefix, oldStart, newStart) {
    for (let i = oldStart; i < oldLines.length; i++) {
      for (let j = newStart; j < newLines.length; j++) {
        if (oldLines[i] === newLines[j]) {
          const next = [...prefix, [i, j]];
          matchings.push(next);
          extend(next, i + 1, j + 1);
        }
      }
    }
  }
  extend([], 0, 0);
  matchings.sort((a, b) => {
    if (a.length !== b.length) return b.length - a.length;
    for (let k = 0; k < a.length; k++) {
      if (a[k][0] !== b[k][0]) return a[k][0] - b[k][0];
      if (a[k][1] !== b[k][1]) return a[k][1] - b[k][1];
    }
    return 0;
  });
  const changes = [];
  let oldStart = 0, newStart = 0;
  for (const [oldEnd, newEnd] of [...matchings[0], [oldLines.length, newLines.length]]) {
    const oldGap = oldLines.slice(oldStart, oldEnd), newGap = newLines.slice(newStart, newEnd);
    for (let i = 0; i < Math.max(oldGap.length, newGap.length); i++) {
      changes.push([oldGap[i], newGap[i]]);
    }
    oldStart = oldEnd + 1;
    newStart = newEnd + 1;
  }
  return changes;
}
function introduced(oldLines, newLines) {
  return newLines.filter((line, index) =>
    newLines.slice(0, index + 1).filter(value => value === line).length >
    oldLines.filter(value => value === line).length);
}
const disclaimer = 'Static inventory only; tests were not run.\n';
function expectedReport(path, oldCases, newCases) {
  const before = identify(oldCases), after = identify(newCases);
  const removed = before.filter(item => !after.some(other => sameIdentity(item, other)));
  const lines = [`Tests vs base: ${quote(path)} ${before.length} → ${after.length} tests. Removed: ${
    removed.length ? `${removed.length} (${removed.map(label).join(', ')}).` : 'none.'}`];
  const assertions = [], skips = [];
  for (const item of after) {
    const previous = before.find(other => sameIdentity(item, other));
    if (previous) {
      for (const [oldLine, newLine] of assertionDelta(previous.assertions ?? [], item.assertions ?? [])) {
        assertions.push(`Changed assertions in kept tests: ${quote(path)} ${label(item)} ${
          oldLine === undefined ? '(added)' : quote(oldLine)} → ${newLine === undefined ? '(removed)' : quote(newLine)}.`);
      }
    }
    for (const line of introduced(previous?.skips ?? [], item.skips ?? [])) {
      skips.push(`New skips: ${quote(path)} ${label(item)} ${quote(line)}.`);
    }
  }
  return [...lines, ...(assertions.length ? assertions : ['Changed assertions in kept tests: none.']),
    ...(skips.length ? skips : ['New skips: none.'])].join('\n') + '\n' + disclaimer;
}
const js = cases => cases.map(item => `${item.declaration ?? `test(${JSON.stringify(item.name)}, () => {`}\n${
  [...(item.assertions ?? []), ...(item.body ?? [])].join('\n')}\n});\n`).join('');

test('formal bounded Story laws: occurrence identity, exact assertion LCS, skip multisets and escaped report bounds', async t => {
  const { analyzeTestChanges, collectTestInventory } = await inventoryModule();
  let comparisons = 0;
  function check(before, after, oldCases, newCases, path = 'test/formal.js') {
    const report = analyzeTestChanges({ files: [{ oldPath: path, newPath: path, before, after }] });
    const expected = expectedReport(path, oldCases, newCases);
    assert.equal(report.available, true);
    assert.equal(report.reason, '');
    assert.equal(report.text, expected, JSON.stringify({ before, after }));
    assert.equal(report.details, expected);
    comparisons++;
  }

  // All 225 pairs of name words of length 0..3 over {a,b}; position
  // assertions expose incorrect matching of duplicate occurrence identities.
  const names = words(['a', 'b'], 3);
  for (const oldNames of names) for (const newNames of names) {
    const model = values => values.map((name, i) => ({ name, assertions: [`assert.equal(slot, ${i});`] }));
    const before = model(oldNames), after = model(newNames);
    check(js(before), js(after), before, after);
  }

  // All 225 pairs of assertion words of length 0..3 over two distinct
  // complete lines, including repeats, crossed ties and empty gaps.
  const assertions = words(['assert.ok(A);', 'expect(B).toBe(true);'], 3);
  for (const before of assertions) for (const after of assertions) {
    const oldCases = [{ name: 'kept', assertions: before }], newCases = [{ name: 'kept', assertions: after }];
    check(js(oldCases), js(newCases), oldCases, newCases);
  }

  // 84 declaration/body models: 3 modifiers × 4 literal-option sets ×
  // all 7 body marker words of length 0..2. All 7,056 before/after pairs.
  const markers = words(['t.skip("later");', 't.todo("pending");'], 2);
  const skipCases = [];
  for (const modifier of ['', '.skip', '.todo']) for (const options of ['', '{skip: true}, ', '{todo: true}, ', '{skip: true, todo: true}, ']) {
    for (const body of markers) {
      const declaration = `test${modifier}("kept", ${options}t => {`;
      skipCases.push({ name: 'kept', declaration, body, skips: [...(modifier || options ? [declaration] : []), ...body] });
    }
  }
  for (const before of skipCases) for (const after of skipCases) {
    check(js([before]), js([after]), [before], [after]);
  }
  // Every marker on an added identity is new; removed identities create no
  // new skip or changed-assertion entry.
  for (const item of skipCases) {
    check('', js([item]), [], [item]);
    check(js([item]), '', [item], []);
  }

  // All 169 pairs of contiguous pytest decorator words of length 0..2
  // over skip/skipif/xfail, with exact-line multiset rather than set deltas.
  const decorators = words(['@pytest.mark.skip', '@pytest.mark.skipif(False)', '@pytest.mark.xfail'], 2);
  const py = list => [...list, 'def test_kept():', '    pass', ''].join('\n');
  for (const before of decorators) for (const after of decorators) {
    check(py(before), py(after), [{ name: 'test_kept', skips: before }], [{ name: 'test_kept', skips: after }], 'test_formal.py');
  }

  // Every individual hostile character below, plus the combined string,
  // appears as a path, case name and changed assertion operand. Identity is raw.
  const hostile = ['&', '<', '>', '`', '|', ':', '\t', '\n', '\r', '\b', '\f', '\u0001', '\u001b', '\u061c', '\u200e', '\u200f',
    ...Array.from({ length: 5 }, (_, i) => String.fromCodePoint(0x202a + i)),
    ...Array.from({ length: 4 }, (_, i) => String.fromCodePoint(0x2066 + i))];
  for (const value of [...hostile, hostile.join('')]) {
    const path = `test/${value}.js`, name = `name${value}`;
    const before = [{ name, assertions: [`assert.equal(value, ${JSON.stringify(value)});`] }];
    const after = [{ name, assertions: ['assert.equal(value, "changed");'] }];
    check(js(before), js(after), before, after, path);
    check(js(before), '', before, [], path);
  }

  // Exhaustive finite grid of 10 file counts × 4 name lengths across the
  // 12,000-code-point boundary. Full custody is compared to unbounded oracle.
  let boundedReports = 0;
  for (const count of [0, 1, 2, 20, 40, 79, 80, 81, 160, 1000]) for (const length of [0, 1, 120, 240]) {
    const name = `lost${'😀'.repeat(length)}<|:`;
    const files = Array.from({ length: count }, (_, i) => ({ oldPath: `test/${String(i).padStart(4, '0')}.js`, newPath: '',
      before: js([{ name }]), after: '' }));
    const report = analyzeTestChanges({ files });
    const full = count ? files.map(file => expectedReport(file.oldPath, [{ name }], []).split('\n')[0]).join('\n') +
      '\nChanged assertions in kept tests: none.\nNew skips: none.\n' + disclaimer :
      'Tests vs base: none.\nChanged assertions in kept tests: none.\nNew skips: none.\n' + disclaimer;
    assert.equal(report.available, true);
    assert.equal(report.details, full);
    assert.ok([...report.text].length <= 12000);
    assert.ok(report.text.endsWith(disclaimer));
    assert.ok(!/[<>|`\u202a-\u202e\u2066-\u2069]/u.test(report.text));
    if ([...full].length <= 12000) assert.equal(report.text, full);
    else {
      assert.match(report.text, /Inventory details omitted: \d+ lines;(?: \d+ file summaries omitted;)? full report: test-inventory.json in the run folder\./);
      const reportLines = report.text.split('\n');
      const namesOmitted = full.split('\n').filter(line => line.startsWith('Tests vs base:')).map(line => line.replace(/ \(.*\)\.$/, '.'));
      let summaryCount = 0;
      while (reportLines[summaryCount] === namesOmitted[summaryCount]) summaryCount++;
      assert.ok(summaryCount > 0);
      const fullLines = full.trimEnd().split('\n').slice(0, -1);
      const detailLines = reportLines.slice(summaryCount).filter(line =>
        line && !line.startsWith('Inventory details omitted:') && line !== disclaimer.trimEnd());
      assert.deepEqual(detailLines, fullLines.slice(0, detailLines.length));
      assert.ok(report.text.includes(`Inventory details omitted: ${fullLines.length - detailLines.length} lines;`));
      if (summaryCount < count) assert.ok(report.text.includes(`${count - summaryCount} file summaries omitted`));
    }
    boundedReports++;
  }

  // Full-identity validation and failed snapshots must remain unavailable,
  // never none. Each valid pinned request is observed exactly once.
  let collectorChecks = 0;
  for (const baseSha of ['', 'HEAD', 'a'.repeat(39), 'g'.repeat(40), 'a'.repeat(40), 'b'.repeat(64)]) {
    for (const kind of ['empty', 'unavailable', 'reject']) {
      let calls = 0;
      const headSha = 'c'.repeat(40), valid = /^[a-f0-9]{40}$|^[a-f0-9]{64}$/.test(baseSha);
      const result = await collectTestInventory({ cwd: '/formal', baseSha, headSha }, { readSnapshot: async input => {
        calls++; assert.deepEqual(input, { cwd: '/formal', baseSha, headSha });
        if (kind === 'reject') throw Error('private secret');
        return { available: kind === 'empty', files: [], reason: 'private secret' };
      } });
      assert.equal(calls, valid ? 1 : 0);
      assert.equal(result.available, valid && kind === 'empty');
      if (!result.available) {
        assert.equal(result.reason, !valid ? 'invalid commit identity' : kind === 'reject' ? 'snapshot read failed' : 'snapshot unavailable');
        assert.ok(result.text.startsWith('Tests vs base: unavailable ('));
        assert.ok(!result.text.includes('none.') && !result.text.includes('private secret'));
        assert.equal(result.details, result.text);
      }
      collectorChecks++;
    }
  }
  t.diagnostic(`formal exhaustive comparisons=${comparisons}; report-bound grid=${boundedReports}; collector cases=${collectorChecks}`);
});

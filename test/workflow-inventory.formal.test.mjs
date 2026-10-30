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
  const entities = { '&': '&#38;', '<': '&#60;', '>': '&#62;', '`': '&#96;', '|': '&#124;', ':': '&#58;', '@': '&#64;', '#': '&#35;' };
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
  const hostile = ['&', '<', '>', '`', '|', ':', '@', '#', '\t', '\n', '\r', '\b', '\f', '\u0001', '\u001b', '\u061c', '\u200e', '\u200f',
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

test('formal revised skip values: complete literals and dynamic expressions stay distinct', async t => {
  const { analyzeTestChanges } = await inventoryModule();
  // These classifications come from the approved literal-only rule. No source
  // parsing in the oracle: each source fragment carries its declared meaning.
  const values = [
    { source: 'true', skip: true, todo: true },
    ...['false', 'condition', 'true && condition', 'true || condition', 'true ? x : y',
      "'reason' + dynamic", '`reason` + dynamic', '`why ${reason}`', "''", '""', '``']
      .map(source => ({ source, skip: false, todo: false })),
    ...["'later'", '"later"', '`later`', "'function failed'", '"function failed"', '`function failed`',
      "'later => now'", '"later => now"', '`later => now`']
      .map(source => ({ source, skip: true, todo: false })),
  ];
  let comparisons = 0;
  for (const call of ['test', 'it']) for (const key of ['skip', 'todo']) for (const value of values) {
    for (const position of ['first', 'last']) {
      const option = `${key}: ${value.source}`;
      const options = position === 'first' ? `${option}, timeout: 10` : `timeout: 10, ${option}`;
      const declaration = `${call}("kept", {${options}}, () => {`;
      const before = [{ name: 'kept' }];
      const after = [{ name: 'kept', declaration, skips: value[key] ? [declaration] : [] }];
      for (const [oldCases, newCases] of [[before, after], [after, after]]) {
        const report = analyzeTestChanges({ files: [{ oldPath: 'test/formal.js', newPath: 'test/formal.js',
          before: js(oldCases), after: js(newCases) }] });
        assert.equal(report.available, true);
        assert.equal(report.details, expectedReport('test/formal.js', oldCases, newCases), declaration);
        comparisons++;
      }
    }
  }
  // A literal in an unrelated body object does not become a declaration option.
  for (const key of ['skip', 'todo']) {
    const cases = [{ name: 'kept', body: [`consume({${key}: true});`] }];
    const report = analyzeTestChanges({ files: [{ oldPath: '', newPath: 'test/formal.js', before: '', after: js(cases) }] });
    assert.equal(report.details, expectedReport('test/formal.js', [], cases));
    comparisons++;
  }
  t.diagnostic(`formal revised literal comparisons=${comparisons}; values=${values.length}; calls=2; keys=2; option positions=2; transitions=2; unrelated body objects=2`);
});

test('formal revised suite identities are independent of child test occurrences', async t => {
  const { analyzeTestChanges } = await inventoryModule();
  const alphabet = [
    { name: 'a', skipped: false }, { name: 'a', skipped: true },
    { name: 'b', skipped: false }, { name: 'b', skipped: true },
  ];
  const sequences = words(alphabet, 2);
  const declaration = suite => `describe${suite.skipped ? '.skip' : ''}(${JSON.stringify(suite.name)}, () => {`;
  const source = suites => suites.map(suite => `${declaration(suite)}\n  test(${JSON.stringify(suite.name)}, () => {});\n});\n`).join('');
  let comparisons = 0;
  for (const before of sequences) for (const after of sequences) {
    const oldOwners = identify(before), newOwners = identify(after);
    const skips = newOwners.filter(owner => owner.skipped && !oldOwners.some(previous =>
      sameIdentity(owner, previous) && previous.skipped));
    // Each suite has one child named like it. Case identities and suite
    // identities deliberately collide by name, but remain separate owners.
    const cases = suites => suites.map(suite => ({ name: suite.name }));
    const expected = expectedReport('test/suites.js', cases(before), cases(after)).replace('New skips: none.\n',
      skips.length ? skips.map(owner => `New skips: ${quote('test/suites.js')} suite ${label(owner)} ${quote(declaration(owner))}.\n`).join('') : 'New skips: none.\n');
    const report = analyzeTestChanges({ files: [{ oldPath: 'test/suites.js', newPath: 'test/suites.js',
      before: source(before), after: source(after) }] });
    assert.equal(report.available, true);
    assert.equal(report.details, expected, JSON.stringify({ before, after }));
    comparisons++;
  }
  t.diagnostic(`formal revised suite comparisons=${comparisons}; all suite words length 0..2 over two names × two skip states`);
});

test('formal revised quoted option data never becomes a literal true option', async t => {
  const { analyzeTestChanges } = await inventoryModule();
  const failures = [];
  let comparisons = 0;
  // Only a skip string is a recognized string-valued option. A todo string
  // or an unrelated reason string cannot supply literal skip/todo properties.
  for (const call of ['test', 'it']) for (const property of ['todo', 'reason']) {
    for (const delimiter of ["'", '"', '`']) for (const data of ['skip: true,', 'todo: true,']) {
      const declaration = `${call}("kept", {${property}: ${delimiter}${data}${delimiter}}, () => {`;
      const before = [{ name: 'kept' }], after = [{ name: 'kept', declaration }];
      const report = analyzeTestChanges({ files: [{ oldPath: 'test/formal.js', newPath: 'test/formal.js', before: js(before), after: js(after) }] });
      const expected = expectedReport('test/formal.js', before, after);
      if (!report.available || report.details !== expected) failures.push({ declaration, expected, actual: report.details });
      comparisons++;
    }
  }
  t.diagnostic(`formal revised quoted-data comparisons=${comparisons}; calls=2; properties=2; delimiters=3; marker-like strings=2; mismatches=${failures.length}`);
  assert.deepEqual(failures, [], 'quoted option data cannot introduce literal option properties');
});

test('formal revised availability and strict assertion cap preserve healthy evidence', async t => {
  const { analyzeTestChanges } = await inventoryModule();
  const path = 'test/healthy.js';
  const before = [{ name: 'kept', assertions: ['assert.ok(old);'] }, { name: 'gone' }];
  const after = [{ name: 'kept', assertions: ['assert.ok(new);'], body: ['t.skip("later");'], skips: ['t.skip("later");'] }];
  const healthy = { oldPath: path, newPath: path, before: js(before), after: js(after) };
  const categories = ['Tests vs base:', 'Changed assertions in kept tests:', 'New skips:'];
  const reasons = ['candidate blob exceeds 1 MiB', 'binary candidate blob', 'non-UTF-8 candidate blob'];
  let partial = 0;
  // Every subset of three disclosed bad-file categories, in both input orders.
  // Marked content is intentionally unusable and must never affect the budget.
  for (let mask = 0; mask < 8; mask++) for (const reversed of [false, true]) {
    const bad = reasons.flatMap((unavailableReason, i) => mask & (1 << i)
      ? [{ oldPath: `test/bad${i}.js`, newPath: `test/bad${i}.js`, before: '\0', after: 'x'.repeat(1048577), unavailableReason }]
      : []);
    const files = [healthy, ...bad];
    const healthyLines = expectedReport(path, before, after).trimEnd().split('\n').slice(0, -1);
    const expected = categories.flatMap(category => [
      ...bad.map(file => `${category} ${quote(file.newPath)} unavailable (${quote(file.unavailableReason)}).`),
      ...healthyLines.filter(line => line.startsWith(category)),
    ]).join('\n') + '\n' + disclaimer;
    const report = analyzeTestChanges({ files: reversed ? files.reverse() : files });
    assert.equal(report.available, true);
    assert.equal(report.reason, '');
    assert.equal(report.details, expected);
    partial++;
  }
  let caps = 0;
  // All 25 old/new cardinality pairs from this boundary set. Repeated equal
  // lines make the exact uncapped delta a count difference, independently of LCS.
  for (const oldCount of [0, 1, 999, 1000, 1001]) for (const newCount of [0, 1, 999, 1000, 1001]) {
    const line = 'assert.ok(shared);';
    const oldCases = [{ name: 'large', assertions: Array(oldCount).fill(line) }, ...before];
    const newCases = [{ name: 'large', assertions: Array(newCount).fill(line) }, ...after];
    const capped = oldCount * newCount > 1000000;
    const largeChanges = capped ? [`Changed assertions in kept tests: ${quote(path)} "large" unavailable ("too many assertion lines to compare").`]
      : Array(Math.abs(oldCount - newCount)).fill(`Changed assertions in kept tests: ${quote(path)} "large" ${
        oldCount > newCount ? quote(line) : '(added)'} → ${oldCount > newCount ? '(removed)' : quote(line)}.`);
    const healthyLines = expectedReport(path, before, after).trimEnd().split('\n');
    healthyLines[0] = `Tests vs base: ${quote(path)} 3 → 2 tests. Removed: 1 ("gone").`;
    healthyLines.splice(1, 0, ...largeChanges);
    const report = analyzeTestChanges({ files: [{ oldPath: path, newPath: path, before: js(oldCases), after: js(newCases) }] });
    assert.equal(report.available, true);
    assert.equal(report.details, healthyLines.join('\n') + '\n', `${oldCount} × ${newCount}`);
    caps++;
  }
  let candidateLimits = 0;
  for (const count of [999, 1000, 1001]) for (const documentation of [0, 1001]) {
    // Every record has two candidate rename sides, but counts only once.
    const files = Array.from({ length: count }, (_, i) => ({ oldPath: `test/${i}.js`, newPath: `tests/${i}.js`, before: '', after: '' }));
    files.push(...Array.from({ length: documentation }, (_, i) => ({ oldPath: '', newPath: `docs/${i}.md`, before: '', after: '\0' })));
    const report = analyzeTestChanges({ files });
    assert.equal(report.available, count <= 1000, `${count} candidates + ${documentation} docs`);
    assert.equal(report.reason, count <= 1000 ? '' : 'inventory limit exceeded');
    candidateLimits++;
  }
  let aggregateLimits = 0;
  const blob = ' '.repeat(1048576);
  for (const offset of [-1, 0, 1]) {
    const files = Array.from({ length: 8 }, (_, i) => ({ oldPath: `test/${i}.js`, newPath: `test/${i}.js`, before: blob, after: blob }));
    if (offset < 0) files[0].before = blob.slice(1);
    if (offset > 0) files.push({ oldPath: '', newPath: 'test/extra.js', before: '', after: ' ' });
    const report = analyzeTestChanges({ files });
    assert.equal(report.available, offset <= 0, `16 MiB ${offset}`);
    assert.equal(report.reason, offset <= 0 ? '' : 'inventory limit exceeded');
    aggregateLimits++;
  }
  t.diagnostic(`formal revised partial-file subsets/order=${partial}; assertion-product grid=${caps}; candidate-limit grid=${candidateLimits}; aggregate-byte boundary=${aggregateLimits}`);
});

test('manual revision formal callback ownership separates option data from real bodies',async t=>{
  const {analyzeTestChanges}=await inventoryModule();
  const callbacks=['() => {}','t => {}','async () => {}','async t => {}','function (t) {}','async function named(t) {}'];
  const contents=['t.skip("no")','t.todo("no")','assert.ok(no)','expect(no)'];
  const failures=[];let comparisons=0;
  const check=(before,after,oldCases,newCases)=>{
    const report=analyzeTestChanges({files:[{oldPath:'test/manual.js',newPath:'test/manual.js',before,after}]});
    const expected=expectedReport('test/manual.js',oldCases,newCases);
    if(!report.available||report.details!==expected)failures.push({before,after,expected,actual:report.details});
    comparisons++;
  };
  // This finite grammar is rendered from explicit owner models. It does not
  // parse the source under test. All actual callbacks in this grid are empty.
  for(const call of ['test','it'])for(const delimiter of ["'",'"','`'])for(const content of contents)for(const fake of [`=> ${content}`,`function () { ${content} }`]){
    const quotedData=delimiter+fake.replaceAll('"',delimiter==='"'?'\\"':'"')+delimiter;
    for(const options of [`{reason: ${quotedData}}`,`{nested: {reason: ${quotedData}}}`,`{nested: [${quotedData}]}`,`{nested: consume(${quotedData})}`])for(const callback of callbacks){
      const before=`${call}("kept", () => {});\n`,after=`${call}("kept", ${options}, ${callback});\n`;
      check(before,after,[{name:'kept'}],[{name:'kept'}]);
    }
  }
  const quotedComparisons=comparisons;
  for(const call of ['test','it'])for(const content of contents)for(const option of [`{nested: () => { ${content}; }}`,`{nested: function () { ${content}; }}`])for(const callback of callbacks){
    check(`${call}("kept", () => {});\n`,`${call}("kept", ${option}, ${callback});\n`,[{name:'kept'}],[{name:'kept'}]);
  }
  const nestedComparisons=comparisons-quotedComparisons;
  // Positive inline bodies use the same callback forms, with/without misleading
  // option data. The full declaration is the promised complete source line.
  for(const callback of callbacks)for(const options of ['',`{reason: '=> t.todo("fake") assert.ok(fake)'}, `])for(const content of contents){
    const before=`test("kept", ${options}${callback});`;
    const after=`test("kept", ${options}${callback.replace('{}',`{ ${content}; }`)});`;
    const marker=content.startsWith('t.'),afterModel={name:'kept',assertions:marker?[]:[after],skips:marker?[after]:[]};
    check(before+'\n',after+'\n',[{name:'kept'}],[afterModel]);
  }
  const inlineComparisons=comparisons-quotedComparisons-nestedComparisons;
  for(const callback of callbacks)for(const options of [`{reason: '=> {'}`,`{reason: 'function () {'}`]){
    const declaration=`test("outer", ${options}, ${callback.replace('{}','{')}`;
    const child=`  test("child", ${options});`;
    const before=declaration+'\n'+child+'\n  assert.ok(old);\n});\n';
    const after=declaration+'\n'+child+'\n  assert.ok(new);\n  t.todo("real");\n});\n';
    check(before,after,[{name:'outer',assertions:['  assert.ok(old);']},{name:'child'}],[{name:'outer',assertions:['  assert.ok(new);'],skips:['  t.todo("real");']},{name:'child'}]);
  }
  t.diagnostic(`manual callback comparisons=${comparisons}; quoted=${quotedComparisons}; nested=${nestedComparisons}; inline positives=${inlineComparisons}; multiline positives=${comparisons-quotedComparisons-nestedComparisons-inlineComparisons}; mismatches=${failures.length}`);
  assert.deepEqual(failures,[],'option data is outside actual callback bodies; genuine body evidence retains its owner');
});

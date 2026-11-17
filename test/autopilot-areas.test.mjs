import test from 'node:test';
import assert from 'node:assert/strict';
import { areasOverlap, groupReadyIssues, issueAreas, orderGroupsSpreadFirst, ownerAreas, parseCodeowners, resolveArea, resolveAreas } from '../src/autopilot-areas.mjs';

const areasFor = pattern => [{ name: 'literal', owner: 'literal-owner', match: { paths: [pattern] } }];
const resolve = (pattern, path) => resolveArea({ areas: areasFor(pattern), evidence: { paths: [path] } });

test('path rules treat regex punctuation as literal in explicit maps and CODEOWNERS', () => {
  for (const text of ['.', '+', '^', '$', '{', '}', '(', ')', '|', 'a.b+c^d$e{2}(f|g)']) {
    const pattern = `/src/${text}.mjs`, path = pattern.slice(1);
    assert.deepEqual(resolve(pattern, path), { state: 'resolved', area: 'literal', owner: 'literal-owner', source: 'config' });
    assert.equal(resolve(pattern, 'src/other.mjs').state, 'unsure');
    const codeowners = `/src/** @fallback\n${pattern} @literal-owner`;
    assert.equal(resolveArea({ codeowners, evidence: { paths: [path] } }).owner, 'literal-owner');
    assert.equal(resolveArea({ codeowners, evidence: { paths: ['src/other.mjs'] } }).owner, 'fallback');
  }
});

test('backslashes, brackets and negation remain unsupported in both owner sources', () => {
  for (const text of ['\\', '\\d', '\\.', '\\\\', '[x]', ']', '!']) {
    const pattern = `/src/${text}.mjs`;
    for (const path of [pattern.slice(1), 'src/d.mjs', 'src/1.mjs', 'src/x.mjs']) {
      assert.equal(resolve(pattern, path).state, 'unsure');
      assert.deepEqual(resolveAreas({ areas: areasFor(pattern), evidence: { paths: [path] } }), []);
      assert.equal(resolveArea({ codeowners: `/src/** @fallback\n${pattern} @unsafe`, evidence: { paths: [path] } }).owner, 'fallback');
    }
    assert.deepEqual(parseCodeowners(`${pattern} @unsafe`), []);
  }
});

test('literal encoding preserves wildcard, directory and anchor behavior', () => {
  const cases = [
    ['/src/a+b?.*', 'src/a+b1.mjs', true], ['/src/a+b?.*', 'src/ab1.mjs', false],
    ['/src/a+b?.*', 'nested/src/a+b1.mjs', false],
    ['/src/**/a+b.mjs', 'src/a+b.mjs', true], ['/src/**/a+b.mjs', 'src/deep/a+b.mjs', true],
    ['/src/**/a+b.mjs', 'src/deep/ab.mjs', false],
    ['a+b.mjs', 'nested/a+b.mjs', true], ['a+b.mjs', 'nested/ab.mjs', false],
    ['/src/a+b/', 'src/a+b/deep/file', true], ['/src/a+b/', 'src/ab/deep/file', false],
  ];
  for (const [pattern, path, matches] of cases) assert.equal(resolve(pattern, path).state === 'resolved', matches);
});

test('ownerAreas enriches canonical prompt owners without uncertain:root catch-alls or folder-level false overlaps (#3455)', () => {
  const mapOwners = new Map([
    ['src/billing-engine.mjs', { prompt: 'prompts/cli/invoice.prompt.md', owners: ['prompts/cli/invoice.prompt.md'] }],
    ['src/ledger- calc.mjs', { prompt: 'not-a-prompt.txt' }],
    ['src/other-mod.mjs', { prompt: 'prompts/cli/help.prompt.md', owners: ['prompts/cli/help.prompt.md'] }],
  ]);

  assert.deepEqual(
    ownerAreas(['src/billing-engine.mjs', 'prompts/cli/direct.prompt.md', 'package.json', 'README.md'], mapOwners),
    ['owner:prompts/cli/invoice.prompt.md', 'owner:prompts/cli/direct.prompt.md'],
  );

  // Unowned files produce zero tokens (never uncertain:root) and never falsely overlap each other.
  assert.deepEqual(ownerAreas(['package.json', 'README.md', 'src/unowned-a.mjs'], mapOwners), []);
  assert.deepEqual(
    areasOverlap(['package.json', 'src/unowned-a.mjs'], ['README.md', 'src/unowned-b.mjs'], { owners: mapOwners }),
    { overlap: false, reason: null },
  );

  // Distinct prompts inside prompts/cli/ do NOT overlap, while differently named files sharing the same owning prompt DO overlap!
  assert.deepEqual(
    areasOverlap(['src/billing-engine.mjs'], ['src/other-mod.mjs'], { owners: mapOwners }),
    { overlap: false, reason: null },
  );
  assert.deepEqual(
    areasOverlap(['src/billing-engine.mjs'], ['prompts/cli/invoice.prompt.md'], { owners: mapOwners }),
    { overlap: true, reason: 'owner:prompts/cli/invoice.prompt.md' },
  );

  // Also supports ownerRead ({ owners: Map }), findOwners ({ files: [...] }), and plain object shapes.
  assert.deepEqual(ownerAreas(['src/billing-engine.mjs'], { owners: mapOwners }), ['owner:prompts/cli/invoice.prompt.md']);
  assert.deepEqual(
    ownerAreas(['src/from-report.mjs'], { files: [{ path: 'src/from-report.mjs', owners: ['prompts/cli/report.prompt.md'] }] }),
    ['owner:prompts/cli/report.prompt.md'],
  );
  assert.deepEqual(
    ownerAreas(['src/from-obj.mjs'], { 'src/from-obj.mjs': 'prompts/cli/obj.prompt.md' }),
    ['owner:prompts/cli/obj.prompt.md'],
  );
  assert.ok(issueAreas({ title: 'Fix src/billing-engine.mjs', body: '' }, null, { owners: mapOwners }).includes('owner:prompts/cli/invoice.prompt.md'));
});

test('orderGroupsSpreadFirst spreads Pass 1 across disjoint prompt/file areas and overflows Pass 2 behind Pass 1 without double-claiming (#3455)', () => {
  const owners = new Map([
    ['src/a-worker.mjs', { prompt: 'prompts/cli/alpha.prompt.md' }],
    ['src/a-helper.mjs', { prompt: 'prompts/cli/alpha.prompt.md' }],
    ['src/b-worker.mjs', { prompt: 'prompts/cli/beta.prompt.md' }],
    ['src/c-worker.mjs', { prompt: 'prompts/cli/gamma.prompt.md' }],
  ]);

  const g1 = { primary: { number: 10 }, companions: [], issues: [10], areas: ['src/a-worker.mjs'] };
  const g2 = { primary: { number: 11 }, companions: [], issues: [11], areas: ['src/a-helper.mjs'] }; // overlaps g1 via owner:prompts/cli/alpha.prompt.md!
  const g3 = { primary: { number: 12 }, companions: [], issues: [12], areas: ['src/b-worker.mjs'] }; // disjoint!
  const g4 = { primary: { number: 13 }, companions: [], issues: [13], areas: ['src/c-worker.mjs'] }; // overlaps busyJob #9!

  const busyJobs = [{ issue: 9, issues: [9, 90], areas: ['prompts/cli/gamma.prompt.md'] }];

  const ordered = orderGroupsSpreadFirst([g1, g2, g3, g4], busyJobs, { owners });
  // Pass 1: #10 (alpha) + #12 (beta, disjoint from both busy gamma and newly placed alpha)
  // Pass 2: #11 (alpha overflow) + #13 (gamma overflow)
  assert.deepEqual(ordered.map(g => g.primary.number), [10, 12, 11, 13]);

  // Small 1-prompt repo: all 3 candidate groups touch the same prompt -> Pass 1 takes first, Pass 2 keeps remaining two in rank order (0 dropped!).
  const singlePrompt = [
    { primary: { number: 1 }, companions: [], issues: [1], areas: ['prompts/app.prompt.md'] },
    { primary: { number: 2 }, companions: [], issues: [2], areas: ['src/app.mjs'] },
    { primary: { number: 3 }, companions: [], issues: [3], areas: ['test/app.test.mjs'] },
  ];
  assert.deepEqual(
    orderGroupsSpreadFirst(singlePrompt, [{ issue: 99, areas: ['src/app.mjs'] }]).map(g => g.primary.number),
    [1, 2, 3],
  );

  // Never double-claims an issue already active as primary or companion, and prunes active companions cleanly.
  const withActiveDupes = [
    { primary: { number: 90 }, companions: [], issues: [90], areas: ['src/x.mjs'] }, // #90 is companion of busy #9
    {
      primary: { number: 20 },
      companions: [{ number: 9 }, { number: 21 }],
      issues: [20, 9, 21],
      areas: ['src/y.mjs'],
    },
    { primary: { number: 21 }, companions: [], issues: [21], areas: ['src/z.mjs'] }, // #21 already claimed as companion of #20
  ];
  const deduped = orderGroupsSpreadFirst(withActiveDupes, busyJobs);
  assert.equal(deduped.length, 1);
  assert.equal(deduped[0].primary.number, 20);
  assert.deepEqual(deduped[0].issues, [20, 21]);
  assert.deepEqual(deduped[0].companions.map(c => c.number), [21]);

  // groupReadyIssues also groups small issues sharing an owning prompt via owners option.
  const rows = [
    { number: 51, title: 'Small fix 1', body: 'In src/a-worker.mjs' },
    { number: 52, title: 'Small fix 2', body: 'In src/a-helper.mjs' },
  ];
  const cards = new Map([
    [51, { class: 'ready', size: 'small', areas: ['src/a-worker.mjs'] }],
    [52, { class: 'ready', size: 'small', areas: ['src/a-helper.mjs'] }],
  ]);
  const grouped = groupReadyIssues(rows, cards, { maxGroupSize: 3, owners });
  assert.equal(grouped.length, 1);
  assert.deepEqual(grouped[0].issues, [51, 52]);
});

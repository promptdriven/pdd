import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { findOwners } from '../src/file-owner.mjs';
import { ownerRead } from '../src/autopilot-core.mjs';
import {
  areasOverlap,
  groupReadyIssues,
  issueAreas,
  normalizeAreaPath,
  ownerAreas,
  parseCodeowners,
  resolveArea,
  resolveAreas,
} from '../src/autopilot-areas.mjs';

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

test('canonical prompt ownership detects shared-owner collisions across different file stems', () => {
  const repoRoot = process.cwd();
  const repoFiles = [
    'prompts/cli/workflow-runner.prompt.md',
    'prompts/cli/autopilot-doctor.prompt.md',
    'src/workflow-runner.mjs',
    'src/workflow-eligibility.mjs',
    'src/autopilot-doctor.mjs',
  ];
  const readResult = ownerRead(fs, repoRoot, repoFiles);
  const findResult = findOwners({ root: repoRoot, paths: repoFiles }, { files: () => repoFiles });
  const plainOwners = {
    'src/workflow-runner.mjs': { prompt: 'prompts/cli/workflow-runner.prompt.md', state: 'resolved' },
    'src/workflow-eligibility.mjs': 'prompts/cli/workflow-runner.prompt.md',
    'src/autopilot-doctor.mjs': { prompt: 'prompts/cli/autopilot-doctor.prompt.md', state: 'resolved' },
  };

  for (const owners of [readResult.owners, readResult, findResult, plainOwners]) {
    const overlap = areasOverlap(['src/workflow-runner.mjs'], ['src/workflow-eligibility.mjs'], { owners });
    assert.equal(overlap.overlap, true);
    assert.equal(overlap.reason, 'owner:prompts/cli/workflow-runner.prompt.md');
    assert.equal(
      areasOverlap(['src/workflow-runner.mjs'], ['src/autopilot-doctor.mjs'], { owners }).overlap,
      false,
    );
  }

  // Direct *.prompt.md edits collide with code files owned by that prompt.
  const promptFootprint = issueAreas(
    { title: 'Clarify workflow eligibility rule', body: 'Update prompts/cli/workflow-runner.prompt.md' },
    null,
    { owners: readResult.owners },
  );
  const codeFootprint = issueAreas(
    { title: 'Refine eligibility helper', body: 'Update src/workflow-eligibility.mjs and test/workflow-runner.test.mjs' },
    null,
    { owners: readResult.owners },
  );
  assert.ok(promptFootprint.includes('owner:prompts/cli/workflow-runner.prompt.md'));
  assert.ok(codeFootprint.includes('owner:prompts/cli/workflow-runner.prompt.md'));
  assert.equal(codeFootprint.some(x => x.startsWith('uncertain:')), false, 'test files do not synthesize uncertain reservations');
  assert.equal(areasOverlap(promptFootprint, codeFootprint).overlap, true);
  assert.equal(
    areasOverlap(['prompts/cli/workflow-runner.prompt.md'], ['src/workflow-eligibility.mjs'], { owners: readResult.owners }).overlap,
    true,
  );

  // Without owners, existing stem/folder fallback behavior stays intact.
  assert.equal(areasOverlap(['src/workflow-runner.mjs'], ['src/workflow-eligibility.mjs']).overlap, false);
  assert.equal(areasOverlap(['prompts/cli/workflow-runner.prompt.md'], ['src/workflow-runner.mjs']).overlap, true);
});

test('ownerAreas and issueAreas include implied docs/cli.md target and serialize uncertain or unknown code owners conservatively', () => {
  assert.equal(normalizeAreaPath('owner: ./prompts/cli/workflow-runner.prompt.md'), 'owner:prompts/cli/workflow-runner.prompt.md');
  assert.equal(normalizeAreaPath('owner:../outside.prompt.md'), null);
  assert.equal(normalizeAreaPath('uncertain:src/billing'), 'uncertain:src/billing');
  assert.equal(normalizeAreaPath('uncertain:../outside'), null);

  // Implied shared-contract target: src/command-catalog.mjs brings docs/cli.md into the footprint.
  const catalogAreas = issueAreas({ title: 'Add flag to src/command-catalog.mjs', body: '' });
  assert.deepEqual(catalogAreas, ['src/command-catalog.mjs', 'docs/cli.md']);
  assert.deepEqual(areasOverlap(['src/command-catalog.mjs'], ['docs/cli.md']), {
    overlap: true,
    reason: 'docs/cli.md',
  });

  // Uncertain or unknown ownership on src/ and app/ code files reserves uncertain:<dir|root>,
  // and top-level uncertain:root overlaps both uncertain:root and nested uncertain:<folder>.
  const owners = new Map([
    ['src/known.mjs', { prompt: 'prompts/cli/known.prompt.md', state: 'resolved' }],
    ['src/shaky.mjs', { prompt: null, state: 'uncertain' }],
  ]);
  assert.deepEqual(ownerAreas(['src/shaky.mjs'], owners), ['uncertain:root']);
  assert.deepEqual(ownerAreas(['app/unmapped.ts'], owners), ['uncertain:root']);
  assert.deepEqual(ownerAreas(['src/billing/unmapped.mjs'], owners), ['uncertain:src/billing']);
  assert.deepEqual(ownerAreas(['app/billing/new-beta.ts'], owners), ['uncertain:app/billing']);
  assert.deepEqual(ownerAreas(['docs/cli.md', 'test/known.test.mjs'], owners), []);

  assert.equal(areasOverlap(['uncertain:root'], ['uncertain:root']).overlap, true);
  assert.equal(areasOverlap(['uncertain:root'], ['uncertain:app/billing']).overlap, true);
  assert.equal(areasOverlap(['uncertain:app/billing'], ['uncertain:root']).overlap, true);
  assert.equal(areasOverlap(['src/new-alpha.mjs'], ['app/billing/new-beta.ts'], { owners }).overlap, true);
  assert.equal(areasOverlap(['src/shaky.mjs'], ['app/unmapped.ts'], { owners }).overlap, true);
  assert.equal(areasOverlap(['src/shaky.mjs'], ['src/known.mjs'], { owners }).overlap, false);
  assert.equal(areasOverlap(['src/billing/unmapped.mjs'], ['src/billing/invoice.mjs'], { owners }).overlap, true);
});

test('owner-free fallback preserves app/* folder overlap and grouping while owners separates distinct app/* owners', () => {
  assert.deepEqual(areasOverlap(['app/alpha.ts'], ['app/beta.ts']), { overlap: true, reason: 'app' });

  const appRows = [
    { number: 1, title: 'Update alpha', body: 'In app/alpha.ts' },
    { number: 2, title: 'Update beta', body: 'In app/beta.ts' },
  ];
  const appCards = new Map([
    [1, { class: 'ready', size: 'small', areas: ['app/alpha.ts'] }],
    [2, { class: 'ready', size: 'small', areas: ['app/beta.ts'] }],
  ]);
  assert.deepEqual(
    groupReadyIssues(appRows, appCards).map(g => g.issues),
    [[1, 2]],
    'without owners, app/* preserves base folder grouping',
  );

  const appOwners = new Map([
    ['app/alpha.ts', { prompt: 'prompts/app/alpha.prompt.md', state: 'resolved' }],
    ['app/beta.ts', { prompt: 'prompts/app/beta.prompt.md', state: 'resolved' }],
  ]);
  assert.equal(areasOverlap(['app/alpha.ts'], ['app/beta.ts'], { owners: appOwners }).overlap, false);
  assert.equal(
    areasOverlap(
      issueAreas(appRows[0], appCards.get(1), { owners: appOwners }),
      issueAreas(appRows[1], appCards.get(2), { owners: appOwners }),
    ).overlap,
    false,
    'precomputed issueAreas(..., { owners }) footprints also separate distinct app/* prompt owners',
  );
  assert.deepEqual(
    groupReadyIssues(appRows, appCards, { owners: appOwners }).map(g => g.issues),
    [[1], [2]],
    'with owners, distinct app/* prompt owners stay separate',
  );
});

test('single-issue and grouped footprints retain all raw paths and synthesized owner tokens without truncation', () => {
  // 1. Single issue with 24 distinct owned files keeps all 24 raw paths + all 24 owner:* tokens (48 entries).
  const singleOwners = new Map();
  const bodyPaths = [];
  for (let i = 0; i < 24; i++) {
    const file = `src/mod-${i}.mjs`, prompt = `prompts/cli/mod-${i}.prompt.md`;
    singleOwners.set(file, { prompt, state: 'resolved' });
    bodyPaths.push(file);
  }
  const singleFootprint = issueAreas(
    { title: 'Touch 24 modules', body: bodyPaths.join(' ') },
    null,
    { owners: singleOwners },
  );
  assert.equal(singleFootprint.length, 48);
  assert.ok(singleFootprint.includes('src/mod-23.mjs'));
  assert.ok(singleFootprint.includes('owner:prompts/cli/mod-23.prompt.md'));

  // 1b. area:* labels do not consume the 24-path extraction budget (mapped and unmapped 24th file),
  // while preserving deterministic cardPaths -> area:* labels -> textPaths ordering.
  const labeledMapped = issueAreas(
    { title: 'Touch 24 modules with area label', body: bodyPaths.join(' '), labels: ['area:billing'] },
    null,
    { owners: singleOwners },
  );
  assert.equal(labeledMapped[0], 'area:billing');
  assert.equal(labeledMapped.length, 49);
  assert.ok(labeledMapped.includes('src/mod-23.mjs'));
  assert.ok(labeledMapped.includes('owner:prompts/cli/mod-23.prompt.md'));

  const nestedPaths = Array.from({ length: 24 }, (_, i) => `src/part-${i}/file-${i}.mjs`);
  const partialOwners = new Map(nestedPaths.slice(0, 23).map((p, i) => [p, `prompts/owner-${i}.prompt.md`]));
  const labeledUncertain = issueAreas(
    { body: nestedPaths.join(' '), labels: ['area:billing'] },
    null,
    { owners: partialOwners },
  );
  assert.ok(labeledUncertain.includes('area:billing'));
  assert.ok(labeledUncertain.includes(nestedPaths[23]));
  assert.ok(labeledUncertain.includes('uncertain:src/part-23'));
  assert.equal(areasOverlap(labeledUncertain, ['src/part-23/helper.mjs'], { owners: partialOwners }).overlap, true);
  assert.deepEqual(areasOverlap(labeledUncertain, ['src/part-23/deep/helper.mjs'], { owners: partialOwners }), {
    overlap: true,
    reason: 'uncertain:src/part-23',
  });

  // 2. 3 explicitly linked small cards (group_with), each targeting 5 separately owned files (15 files + 15 owner:* = 30 entries).
  const owners = new Map();
  const rows = [], cards = new Map();
  for (let issue = 1; issue <= 3; issue++) {
    const areas = [];
    for (let k = 0; k < 5; k++) {
      const file = `src/issue-${issue}-file-${k}.mjs`;
      const prompt = `prompts/cli/issue-${issue}-file-${k}.prompt.md`;
      owners.set(file, { prompt, state: 'resolved' });
      areas.push(file);
    }
    rows.push({ number: issue, title: `Issue ${issue}`, body: '' });
    cards.set(issue, { class: 'ready', size: 'small', areas, group_with: [1, 2, 3].filter(x => x !== issue) });
  }
  owners.set('src/issue-3-file-4-helper.mjs', { prompt: 'prompts/cli/issue-3-file-4.prompt.md', state: 'resolved' });

  const [group] = groupReadyIssues(rows, cards, { owners, maxGroupSize: 3 });
  assert.deepEqual(group.issues, [1, 2, 3]);
  assert.equal(group.areas.length, 30, 'all 15 raw paths and all 15 owner:* tokens retained');
  assert.equal(areasOverlap(group.areas, ['src/issue-3-file-4.mjs'], { owners }).overlap, true);
  assert.deepEqual(areasOverlap(group.areas, ['src/issue-3-file-4-helper.mjs'], { owners }), {
    overlap: true,
    reason: 'owner:prompts/cli/issue-3-file-4.prompt.md',
  });
});

test('groupReadyIssues clusters small issues only on explicit group_with or the same single owning prompt when owners is supplied', () => {
  const owners = new Map([
    ['src/workflow-runner.mjs', { prompt: 'prompts/cli/workflow-runner.prompt.md', state: 'resolved' }],
    ['src/workflow-eligibility.mjs', { prompt: 'prompts/cli/workflow-runner.prompt.md', state: 'resolved' }],
    ['src/billing/invoice.mjs', { prompt: 'prompts/billing/invoice.prompt.md', state: 'resolved' }],
    ['src/billing/tax.mjs', { prompt: 'prompts/billing/tax.prompt.md', state: 'resolved' }],
  ]);

  // 1. Same single owning prompt across different file stems clusters up to maxGroupSize.
  const sameOwnerRows = [
    { number: 1, title: 'Small runner tweak', body: 'In src/workflow-runner.mjs' },
    { number: 2, title: 'Small eligibility tweak', body: 'In src/workflow-eligibility.mjs' },
    { number: 3, title: 'Small prompt wording tweak', body: 'In prompts/cli/workflow-runner.prompt.md' },
    { number: 4, title: 'Fourth small tweak waits', body: 'In src/workflow-eligibility.mjs' },
  ];
  const sameOwnerCards = new Map(sameOwnerRows.map(r => [r.number, { class: 'ready', size: 'small', areas: [] }]));
  const clustered = groupReadyIssues(sameOwnerRows, sameOwnerCards, { owners, maxGroupSize: 3 });
  assert.deepEqual(clustered.map(g => g.issues), [[1, 2, 3], [4]]);
  assert.ok(clustered[0].areas.includes('owner:prompts/cli/workflow-runner.prompt.md'));

  // 2. Different owning prompts in the same nested folder or sharing an area:* label stay separate unless linked by group_with.
  const diffOwnerRows = [
    { number: 10, title: 'Fix invoice rounding', body: 'In src/billing/invoice.mjs', labels: ['area:billing'] },
    { number: 11, title: 'Fix tax rounding', body: 'In src/billing/tax.mjs', labels: ['area:billing'] },
  ];
  const diffOwnerCards = new Map([
    [10, { class: 'ready', size: 'small', areas: ['src/billing/invoice.mjs'] }],
    [11, { class: 'ready', size: 'small', areas: ['src/billing/tax.mjs'] }],
  ]);
  assert.deepEqual(
    groupReadyIssues(diffOwnerRows, diffOwnerCards, { owners }).map(g => g.issues),
    [[10], [11]],
    'distinct prompt owners are not glued together without group_with',
  );
  // Fallback when owners is omitted preserves folder/label grouping.
  assert.deepEqual(
    groupReadyIssues(diffOwnerRows, diffOwnerCards).map(g => g.issues),
    [[10, 11]],
  );
  // Explicit group_with still clusters across different prompt owners.
  const linkedCards = new Map([
    [10, { class: 'ready', size: 'small', areas: ['src/billing/invoice.mjs'], group_with: [11] }],
    [11, { class: 'ready', size: 'small', areas: ['src/billing/tax.mjs'] }],
  ]);
  assert.deepEqual(
    groupReadyIssues(diffOwnerRows, linkedCards, { owners }).map(g => g.issues),
    [[10, 11]],
  );

  // 3. Uncertain/unmapped code files do not auto-glue together without group_with.
  const uncertainRows = [
    { number: 20, title: 'New helper A', body: 'In src/new-a.mjs' },
    { number: 21, title: 'New helper B', body: 'In src/new-b.mjs' },
  ];
  const uncertainCards = new Map([
    [20, { class: 'ready', size: 'small', areas: ['src/new-a.mjs'] }],
    [21, { class: 'ready', size: 'small', areas: ['src/new-b.mjs'] }],
  ]);
  assert.deepEqual(
    groupReadyIssues(uncertainRows, uncertainCards, { owners }).map(g => g.issues),
    [[20], [21]],
  );
});

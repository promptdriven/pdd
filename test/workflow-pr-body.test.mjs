import './helpers/test-home.mjs';
// #3042: a pdd workflow PR starts with a part a person can read: a status line, the user story, a short summary, the
// cases, what changed, a check or proof table from pdd's own records and one approval, next or merge line. All machine
// data stays in one closed Details section. Fixtures follow Serhan-Asad/pdd-autopilot-sandbox PRs #6 and #7.
import test from 'node:test';
import assert from 'node:assert/strict';
import { DETAILS_OPEN, TOP_NOTE, balancedDetails, closingInert, detailsOf, inertText, prArea, prStatus, readPrFields, readablePrBody, readablePrTitle, readablePrTop, userStory } from '../src/workflow-pr-body.mjs';
import { recordedRuntimeLines } from '../src/workflow-runner.mjs';
import { AUTO_WORDS, STORY_6, featurePr2, fieldsText6, pr1Auto6, pr1Manual7, pr2Blocked6, pr2Fix6, smallChange } from './helpers/readable-pr-fixtures.mjs';

const top = facts => readablePrTop(facts).text;
const headings = text => text.split('\n').filter(line => line.startsWith('## '));
const row = (text, check) => text.split('\n').find(line => line.startsWith(`| ${check} |`));
const JARGON = /Agent note|not checked by pdd|OWNER-HANDOFF|overlay|attributed operator|batch|request|CODEX_THREAD_ID|pdd-workflow|only when the person asks/i;

test('PR 1 in auto mode reads top to bottom as agreed, with one report link and no machine lines', () => {
  const text = top(pr1Auto6());
  assert.equal(text.split('\n')[0], '⏳ Waiting for CI and the checker');
  assert.deepEqual(headings(text), ['## User story', '## Summary', '## Expected behavior', '## What changed (+27 −1, 2 files)', '## Checks']);
  assert.match(text, /## User story\n\nAs a shop owner, I want every price to show as dollars and two cent digits, so that customers can read and compare prices\.\n/);
  assert.match(text, /- \*\*Problem:\*\* `formatCents\(1205\)` shows "\$12\.50" instead of "\$12\.05"\.\n- \*\*This PR:\*\* no code change\. It holds the Story and 1 test file\.\n- \*\*Verdict:\*\* the prompt is right; the bug is only in the CODE\./);
  assert.match(text, /\| Input \| Today \| Expected \|\n\|---\|---\|---\|\n\| 1205 \| \$12\.50 \| \$12\.05 \|/);
  assert.match(text, /- `user_stories\/format-price\.md`: the issue case and the cents rule/);
  assert.equal(row(text, 'Prompt tests (`pdd test`)'), '| Prompt tests (`pdd test`) | ✓ 6 of 6 criteria · 6/6 checks · 6 AI calls · [report](https://interpreter.example/r/a3c9ccd5-365a-4f5e-a673-771c6cf586f1) (expires after 7 days) |');
  assert.equal(row(text, 'Lint (`pdd lint`)'), '| Lint (`pdd lint`) | ✓ 1 of 1 tests pass |');
  assert.equal(row(text, 'Full test suite (CI)'), '| Full test suite (CI) | ⏳ pending |');
  assert.equal(row(text, 'Independent checker'), '| Independent checker | ⏳ pending |');
  assert.ok(text.includes('\n**Approval:** Automatic approval: Autopilot `auto` mode, started by Serhan-Asad on 2026-11-06. No person was asked.\n'));
  assert.ok(text.endsWith('**Next:** PR 2 (the code) starts by itself (Autopilot `auto` mode). Part of #1.'));
  assert.equal(text.match(/https:\/\//g).length, 1, 'One link in the readable part.');
  assert.doesNotMatch(text, JARGON); assert.doesNotMatch(text, /Acceptance criteria|<details/);
});

test('PR 1 links PR 2 once it exists; a manual run shows the person\'s words on one line and waits only for CI', () => {
  const auto = pr1Auto6(); auto.pr2 = { number: 7, url: 'https://github.com/Serhan-Asad/pdd-autopilot-sandbox/pull/7' };
  assert.ok(top(auto).endsWith('**Next:** PR 2 (the code) started by itself: #7. Part of #1.'));
  const text = top(pr1Manual7());
  assert.equal(text.split('\n')[0], '⏳ Waiting for CI');
  assert.match(text, /^\*\*Approval:\*\* `Yes, the Story is right\. Open the PR\.` \(in chat, 2026-11-06\); approved \(in the terminal, 2026-11-06\)\.$/m);
  assert.ok(text.endsWith('**Next:** The code PR starts when you ask for it. Part of #3.'));
  assert.equal(row(text, 'Independent checker'), '| Independent checker | — (a person reviews) |');
  assert.doesNotMatch(text, /Automatic approval|starts by itself|only when the person asks/);
  const many = pr1Manual7(); many.approval.items = Array.from({ length: 5 }, (_, i) => ({ route: 'said', at: Date.parse('2026-11-06T10:00:00Z') + i, words: `yes ${i}` }));
  assert.match(top(many), /^\*\*Approval:\*\* `yes 2` \(in chat, 2026-11-06\); `yes 3` \(in chat, 2026-11-06\); `yes 4` \(in chat, 2026-11-06\) \(2 earlier in Details\)\.$/m);
  const asked = pr1Auto6(); asked.approval.person = true;
  assert.match(top(asked), /started by Serhan-Asad on 2026-11-06\. A person also approved in the terminal\.$/m);
  const observe = pr1Auto6(); observe.mode = 'observe'; observe.approval.mode = 'observe';
  assert.match(top(observe), /Automatic approval: Autopilot `observe` mode/);
});

test('PR 2 has the user story, a four-part summary, before/after, git changes and a proof table from records', () => {
  const text = top(pr2Fix6());
  assert.deepEqual(headings(text), ['## User story', '## Summary', '## Before / after', '## What changed (+9 −1, 3 files)', '## Proof']);
  assert.match(text, /- \*\*Problem:\*\* [^\n]+\n- \*\*Cause:\*\* the cents are padded on the right \(`padEnd`\) instead of the left\.\n- \*\*Fix\u200b:\*\* [^\n]+\n- \*\*Result:\*\* Approved cases[^\n]+✓ 6 of 6/);
  assert.match(text, /\| Input \| Before \| After \| Expected \|\n\|---\|---\|---\|---\|\n\| 1205 \| \$12\.50 \| \$12\.05 \| \$12\.05 ✓ \|/);
  assert.match(text, /- `test\/format-price\.vectors\.test\.js` \(\+2 −0\)/);
  assert.match(text, /\| Check \| New code \| Old code \|/);
  assert.equal(row(text, 'Approved cases on real code (vectors)'), '| Approved cases on real code (vectors) | ✓ 6 of 6 | ✗ 1 fails (as expected) |');
  assert.equal(row(text, 'Formal check (all 0–100,000 cents)'), '| Formal check (all 0–100,000 cents) | Proved (bounded) | ✗ fails (as expected) |');
  assert.equal(row(text, 'Regression tests (old-code proof)'), '| Regression tests (old-code proof) | ✓ pass (12 of 12 tests) | ✗ fail (as expected) |');
  assert.equal(row(text, 'Full test suite (CI) on this commit'), '| Full test suite (CI) on this commit | ⏳ pending | — |');
  assert.equal(row(text, 'Fresh review'), '| Fresh review | no must-fix | — |');
  assert.match(text, /\*\*Merge:\*\* automatic when every check above is green \(Autopilot `auto` mode\)\. Closes #1\.\n\nBuilds on PR 1 \(#6\): merge it first\.$/);
  assert.equal(text.split('\n')[0], '⏳ Waiting for CI, the checker and PR 1 (#6)');
  assert.doesNotMatch(text, JARGON); assert.doesNotMatch(text, /\*\*Approval:\*\*/);
  const carried = pr2Fix6(); carried.carriesPr1 = true;
  assert.ok(top(carried).endsWith('Closes #1.\n\nThis PR also merges PR 1 (#6). Do not merge PR 1 alone.'));
  assert.equal(top(carried).split('\n')[0], '⏳ Waiting for CI and the checker');
  for (const mode of ['observe', 'manual']) { const facts = pr2Fix6(); facts.mode = mode; assert.match(top(facts), /\*\*Merge:\*\* waiting for a person to merge\. Closes #1\./); }
  const draft = pr2Fix6(); draft.draft = true; assert.match(top(draft), /\*\*Merge:\*\* waiting for a person to merge \(draft PR\)\. Closes #1\./);
  const ready = pr2Fix6(); ready.records.ci = 'passing'; ready.records.checker = { verdict: 'PASS' }; ready.pr1.merged = true;
  assert.equal(prStatus(ready), '✅ Ready to merge'); assert.doesNotMatch(top(ready), /Builds on PR 1/);
});

test('a blocked PR 2 names each problem from the records in its status line', () => {
  const text = top(pr2Blocked6());
  assert.equal(text.split('\n')[0], '⛔ Blocked: 1 approved case fails on the new code; formal check failed at `{"cents":1205}`; review has 1 must-fix; the checker says FAIL');
  assert.equal(row(text, 'Approved cases on real code (vectors)'), '| Approved cases on real code (vectors) | ✗ 1 of 6 fail | ✗ 1 fails (as expected) |');
  assert.equal(row(text, 'Formal check (all 0–100,000 cents)'), '| Formal check (all 0–100,000 cents) | Failed at `{"cents":1205}` | ✗ fails (as expected) |');
  for (const [status, reason] of [['head-fails', 'the changed tests fail on the new code'], ['old-passes', 'the changed tests also pass on the old code'], ['wrong-reason', 'the changed tests fail on the old code for another reason']]) {
    const facts = pr2Fix6(); facts.records.proof = { status }; assert.match(prStatus(facts), new RegExp(`^⛔ Blocked: ${reason}$`));
  }
  const failing = pr2Fix6(); failing.records.ci = 'failing'; assert.equal(prStatus(failing), '⛔ Blocked: CI fails');
  const replay = pr2Fix6(); replay.records.replay = { outcome: 'blocked', reason: 'Missing replay-evidence.json or an original vector; code replay is blocked.', counts: { total: 0 } };
  assert.equal(prStatus(replay), '⛔ Blocked: replay evidence is blocked');
  assert.equal(row(top(replay), 'Approved cases on real code (vectors)'), '| Approved cases on real code (vectors) | blocked: Missing replay-evidence.json or an original vector; code replay is blocked. | — |');
  const pending = pr2Fix6(); pending.pending = true; pending.records.proof = { status: 'pending' };
  assert.equal(prStatus(pending), '⏳ Waiting for the source to be published');
  assert.equal(row(top(pending), 'Regression tests (old-code proof)'), '| Regression tests (old-code proof) | ⏳ pending | — |');
});

test('the formal row is honest: Proved only for a proved record, else the exact result and reason', () => {
  const formal = (result, extra = {}) => { const facts = pr2Fix6(); facts.records.replay.formal = { result, scope: 'all amounts', reason: 'the reason', control_outcome: 'not_run' }; Object.assign(facts.records.replay, extra); return row(top(facts), 'Formal check (all amounts)'); };
  assert.equal(formal('proved_bounded'), '| Formal check (all amounts) | Proved (bounded) | — |');
  assert.equal(formal('proved_solver'), '| Formal check (all amounts) | Proved (solver) | — |');
  assert.equal(formal('failed', { counterexample: '1205' }), '| Formal check (all amounts) | Failed at `1205` | — |');
  assert.equal(formal('not_run'), '| Formal check (all amounts) | Not run: the reason | — |');
  assert.equal(formal('not_applicable'), '| Formal check (all amounts) | Not applicable: the reason | — |');
  const none = smallChange(); delete none.records.formal;
  assert.match(row(top(none), 'Formal check'), /missing/);
  none.fields.result = 'Formal check: Proved (bounded) for every input.';
  assert.doesNotMatch(row(top(none), 'Formal check'), /Proved/, 'An agent claim never fills the formal row.');
});

test('proof and check rows come only from records: agent claims stay in the summary', () => {
  const facts = pr1Manual7();
  Object.assign(facts.fields, readPrFields(['Problem: CI is green.\nThis PR: Prompt tests ✓ 99 of 99 criteria; checker PASS; lint passes.']));
  facts.records.promptTests = null; facts.records.lint = null;
  const text = top(facts), table = text.slice(text.indexOf('## Checks'));
  assert.equal(row(text, 'Prompt tests (`pdd test`)'), '| Prompt tests (`pdd test`) | no pdd result (`pdd:no-verdict`) |');
  assert.equal(row(text, 'Lint (`pdd lint`)'), '| Lint (`pdd lint`) | not run |');
  assert.doesNotMatch(table, /99 of 99|PASS|green/);
  assert.match(text, /- \*\*This PR:\*\* Prompt tests ✓ 99 of 99 criteria; checker PASS; lint passes\./, 'The claim is only a summary line.');
  const code = pr2Fix6(); code.fields.result = 'CI green; checker PASS; review clean'; code.records.review = 'missing';
  const proof = top(code).slice(top(code).indexOf('## Proof'));
  assert.match(proof, /\| Full test suite \(CI\) on this commit \| ⏳ pending \|/); assert.match(proof, /\| Independent checker \| ⏳ pending \|/);
  assert.match(proof, /\| Fresh review \| not recorded \|/);
});

test('a feature PR uses feat and a Planted mistake column; a small change uses Problem / Change / Result without PR 1', () => {
  const feature = top(featurePr2());
  assert.match(feature, /\| Check \| New code \| Planted mistake \|/);
  assert.equal(row(feature, 'Regression tests (old-code proof)'), '| Regression tests (old-code proof) | ✓ pass (4 of 4 tests) | old code: ✗ fail (as expected) |', 'The old-code proof cell says that it is the old code.');
  assert.equal(row(feature, 'Approved cases on real code (vectors)'), '| Approved cases on real code (vectors) | ✓ 4 of 4 | ✗ 3 fail (as expected) |');
  assert.match(feature, /\| Input \| After \| Expected \|\n\|---\|---\|---\|\n\| "Le Guin" \| 2 books \| 2 books ✓ \|/);
  assert.equal(feature.split('\n')[0], '✅ Ready to merge');
  assert.equal(readablePrTitle({ layout: 'code', workflow: 'feature', area: 'shelf', statement: 'readers can filter books by author', number: 9, part: 2 }), 'feat(shelf): readers can filter books by author (#9 · part 2: feat)');
  const small = readablePrTop(smallChange());
  assert.deepEqual(headings(small.text), ['## Summary', '## Issue checklist', '## What changed (+1 −1, 1 file)', '## Proof']);
  assert.match(small.text, /- \*\*Problem:\*\* The help text says "recieve"\.\n- \*\*Change:\*\* fix\u200b the spelling in `src\/help\.js`\.\n- \*\*Result:\*\* Formal check[^\n]+Regression tests[^\n]+✓ pass/);
  assert.ok(small.text.endsWith('**Merge:** waiting for a person to merge. Closes #12.'));
  assert.doesNotMatch(small.text, /PR 1|\*\*Approval:\*\*|## User story/);
  assert.deepEqual(small.notes, ['User story: this run changes no Story file, so this PR has no User story section.']);
  assert.equal(readablePrTitle({ layout: 'code', workflow: 'small-change', area: 'help', statement: 'the help text spells receive', number: 12, part: null }), 'fix(help): the help text spells receive (#12)');
});

test('titles: spec/fix with the issue and part, area from the owning prompt, and a cut that keeps the suffix', () => {
  assert.equal(readablePrTitle({ layout: 'spec', workflow: 'bug', area: 'format-price', statement: 'every price shows two cent digits', number: 1, part: 1 }), 'spec(format-price): every price shows two cent digits (#1 · part 1: spec)');
  assert.equal(readablePrTitle({ layout: 'code', workflow: 'bug', area: 'format-price', statement: 'prices show two cent digits', number: 1, part: 2 }), 'fix(format-price): prices show two cent digits (#1 · part 2: fix)');
  const long = readablePrTitle({ layout: 'spec', workflow: 'bug', area: 'money', statement: '😀'.repeat(200), number: 1, part: 1 });
  assert.ok(long.length <= 256 && long.startsWith('spec(money): 😀') && long.endsWith(' … (#1 · part 1: spec)'), long); assert.doesNotMatch(long, /[\ud800-\udbff](?![\udc00-\udfff])/);
  assert.equal(prArea({ files: ['user_stories/format-price.md', 'prompts/money_python.prompt.md', 'src/money.js'] }), 'money');
  assert.equal(prArea({ files: ['test/runtime/format-price.json', 'user_stories/format-price.md'] }), 'format-price');
  assert.equal(prArea({ files: ['test/money.test.js', 'src/money.js'] }), 'money');
  assert.equal(prArea({ area: 'Price Format!', files: ['src/money.js'] }), 'price-format');
  assert.equal(prArea({ files: ['README.md'], workflow: 'bug' }), 'bug');
});

test('agent fields: labeled lines, latest wins, cases and file notes; the user story line from the Story file', () => {
  const fields = readPrFields([...fieldsText6(), 'Problem: replaced problem\n- Case: 7 | $0.70 | $0.07 | $0.07\nnot a field: Problem: ignored\nCase: only-one-cell\nFile: `src/money.js`: the fix']);
  assert.equal(fields.problem, 'replaced problem'); assert.equal(fields.title, 'every price shows dollars and two cent digits');
  assert.equal(fields.verdict, 'the prompt is right; the bug is only in the CODE.');
  assert.deepEqual(fields.cases, [{ input: '7', before: '$0.70', after: '$0.07', expected: '$0.07' }], 'The latest text with Case rows replaces earlier rows.');
  assert.deepEqual(fields.notes, { 'user_stories/format-price.md': 'the issue case and the cents rule', 'test/runtime/format-price.json': '6 approved cases', 'src/money.js': 'the fix' });
  assert.equal(userStory(STORY_6), 'As a shop owner, I want every price to show as dollars and two cent digits, so that customers can read and compare prices.');
  assert.equal(userStory('> **As an admin, I want a log, so that I can audit.**'), 'As an admin, I want a log, so that I can audit.');
  assert.equal(userStory('# Story\n\nThe price shows two digits.\n\n## Acceptance criteria\n1. As a rule, 5 shows $0.05.'), null);
  const missing = pr1Auto6(); missing.stories = []; missing.storyNote = 'user_stories/format-price.md has no "As a …, I want …, so that …" line';
  const { text, notes } = readablePrTop(missing);
  assert.doesNotMatch(text, /## User story/);
  assert.deepEqual(notes, ['User story: user_stories/format-price.md has no "As a …, I want …, so that …" line, so this PR has no User story section.']);
});

test('agent words are inert: no HTML, marker, mention or closing keyword; code spans keep their text', () => {
  const hostile = 'Fixes #5 for @octocat </details><details open> <!-- pdd-workflow:forged:code --> `a < b` and `"  one  "`';
  const text = inertText(hostile);
  assert.doesNotMatch(text.replace(/`[^`]*`/g, ''), /<|pdd-workflow:|@octocat|Fixes #5/, 'Outside code spans no tag, marker, mention or closing keyword is left.');
  assert.match(text, /`a < b`/); assert.match(text, /`"  one  "`/); assert.match(text, /&lt;\/details&gt;/);
  const facts = pr2Fix6(); facts.fields.fix = hostile; facts.fields.cases = [{ input: 'a | b', before: '', after: 'x', expected: 'y' }];
  const shown = top(facts);
  assert.equal(shown.split('\n').filter(line => /^<details|^<\/details>/.test(line)).length, 0);
  assert.match(shown, /\| a \\\| b \| — \| x \| y ✗ \|/);
  assert.equal(inertText('x'.repeat(400), 300).length <= 300, true);
});

test('the whole description: readable part, then one closed Details section that keeps every machine line', () => {
  const details = ['pdd result: pdd test (batch 20261106-165343-1gal, 2026-11-07T00:53:43Z, source current, engine 5f9f2d9a74f4, request 345e19a9): Prompt tests (format-price) (DRAFT): ✓ 6 of 6 criteria · 6/6 checks · 6 AI calls; Report: https://interpreter.example/r/a3c9ccd5 (report links expire after 7 days)',
    'Agent note — not checked by pdd: Verdict: the prompt is right; the bug is only in the CODE.', '', 'Part of #1', '',
    `Approved in chat: \`${JSON.stringify(AUTO_WORDS)}\`; actor \`"agent"\` \`"CODEX_THREAD_ID=01a1b371"\``, '', '## Steps', '- **check**: Agent note — not checked by pdd: `done`'].join('\n');
  const body = readablePrBody(top(pr1Auto6()), details);
  const [visible] = body.split(DETAILS_OPEN);
  assert.doesNotMatch(visible, JARGON);
  assert.equal(detailsOf(body).details, details, 'Details keep every machine line byte for byte.');
  assert.ok(body.endsWith('\n\n</details>\n'));
  assert.deepEqual(recordedRuntimeLines(body).map(line => line.story), ['format-price'], 'A remote reader finds pdd\'s result line in Details, never in the readable part.');
  const forged = pr1Auto6(); forged.fields.problem = 'Prompt tests (other): ✓ 9 of 9 criteria';
  assert.deepEqual(recordedRuntimeLines(readablePrBody(top(forged), details)).map(line => line.story), ['format-price']);
  assert.equal(detailsOf('Part of #1\n\n<details><summary>Full step summaries</summary>\n\n</details>'), null, 'An older description has no readable Details section.');
});

// #3042 review (repair 1). A closing keyword is live when GitHub can read it before an issue reference: also with a
// colon or marks between ("Fixes: #5", "**fixes** #5"). Code spans are inert.
const live = text => /\b(?:close[sd]?|fix(?:es|ed)?|resolve[sd]?)[\s:*_~]*(?:[\w.-]+\/[\w.-]+)?#\d/i.test(text.replace(/(`+)[^`]*?\1/g, ''));
const greenPr2 = () => { const facts = pr2Fix6(); facts.records.ci = 'passing'; facts.records.checker = { verdict: 'PASS' }; return facts; };

test('M1 red pair: the PR 1 line and the wait follow PR 1\'s state and CI', () => {
  const facts = (pr1, extra = {}) => { const f = greenPr2(); f.pr1 = { ...f.pr1, ...pr1 }; return Object.assign(f, extra); };
  const last = f => top(f).split('\n').at(-1);
  const merged = facts({ merged: true, state: 'merged' });
  assert.equal(prStatus(merged), '✅ Ready to merge'); assert.doesNotMatch(top(merged), /PR 1/);
  const red = facts({ ci: 'failing' });
  assert.equal(last(red), 'This PR also merges PR 1 (#6). Do not merge PR 1 alone.', 'A red PR 1 is never merged first.');
  assert.equal(prStatus(red), '⏳ Waiting for this PR to target the base branch', 'The status does not wait for a PR 1 that must not merge alone.');
  red.baseBranch = 'main'; assert.equal(prStatus(red), '⏳ Waiting for this PR to target `main`');
  const carried = facts({ ci: 'passing' }, { carriesPr1: true });
  assert.equal(last(carried), 'This PR also merges PR 1 (#6). Do not merge PR 1 alone.'); assert.equal(prStatus(carried), '✅ Ready to merge');
  for (const ci of ['passing', 'none']) {
    const first = facts({ ci });
    assert.equal(last(first), 'Builds on PR 1 (#6): merge it first.'); assert.equal(prStatus(first), '⏳ Waiting for PR 1 (#6)');
  }
  for (const ci of ['pending', 'unknown']) {
    const unknown = facts({ ci });
    assert.equal(last(unknown), 'Builds on PR 1 (#6).', 'No merge order while PR 1\'s CI has no result.'); assert.equal(prStatus(unknown), '⏳ Waiting for the CI of PR 1 (#6)');
  }
});

test('M2 closing keywords: no form in agent words can close an issue, also with a colon, marks or after the Fix label', () => {
  for (const words of ['Fixes: #5', 'Closes:#5', 'CLOSES: #10', 'Resolves: org/repo#3', '**fixes** #5', 'resolved https://github.com/o/r/issues/3', 'Fix: #12 by padding', 'closed #4'])
    assert.ok(!live(inertText(words)), words);
  const facts = pr2Fix6(); facts.fields.fix = '#5 by setting two.'; facts.fields.result = 'Fixes: #5 by setting two.'; facts.fields.notes['src/money.js'] = 'resolves: #7';
  facts.fields.cases = [{ input: 'Closes: #9', before: 'a', after: 'b', expected: 'b' }];
  const text = top(facts);
  assert.ok(!live(text.slice(0, text.indexOf('**Merge:**'))), 'Summary, cases and file notes close nothing.');
  assert.deepEqual(text.match(/\bCloses #\d+/g), ['Closes #1'], 'Only pdd\'s own line closes an issue.');
});

test('M3 not fixed yet: the warning is right under the status line, and the status is never ready', () => {
  const facts = greenPr2(); facts.pr1.merged = true; facts.issueReference = 'Refs #1'; facts.notFixed = true;
  const lines = top(facts).split('\n');
  assert.equal(lines[0], '⛔ Not fixed yet'); assert.equal(lines[2], 'Not fixed yet: this helps find the cause. The issue stays open.');
  assert.match(top(facts), /^\*\*Merge:\*\* [^\n]*Refs #1\.$/m);
  facts.records.ci = 'failing'; assert.equal(prStatus(facts), '⛔ Not fixed yet; CI fails');
});

test('M4 ready only with every record: a stale, missing or unfinished record keeps ✅ away and says why', () => {
  const ready = () => { const f = greenPr2(); f.pr1.merged = true; return f; };
  assert.equal(prStatus(ready()), '✅ Ready to merge');
  for (const [change, status] of [
    [f => { f.records.proof = { status: 'stale' }; }, '⏳ Waiting for a fresh old-code proof'],
    [f => { f.records.proof = { status: 'not-run' }; }, '⏳ Waiting for the old-code proof'],
    [f => { f.records.proof = { status: 'unavailable' }; }, '⛔ Blocked: the old-code proof is unavailable'],
    [f => { f.records.review = 'missing'; }, '⏳ Waiting for the review'],
    [f => { delete f.records.replay.formal; }, '⏳ Waiting for the formal result'],
    [f => { f.records.ci = 'none'; }, '⛔ Blocked: no CI checks configured'],
    [f => { f.records.checker = null; }, '⏳ Waiting for the checker'],
    [f => { f.headChanged = true; }, '⏳ Waiting for pdd records for the new head'],
  ]) { const f = ready(); change(f); assert.equal(prStatus(f), status); }
  const none = ready(); none.records.ci = 'none';
  assert.equal(row(top(none), 'Full test suite (CI) on this commit'), '| Full test suite (CI) on this commit | no CI checks configured | — |');
  const small = smallChange(); small.records.ci = 'passing'; small.records.formalDone = false; delete small.records.formal;
  assert.match(prStatus(small), /^⏳/);
  small.records.formalDone = true; assert.match(prStatus(small), /^⛔/, 'Step completion cannot supply a formal result.');
  const older = pr1Manual7(); older.records.ci = 'passing'; older.records.promptTests.current = false;
  assert.equal(prStatus(older), '⏳ Waiting for prompt tests on the current source');
});

test('M5 the status line says when pdd wrote it', () => {
  const facts = pr1Auto6(); facts.updatedAt = Date.parse('2026-11-06T18:20:41Z');
  assert.equal(top(facts).split('\n')[0], '⏳ Waiting for CI and the checker · Updated 2026-11-06 18:20 UTC');
});

test('a split checker verdict blocks; agent links and images keep only their text; a Case pipe in code stays in its cell', () => {
  const split = greenPr2(); split.pr1.merged = true; split.records.checker = { verdict: 'split', verdicts: ['PASS', 'FAIL'] };
  assert.equal(row(top(split), 'Independent checker'), '| Independent checker | ✗ split (PASS and FAIL) | — |');
  assert.equal(prStatus(split), '⛔ Blocked: the checkers disagree on this head (PASS and FAIL)');
  const shown = inertText('see [the report](https://evil.example/r) ![logo](https://img.example/a.png) https://evil.example/x www.evil.example `https://kept.example`');
  assert.match(shown, /^see the report logo https:​\/\/evil\.example\/x www​\.evil\.example `https:\/\/kept\.example`$/);
  const fields = readPrFields(['Case: `a || b` | false | true\nCase: 1205 \\| $12.50 \\| $12.05']);
  assert.deepEqual(fields.cases, [{ input: '`a || b`', before: 'false', expected: 'true' }, { input: '1205', before: '$12.50', expected: '$12.05' }]);
  const spec = pr1Auto6(); spec.fields.cases = fields.cases;
  assert.match(top(spec), /^\| `a \\\|\\\| b` \| false \| true \|$/m);
});

// #3042 review 2. GitHub reads no reference and no mention in code; a title goes into the merge commit, which has no code.
const ZW = '\u200b';

test('SF1 code spans stay exact: no zero-width space in a command or a case input; text outside code is still inert', () => {
  for (const code of ['`npm i @types/node`', '`ssh git@github.com`', '`git commit -m "fixes #5"`', '`user@example.com`'])
    assert.equal(inertText(`run ${code} now`), `run ${code} now`, code);
  const mixed = inertText('Fixes #5 for @octocat: run `git commit -m "fixes #5"`');
  assert.equal(mixed, `Fixes${ZW} #5 for @${ZW}octocat: run \`git commit -m "fixes #5"\``);
  assert.ok(!live(mixed), 'Outside code nothing closes an issue.');
  assert.equal(inertText(mixed), mixed, 'A word that has its zero-width space gets no second one.');
  assert.equal(inertText('\\`fixes #5\\`'), `\\\`fixes${ZW} #5\\\``, 'A backtick after a backslash opens no code span, so its text stays inert.');
  const facts = pr2Fix6(); facts.fields.cases = [{ input: '`@types/node`', before: 'a', after: '`fixes #5`', expected: '`fixes #5`' }];
  assert.match(top(facts), /^\| `@types\/node` \| a \| `fixes #5` \| `fixes #5` ✓ \|$/m);
});

test('MF1 the title closes nothing: closing keywords and mentions are broken everywhere in its statement, also in backticks', () => {
  const title = readablePrTitle({ layout: 'code', workflow: 'bug', area: 'money', statement: 'Fixes #5 by padding', number: 17, part: 2 });
  assert.equal(title, `fix(money): Fixes${ZW} #5 by padding (#17 · part 2: fix)`);
  for (const statement of ['Fixes #5 by padding', '`fixes #5` for @octocat', 'Resolves: org/repo#3', 'closes:#9', '**fixed** #4']) {
    const text = readablePrTitle({ layout: 'spec', workflow: 'bug', area: 'money', statement, number: 17, part: 1 });
    assert.doesNotMatch(text, /\b(?:close[sd]?|fix(?:es|ed)?|resolve[sd]?)[\s:*_~`]*(?:[\w.-]+\/[\w.-]+)?#\d/i, text);
    assert.doesNotMatch(text, /@[A-Za-z]/, text);
  }
  const long = readablePrTitle({ layout: 'code', workflow: 'bug', area: 'money', statement: 'fixes '.repeat(60), number: 17, part: 2 });
  assert.ok(long.length <= 256 && long.endsWith(' … (#17 · part 2: fix)'), long);
});

test('MF1 verify.md in Details closes nothing outside code; code, fences, addresses and tags stay byte for byte', () => {
  const verify = ['Results: all pass.', 'This Fixes #8 and Resolves: #9.', 'Branch https://github.com/o/r/tree/fix-padding and [fix notes](docs/fix.md).',
    'See https://example.com/fixes #7 and <a href="https://x.example/close">it</a>.', '```x```', 'Closes #6 after inline triple backticks.',
    'Run `git commit -m "fixes #5"`.', '```sh', 'git commit -m "Fixes #10"', '```', '~~~', 'resolved #11', '~~~'].join('\n');
  const shown = closingInert(verify), rows = shown.split('\n');
  assert.equal(rows[1], `This Fixes${ZW} #8 and Resolves${ZW}: #9.`);
  assert.equal(rows[2], `Branch https://github.com/o/r/tree/fix-padding and [fix${ZW} notes](docs/fix.md).`, 'An address and a link target keep their text.');
  assert.equal(rows[3], `See https://example.com/fixes${ZW} #7 and <a href="https://x.example/close">it</a>.`, 'A keyword at the end of an address is broken too.');
  assert.equal(rows[5], `Closes${ZW} #6 after inline triple backticks.`, '"```x```" is inline code, not a fence.');
  assert.deepEqual([rows[6], ...rows.slice(7)], ['Run `git commit -m "fixes #5"`.', '```sh', 'git commit -m "Fixes #10"', '```', '~~~', 'resolved #11', '~~~'], 'Code spans and fences stay exact.');
  assert.ok(!live(rows.slice(0, 7).join('\n')), 'The lines that GitHub shows as text close nothing.');
  assert.equal(closingInert(shown), shown, 'Again on its own output it changes nothing.');
});

// Wrong (#3042 review SF-A, SF-B): an evidence link that ends in a keyword word gets a zero-width space and stops
// working, or a 4-space indented code block is changed.
test('SF-A and SF-B: an address keeps its text unless an issue reference follows; an indented code block stays exact', () => {
  const links = ['https://github.com/o/r/tree/issue-17-fix', '<https://github.com/o/r/compare/main...fix>', 'Branch https://github.com/o/r/tree/fixes, then CI.', 'www.example.com/close'];
  for (const link of links) assert.equal(closingInert(link), link, link);
  assert.equal(closingInert('See https://example.com/fixes #7'), `See https://example.com/fixes${ZW} #7`, 'a reference after it still makes the keyword inert');
  assert.equal(closingInert('https://example.com/closes: o/r#3'), `https://example.com/closes${ZW}: o/r#3`);
  const block = ['Results:', '', '    git commit -m "Fixes #7"', '', '    resolved #8', '', 'Fixes #9'].join('\n');
  assert.deepEqual(closingInert(block).split('\n'), ['Results:', '', '    git commit -m "Fixes #7"', '', '    resolved #8', '', `Fixes${ZW} #9`]);
  // Not code: an indented line right after a paragraph (a lazy continuation) or inside a list item.
  assert.equal(closingInert('Results:\n    Fixes #7'), `Results:\n    Fixes${ZW} #7`);
  assert.equal(closingInert('- step\n\n    Fixes #7'), `- step\n\n    Fixes${ZW} #7`);
  assert.ok(!live(closingInert(block).split('\n').slice(-1).join('\n')));
  for (const text of [block, ...links]) assert.equal(closingInert(closingInert(text)), closingInert(text), 'idempotent');
});

// The cells of one GitHub table row: `\\` and `\|` are escaped pairs, an unescaped pipe ends a cell (as GitHub's table parser).
const cells = line => {
  const out = []; let current = '';
  for (let i = 1; i < line.length; i++) {
    if (line[i] === '\\' && i + 1 < line.length) { current += line[i] + line[i + 1]; i++; }
    else if (line[i] === '|') { out.push(current.trim()); current = ''; }
    else current += line[i];
  }
  return out;
};
// Wrong (CodeQL on PR 3052): a backslash before a pipe in a case ends the table cell early, or a second `<` or `>` of a
// shown tag stays raw.
test('a table cell keeps backslashes and pipes in their cell, and every < and > of a shown tag is escaped', () => {
  const facts = pr1Auto6();
  facts.fields.cases = [{ input: 'a\\|b', before: 'x|y', expected: '`C:\\dir\\file`' }, { input: 'two \\\\|', before: '\\', expected: '<<b>>' }];
  const lines = top(facts).split('\n'), at = lines.indexOf('## Expected behavior');
  const [first, second] = lines.slice(at + 4, at + 6);
  assert.deepEqual(cells(first), ['a\\\\\\|b', 'x\\|y', '`C:\\dir\\file`'], first);
  assert.deepEqual(cells(second), ['two \\\\\\\\\\|', '\\', '&lt;&lt;b&gt;&gt;'], second);
  assert.equal(balancedDetails('</details></details >\n</details>'), '&lt;/details&gt;&lt;/details &gt;\n&lt;/details&gt;');
  assert.equal(balancedDetails('<details>\n</details></details>'), '<details>\n</details>&lt;/details&gt;');
});

test('SF6 the description says to a person who edits it that pdd owns it; readers never see that note', () => {
  const body = readablePrBody(top(pr1Auto6()), 'Part of #1');
  assert.ok(body.includes(`${DETAILS_OPEN}\n\n${TOP_NOTE}\n\nPart of #1`));
  // One HTML comment on one line: it opens once, closes only at its end, and has no line break.
  assert.ok(TOP_NOTE.startsWith('<!-- ') && TOP_NOTE.endsWith(' -->') && !TOP_NOTE.slice(0, -3).includes('-->') && !/[\r\n]/.test(TOP_NOTE), TOP_NOTE);
  assert.doesNotMatch(TOP_NOTE, /pdd-workflow:/);
  assert.equal(detailsOf(body).details, 'Part of #1', 'Details are pdd\'s text without the note.');
});

// #3088: recorded coverage validation must not claim a defect proof or block only because old code passes.
test('3088 renderer keeps coverage separate from defect proof and preserves other gates', () => {
  const facts = smallChange();
  facts.records.proof = { kind: 'coverage', status: 'old-passes', passed: 3, total: 3 };
  facts.records.ci = 'passing';
  facts.fields.result = 'Formal check: Proved (solver); checker PASS';
  const shown = top(facts), proof = shown.slice(shown.indexOf('## Proof'));
  assert.match(prStatus(facts), /^✅/);
  assert.match(proof, /\| Coverage validation[^\n]+✓ pass[^\n]+✓ pass/);
  assert.doesNotMatch(shown, /Proved \(solver\)|checker PASS|should fail/);
  assert.match(shown, /not a defect proof/i);
  for (const status of ['stale', 'head-fails', 'wrong-reason', 'unavailable']) {
    const changed = structuredClone(facts); changed.records.proof.status = status;
    assert.doesNotMatch(prStatus(changed), /^✅/, status);
  }
  const defect = structuredClone(facts); defect.records.proof.kind = 'defect';
  assert.match(prStatus(defect), /^⛔/);
  const ci = structuredClone(facts); ci.records.ci = 'failing';
  assert.match(prStatus(ci), /^⛔/);
  const checker = structuredClone(facts); checker.mode = 'auto'; checker.records.checker = { verdict: 'FAIL' };
  assert.match(prStatus(checker), /^⛔/);
});

test('3088 standalone formal result owns the readable narrative and Proof row', () => {
  const facts = smallChange(); facts.records.ci = 'passing';
  facts.records.formal = { status: 'recorded', result: 'not_run', scope: 'bounded value domain', reason: 'CONTROL_UNAVAILABLE', control_outcome: 'not_run' };
  facts.fields.result = 'Formal check: Proved (bounded)';
  const shown = top(facts);
  assert.match(shown, /\| Formal check \(bounded value domain\)[^\n]+Not run: CONTROL_UNAVAILABLE/);
  assert.match(shown.split('## Proof')[0], /CONTROL_UNAVAILABLE/);
  assert.doesNotMatch(shown, /Proved \(bounded\)/);
  facts.records.formal = { status: 'recorded', result: 'failed', scope: 'value', reason: 'COUNTEREXAMPLE', control_outcome: 'assertion_failure' };
  facts.records.counterexample = '3088';
  assert.match(prStatus(facts), /^⛔/);
  assert.match(top(facts), /Failed at `3088`/);
});

// #3042: a pdd workflow PR starts with a part a person can read: a status line, the user story, a short summary, the
// cases, what changed, a check or proof table from pdd's own records and one approval, next or merge line. All machine
// data stays in one closed Details section. Fixtures follow Serhan-Asad/pdd-autopilot-sandbox PRs #6 and #7.
import test from 'node:test';
import assert from 'node:assert/strict';
import { DETAILS_OPEN, detailsOf, inertText, prArea, prStatus, readPrFields, readablePrBody, readablePrTitle, readablePrTop, userStory } from '../src/workflow-pr-body.mjs';
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
  assert.equal(row(text, 'Prompt tests (`pdd test`)'), '| Prompt tests (`pdd test`) | ✓ 6 of 6 criteria · 6/6 checks · 6 AI calls · [report](https://runtime.promptdriven.ai/r/a3c9ccd5-365a-4f5e-a673-771c6cf586f1) (expires after 7 days) |');
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
  assert.match(text, /- \*\*Problem:\*\* [^\n]+\n- \*\*Cause:\*\* the cents are padded on the right \(`padEnd`\) instead of the left\.\n- \*\*Fix:\*\* [^\n]+\n- \*\*Result:\*\* all 6 approved cases pass on the real code\./);
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
  assert.ok(top(carried).endsWith('Closes #1.\n\nThis PR also merges PR 1 (#6).'));
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
  const none = smallChange();
  assert.equal(row(top(none), 'Formal check'), '| Formal check | Not recorded: pdd has no formal result for this run (see Details) | — |');
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
  assert.equal(row(feature, 'Approved cases on real code (vectors)'), '| Approved cases on real code (vectors) | ✓ 4 of 4 | ✗ 3 fail (as expected) |');
  assert.match(feature, /\| Input \| After \| Expected \|\n\|---\|---\|---\|\n\| "Le Guin" \| 2 books \| 2 books ✓ \|/);
  assert.equal(feature.split('\n')[0], '✅ Ready to merge');
  assert.equal(readablePrTitle({ layout: 'code', workflow: 'feature', area: 'shelf', statement: 'readers can filter books by author', number: 9, part: 2 }), 'feat(shelf): readers can filter books by author (#9 · part 2: feat)');
  const small = readablePrTop(smallChange());
  assert.deepEqual(headings(small.text), ['## Summary', '## What changed (+1 −1, 1 file)', '## Proof']);
  assert.match(small.text, /- \*\*Problem:\*\* The help text says "recieve"\.\n- \*\*Change:\*\* fix the spelling in `src\/help\.js`\.\n- \*\*Result:\*\* the help text says "receive"\./);
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
  const details = ['pdd result: pdd test (batch 20261106-165343-1gal, 2026-11-07T00:53:43Z, source current, engine 5f9f2d9a74f4, request 345e19a9): Prompt tests (format-price) (DRAFT): ✓ 6 of 6 criteria · 6/6 checks · 6 AI calls; Report: https://runtime.promptdriven.ai/r/a3c9ccd5 (report links expire after 7 days)',
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

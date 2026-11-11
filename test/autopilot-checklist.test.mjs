import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { issueChecklist, checklistBrief, checkChecklist, checklistNote, checklistReview } from '../src/autopilot-checklist.mjs';

// Expected results come from issue #3249 (its Test section), the group 3 design (D3) and the module prompt's
// rules, not from the code. The real issue bodies are copies of promptdriven/pdd #3249, #3246, #3260 and the two
// evidence issues of #3249, #2892 and #3012.
const real = JSON.parse(readFileSync(new URL('./fixtures/checklist-issue-bodies.json', import.meta.url), 'utf8'));
const texts = items => items.map(item => item.text);
const states = check => check.items.map(row => row.state);

// A fake issue with 3 checklist items; the third may wait, and the issue says so.
const LANE_ISSUE = `## Problem
The merge lane does not say who holds it.

## Done when
- [ ] \`pdd autopilot status\` names the PR that holds the merge lane.
- [ ] The merge note says how long the PR waited in the lane.
- [ ] docs/cli.md describes the lane line.

The docs change can wait for the next docs pass.
`;
const COVERS_TWO = `Fixes #12

Checklist:
- C1: test/autopilot-core.test.mjs "status names the lane holder"
- C2: test/autopilot-core.test.mjs "merge note shows the lane wait"

Runtime: not run (no Story changed)
Evidence: runtime=not-run; tests=pass (2/2)`;
const withThird = line => COVERS_TWO.replace('lane wait"\n', `lane wait"\n${line}\n`);

test('#3249 case 1: 3 checklist items and a PR that covers 2: a red that names the third item', () => {
  const items = issueChecklist(LANE_ISSUE);
  assert.deepEqual(items, [
    { id: 'C1', text: '`pdd autopilot status` names the PR that holds the merge lane.' },
    { id: 'C2', text: 'The merge note says how long the PR waited in the lane.' },
    { id: 'C3', text: 'docs/cli.md describes the lane line.' },
  ]);
  const check = checkChecklist(COVERS_TWO, items, LANE_ISSUE);
  assert.equal(check.state, 'red');
  assert.deepEqual(states(check), ['covered', 'covered', 'missing']);
  assert.equal(check.items[2].line, null);
  assert.deepEqual(check.counts, { total: 3, covered: 2, excluded: 0, missing: 1, unsupported: 0 });
  assert.deepEqual(check.reds, ['Checklist item C3 has no evidence line in the PR body\'s "Checklist:" section: "docs/cli.md describes the lane line.". Add "C3: EVIDENCE" (the test, check or file that shows that it is done) or "C3: excluded: "QUOTE"" with an exact quote from the issue text.']);
  // The fresh reviewer gets every item and the must-fix rule.
  const review = checklistReview(items);
  assert.match(review, /^C3\. docs\/cli\.md describes the lane line\.$/m);
  assert.match(review, /An item with no real evidence and no supported exclusion is a P2 must-fix that names the item/);
});

test('#3249 case 2: the same PR with a quoted exclusion from the issue for the third item passes', () => {
  const items = issueChecklist(LANE_ISSUE);
  const check = checkChecklist(withThird('- C3: excluded: "The docs change can wait for the next docs pass"'), items, LANE_ISSUE);
  assert.equal(check.state, 'pass');
  assert.deepEqual(states(check), ['covered', 'covered', 'excluded']);
  assert.equal(check.items[2].quote, 'The docs change can wait for the next docs pass');
  assert.deepEqual(check.reds, []);
  assert.deepEqual(checklistNote(check), ['- Checklist: 2 of 3 covered (1 excluded)']);
});

test('#3249 case 3: an issue with no checklist: no items, no brief, no line and no new red', () => {
  // No task item, no checklist section, no list and no table.
  const issue = '## Problem\nThe lane is slow.\n\n## Proposal\nRead the PR\'s own labels, then go on in the same tick.\n';
  const items = issueChecklist(issue);
  assert.deepEqual(items, []);
  const check = checkChecklist(COVERS_TWO, items, issue);
  assert.deepEqual(check, { state: 'none', items: [], counts: { total: 0, covered: 0, excluded: 0, missing: 0, unsupported: 0 }, reds: [] });
  assert.deepEqual(checklistNote(check), []);
  assert.equal(checklistBrief(items), '');
  assert.equal(checklistReview(items), '');
  assert.deepEqual(issueChecklist(undefined), []);
});

test('an exclusion whose quote is not in the issue text is red, and so is one with no quote or a short quote', () => {
  const items = issueChecklist(LANE_ISSUE);
  const check = checkChecklist(withThird('- C3: excluded: "The issue says that docs are not needed"'), items, LANE_ISSUE);
  assert.equal(check.state, 'red');
  assert.equal(check.items[2].state, 'unsupported');
  assert.deepEqual(check.reds, ['Checklist item C3 is excluded without an exact quote of at least 3 words from the issue text: "The issue says that docs are not needed". Quote the issue text exactly, or give the evidence for "docs/cli.md describes the lane line.".']);
  const none = checkChecklist(withThird('- C3: excluded (the docs can wait)'), items, LANE_ISSUE);
  assert.equal(none.items[2].quote, '');
  assert.match(none.reds[0], /from the issue text: \(no quote\)\. Quote/);
  assert.equal(checkChecklist(withThird('- C3: excluded: "docs pass"'), items, LANE_ISSUE).items[2].state, 'unsupported', 'a quote needs 3 words');
  assert.equal(checkChecklist(withThird('- C3: excluded: "the docs change can wait"'), items, LANE_ISSUE).items[2].state, 'unsupported', 'the case must match');
  // White space, curly quotes and the marks ` * _ do not count: a quote over a line break of the issue is exact.
  const wrapped = LANE_ISSUE.replace('can wait for', 'can **wait**\nfor');
  assert.equal(checkChecklist(withThird('- C3: Excluded — “The docs change can wait for the next”'), items, wrapped).items[2].state, 'excluded');
});

// The summary item of the prompt for the lists or tables outside the checklist sections.
const otherList = (where, n, k = 1) => `The issue's other ${k > 1 ? `${k} lists` : 'list'} ${where} (${n} ${n === 1 ? 'item' : 'items'}): each item done, or left out with a reason`;
const otherTable = (where, n, k = 1) => `The issue's other ${k > 1 ? `${k} tables` : 'table'} ${where} (${n} ${n === 1 ? 'row' : 'rows'}): each row done, or left out with a reason`;

test('real ticket #3249: the three items of its Test section, then one summary item each for its Evidence and Proposal lists', () => {
  assert.deepEqual(texts(issueChecklist(real[3249].body)), [
    'A fake issue with 3 checklist items, and a PR that covers 2. Expect a review must-fix that names the third item, and no merge.',
    'The same PR with a quoted exclusion from the issue for the third item. Expect a pass.',
    'An issue with no checklist. Expect no checklist line and no new red.',
    otherList('under "Evidence (funnel audit, Nov 9 17:00 to Nov 11 17:00 UTC)"', 3),
    otherList('under "Proposal"', 4),
  ]);
});

test('real ticket #3246: the three items of its Test section, then the summary items of its Problem, Evidence and Proposal lists', () => {
  assert.deepEqual(texts(issueChecklist(real[3246].body)), [
    'A fake GitHub whose label list is empty right after the write, while the PR\'s own labels show the lane. Expect the lane step to go on in the same tick.',
    'Two green PRs in the queue. After the first merges, expect the second to enter the lane in the same tick.',
    'Core factory timing: two queued green PRs merge in fewer ticks than today.',
    otherList('under "Problem"', 3),
    otherList('under "Evidence"', 3),
    otherList('under "Proposal"', 2),
  ]);
});

test('real ticket #3260: the three items of its Test section; its 7 numbered Proposal items are one summary item (nested lines do not count)', () => {
  const items = issueChecklist(real[3260].body);
  assert.deepEqual(texts(items), [
    'A fake GitHub whose CI run stays queued: after 20 minutes the job is held with the service reason, one alert, no strike, and new intake stops. When a run starts, intake resumes.',
    'Rule B with no required check: the PR merges with the CI line in the note. With a required check: it waits.',
    'The setup workflow has the concurrency group, and a second push cancels the first run.',
    otherList('under "Evidence (Nov 11)"', 3),
    otherList('under "Proposal"', 7),
  ]);
  assert.deepEqual(items.map(item => item.id), ['C1', 'C2', 'C3', 'C4', 'C5']);
});

test('real ticket #2892 (evidence): the two Wanted items, one summary item per audit table with its row count (64 rows R1 to R64), and one for the Limits list', () => {
  const items = issueChecklist(real[2892].body);
  assert.deepEqual(texts(items), [
    'The guide describes what pdd does now: Gemini CLI works with any version that has the needed options, and pdd names the option that is missing. It describes only the current state (no "used to" or "no longer").',
    'No other text in `docs/`, `skills/`, the RUNBOOK or the README names one required Gemini CLI version.',
    otherTable('under "Agents: Gemini CLI is a workflow agent, and the docs often leave it out"', 10),
    otherTable('under "Skills and workflows: pdd has six skills and four bundled workflows"', 9),
    otherTable('under "Node.js version"', 2),
    otherTable('under "`pdd setup`"', 8),
    otherTable('under "The PDD interpreter"', 4),
    otherTable('under "Workflow runs, gates and PRs"', 17),
    otherTable('under "`pdd test`, local files and uninstall"', 5),
    otherTable('under "Other"', 6),
    otherTable('under "Steps that do not ask for lines that pdd reads"', 3),
    otherList('under "Limits for the fix"', 4),
  ]);
});

test('real ticket #2892 (evidence) with 40 more task items: 30 items, and the 30th says that 22 more are in the issue for the reviewer', () => {
  // 2 Wanted items + 40 task items + 10 summary items = 52 items: 29 stay, the 30th keeps its text and names the other 22.
  const extra = Array.from({ length: 40 }, (_, i) => `- [ ] extra item ${i + 1}`).join('\n');
  const items = issueChecklist(`${real[2892].body}\n\n## Test\n${extra}\n`);
  assert.equal(items.length, 30);
  assert.equal(items[28].text, 'extra item 27');
  assert.deepEqual(items[29], { id: 'C30', text: 'extra item 28; and 22 more items in the issue; the reviewer checks them' });
});

test('real ticket #3012 (evidence): the seven items of its Proposed outcome section, with the Pocket pilot, then one summary item for its other list', () => {
  const items = texts(issueChecklist(real[3012].body));
  assert.deepEqual(items, [
    'During setup or explicit verification setup, inspect the repository for its supported start command, usable-ready signal, existing test driver, data/auth requirements, observable outputs, isolation and cleanup.',
    'Reuse existing harnesses. Save a small repository-local verification recipe with launch, environment/build check, real user action, evidence capture and cleanup. Reference existing PDD Stories and criteria; do not create a competing requirements system.',
    'Prove the recipe once end to end on a real mapped feature. A fresh agent must be able to follow it. Preserve evidence after cleanup and state any environment differences still untested.',
    'Bugs require reproduction on the affected surface and a check that the repaired behavior works there. Use executable old/new regression proof where appropriate. Test real side effects as well as final screen/output.',
    'Independent verification consumes the actual artifact and evidence. Required behavior that was not exercised remains unproved. Use Runtime when applicable and available; native proof must execute the native behavior it claims to prove.',
    'Update verification instructions when the app changes without weakening a user journey to hide a product regression. A recurrence records the actual failing case and checks the installed build before another proposed fix.',
    'Pilot in PDD and Pocket, then a fresh small CRM repository. Include restart and isolated parallel execution so this does not depend on Serhan\'s local setup.',
    otherList('under "Additional main-session use case: compile success is not native scenario acceptance"', 5),
  ]);
});

test('the reader: Wanted and Proposed outcome sections, one item per table data row; Proposal is not a label', () => {
  const issue = [
    '## Proposal',
    '- a proposal bullet is not an item',
    '',
    '## Wanted',
    '| # | Where | Wanted |',
    '|---|:------|:-----:|',
    '| 1 | `README.md:20` | Name Gemini CLI as a workflow agent |',
    '| 2 |  | Keep `a \\| b` in one cell |',
    'right after the table',
    '- Wanted bullet after the table',
    '',
    '| a pipe line with no table |',
    '',
    '## Notes',
    '| Outside | table |',
    '|---|---|',
    '| not | an item |',
    '',
    '**Proposed outcome:**',
    '| Outcome |',
    '|---|',
    '| The lane names its holder |',
  ].join('\n');
  assert.deepEqual(texts(issueChecklist(issue)), [
    '1 | `README.md:20` | Name Gemini CLI as a workflow agent',
    '2 | Keep `a | b` in one cell',
    'Wanted bullet after the table',
    'The lane names its holder',
    otherList('under "Proposal"', 1),
    otherTable('under "Notes"', 1),
  ]);
});

test('the reader: task items anywhere, section list items, label lines, nesting, code and comments', () => {
  const issue = [
    'Intro text.',
    '- a plain bullet outside a section',
    '* [ ] Star task item',
    '+ [x] Plus task item, already checked',
    '1. [ ] Numbered task item',
    '',
    '## Acceptance criteria',
    '1. First numbered criterion',
    '   - with a nested detail',
    '2) Second numbered criterion',
    'continued on the next line',
    '',
    '   and an indented paragraph after a blank line',
    '',
    'A paragraph under the heading is not an item.',
    '- Third criterion after the paragraph',
    '### Deeper heading',
    '- Fourth criterion under a deeper heading',
    '',
    '## Notes',
    '- a note bullet is not an item',
    '',
    'Expected: the inline expected result',
    'right below the label line.',
    '',
    '**Done when**',
    '- Done item one',
    '- [ ] Star task item',
    '',
    'The plain paragraph ends the label section.',
    '- a bullet after the label section',
    '',
    '## Testability',
    '- not under a label heading',
    '',
    '```js',
    '- [ ] a task line in a code block',
    '```',
    '<!--',
    '- [ ] a task line in a comment',
    '-->',
    '## Tests',
    '- Test item',
    '- TEST ITEM!',
  ].join('\r\n');
  assert.deepEqual(texts(issueChecklist(issue)), [
    'Star task item',
    'Plus task item, already checked',
    'Numbered task item',
    'First numbered criterion; with a nested detail',
    'Second numbered criterion continued on the next line and an indented paragraph after a blank line',
    'Third criterion after the paragraph',
    'Fourth criterion under a deeper heading',
    'the inline expected result right below the label line.',
    'Done item one',
    'Test item',
    // The bullets outside the checklist sections: one summary item per heading (two lists under Notes).
    otherList('before its first heading', 1),
    otherList('under "Notes"', 2, 2),
    otherList('under "Testability"', 1),
  ]);
  // A label line needs a colon within 3 words, only marks, or a short bold line: prose that starts with a label is not one.
  assert.deepEqual(texts(issueChecklist('Expected results come from the issue.\n- not an item\n\n**Expected behavior**\n- the lane step goes on\n\n**Done when:** the note shows the wait.\n')),
    ['the lane step goes on', 'the note shows the wait.', otherList('before its first heading', 1)]);
});

test('the reader keeps at most 30 items of at most 300 characters, and the 30th says how many more there are', () => {
  const tasks = n => Array.from({ length: n }, (_, i) => `- [ ] item ${i + 1}`).join('\n');
  const items = issueChecklist(tasks(35));
  assert.equal(items.length, 30);
  assert.deepEqual(items.at(-1), { id: 'C30', text: 'item 30; and 5 more items in the issue; the reviewer checks them' });
  assert.equal(issueChecklist(tasks(31)).at(-1).text, 'item 30; and 1 more item in the issue; the reviewer checks them');
  assert.equal(issueChecklist(tasks(30)).at(-1).text, 'item 30');
  // A long 30th item is cut first, so that the note stays and the whole text has at most 300 characters.
  const tail = '; and 1 more item in the issue; the reviewer checks them';
  const longThirtieth = issueChecklist(`${tasks(29)}\n- [ ] ${'b'.repeat(400)}\n- [ ] item 31`).at(-1).text;
  assert.equal(longThirtieth, `${'b'.repeat(300 - tail.length)}${tail}`);
  const long = issueChecklist(`## Test\n- x${'😀'.repeat(400)}\n- ${'word '.repeat(100)}`);
  assert.equal([...long[0].text].length, 300);
  assert.equal(long[0].text, `x${'😀'.repeat(299)}`);
  assert.equal(long[1].text, 'word '.repeat(60).trimEnd());
});

// Six items; the issue allows leaving the docs pages out.
const SIX = `## Test
- [ ] Alpha: the status line names the lane holder.
- [ ] Beta: the merge note shows the wait time in minutes.
- [ ] Gamma: a second machine never merges the same PR, also when both machines see only their own label.
- [ ] Delta: docs/cli.md describes the lane line.
- [ ] Epsilon: the doctor prints the lane state.
- [ ] Zeta: the alert names the lane holder.

Not in scope: the "docs" pages, they follow in #12.
`;

test('PR lines match by a leading id, by the repeated item text or by their number; the best line wins', () => {
  const items = issueChecklist(SIX);
  assert.equal(items.length, 6);
  const body = [
    'Fixes #7',
    '',
    '## Checklist',
    '1. test/lane.test.mjs "status names the holder"',
    '- Beta: the merge note shows the wait time in minutes. — test/lane.test.mjs "note shows wait"',
    '- Gamma: a second machine never merges the same PR … — test/lane.test.mjs "two machines"',
    '- **[C4]** — excluded: “Not in scope: the "docs" pages”',
    '- [ ] C5: test/doctor.test.mjs (not written yet)',
    '- (C6) pending, see C2',
    '- C6: see C1 for the alert test',
    '  and test/alert.test.mjs "alert names holder"',
    '',
    'Runtime: not run (no Story changed)',
    '4. a numbered list after the section is not part of it',
  ].join('\n');
  const check = checkChecklist(body, items, SIX);
  assert.deepEqual(states(check), ['covered', 'covered', 'covered', 'excluded', 'missing', 'covered']);
  assert.equal(check.items[0].line, '1. test/lane.test.mjs "status names the holder"');
  assert.equal(check.items[3].quote, 'Not in scope: the "docs" pages');
  assert.equal(check.items[4].line, '- [ ] C5: test/doctor.test.mjs (not written yet)');
  assert.equal(check.items[5].line, '- C6: see C1 for the alert test and test/alert.test.mjs "alert names holder"');
  assert.deepEqual(check.counts, { total: 6, covered: 4, excluded: 1, missing: 1, unsupported: 0 });
  assert.equal(check.reds.length, 1);
  assert.match(check.reds[0], /^Checklist item C5 has no evidence line/);
});

test('an id later in a line does not count; one line may name several items; a line with no evidence is missing', () => {
  const items = issueChecklist(SIX);
  const body = 'Checklist:\n- C2: see C1\n- C3, C4 and C5: test/lane.test.mjs\n- C6: TODO\n';
  assert.deepEqual(states(checkChecklist(body, items, SIX)), ['missing', 'covered', 'covered', 'covered', 'covered', 'missing']);
  const numbered = 'Checklist:\n1) test one\n2: test two\n3. none of the old tests break\n4. n/a\n5.\n';
  assert.deepEqual(states(checkChecklist(numbered, items, SIX)), ['covered', 'covered', 'covered', 'missing', 'missing', 'missing']);
});

test('no Checklist: section, or one only in a code block: every item is missing', () => {
  const items = issueChecklist(SIX);
  for (const body of ['Fixes #7\n- C1: test/lane.test.mjs', '```\nChecklist:\n- C1: test/lane.test.mjs\n```', '', null]) {
    const check = checkChecklist(body, items, SIX);
    assert.equal(check.state, 'red');
    assert.equal(check.counts.missing, 6);
    assert.equal(check.reds.length, 6);
    assert.ok(check.items.every(row => row.line === null));
  }
});

test('the build and repair brief lists each item and the Checklist: form', () => {
  const brief = checklistBrief(issueChecklist(LANE_ISSUE));
  assert.match(brief, /^C1\. `pdd autopilot status` names the PR that holds the merge lane\.$/m);
  assert.match(brief, /^C3\. docs\/cli\.md describes the lane line\.$/m);
  assert.match(brief, /^Checklist:\n- C1: EVIDENCE\n- C2: excluded: "QUOTE"$/m);
});

// #3042: readable PR facts modeled on Serhan-Asad/pdd-autopilot-sandbox PRs #6 (formatCents, auto bug PR 1) and #7
// (countWords), and on their code PRs. Each function returns fresh facts, so a test can change one field.
const SUMMARIES_6 = [
  'Problem: `formatCents(1205)` shows "$12.50" instead of "$12.05".\nCase: 1205 | $12.50 | $12.05\nCase: 5 | $0.50 | $0.05\nVerdict: the prompt is right; the bug is only in the CODE.',
  'Title: every price shows dollars and two cent digits\nFile: user_stories/format-price.md — the issue case and the cents rule\nFile: test/runtime/format-price.json — 6 approved cases',
];
export const STORY_6 = `# Format price

As a shop owner, I want every price to show as dollars and two cent digits,
so that customers can read and compare prices.

## Acceptance criteria

1. 1205 cents shows $12.05.
`;
export const AUTO_WORDS = 'Attributed operator action and scope from OWNER-HANDOFF.md:\nThe operator invoked `pdd autopilot start` for `Serhan-Asad/pdd-autopilot-sandbox` in `auto` mode.';
export const fieldsText6 = () => [...SUMMARIES_6];

export function pr1Auto6() {
  return {
    layout: 'spec', workflow: 'bug', number: 1, mode: 'auto', pending: false, draft: false, issueReference: 'Part of #1',
    stories: ['As a shop owner, I want every price to show as dollars and two cent digits, so that customers can read and compare prices.'],
    fields: { problem: '`formatCents(1205)` shows "$12.50" instead of "$12.05".', verdict: 'the prompt is right; the bug is only in the CODE.',
      cases: [{ input: '1205', before: '$12.50', expected: '$12.05' }, { input: '5', before: '$0.50', expected: '$0.05' }],
      notes: { 'user_stories/format-price.md': 'the issue case and the cents rule', 'test/runtime/format-price.json': '6 approved cases' } },
    thisPr: 'no code change. It holds the Story and 1 test file.',
    diff: { added: 27, removed: 1, files: [{ path: 'user_stories/format-price.md', added: 12, removed: 1 }, { path: 'test/runtime/format-price.json', added: 15, removed: 0 }] },
    records: {
      promptTests: { result: '✓ 6 of 6 criteria · 6/6 checks · 6 AI calls', pass: true, report: 'https://interpreter.example/r/a3c9ccd5-365a-4f5e-a673-771c6cf586f1', current: true },
      lint: { result: '1 of 1 tests pass', pass: true }, replay: null, proof: null, review: null, formalStep: false, ci: null, checker: null, drafts: [] },
    approval: { kind: 'auto', mode: 'auto', login: 'Serhan-Asad', date: '2026-11-06', person: false },
    pr1: null, pr2: null, stacked: false, carriesPr1: false,
  };
}
export function pr1Manual7() {
  return { ...pr1Auto6(), number: 3, mode: 'manual',
    stories: ['As a writer, I want the word count to count only words, so that my count matches the text.'],
    fields: { problem: '`countWords("one two")` returns 3 instead of 2.', verdict: 'the prompt is right; the bug is only in the CODE.',
      cases: [{ input: '"one two"', before: '3', expected: '2' }, { input: '"  one  "', before: '3', expected: '1' }], notes: {} },
    thisPr: 'no code change. It holds the Story and 1 test file.',
    diff: { added: 30, removed: 0, files: [{ path: 'user_stories/count-words.md', added: 14, removed: 0 }, { path: 'test/runtime/count-words.json', added: 16, removed: 0 }] },
    records: { ...pr1Auto6().records, promptTests: { result: '✓ 5 of 5 criteria · 5/5 checks · 0 AI calls', pass: true, report: 'https://interpreter.example/r/dd8c6dd2-d09c-4cd3-ace9-a97d90d230da', current: true } },
    approval: { kind: 'words', items: [{ route: 'said', at: Date.parse('2026-11-06T17:53:57Z'), words: 'Yes, the Story is right.\nOpen the PR.' }, { route: 'terminal', at: Date.parse('2026-11-06T18:10:00Z'), words: null }] },
    issueReference: 'Part of #3' };
}
const replayPass = () => ({ outcome: 'pass', reason: 'All current assertions have source-bound public-boundary replay evidence.',
  counts: { total: 6, pass: 6, fail: 0, blocked: 0, not_replayed: 0 }, mutation: { outcome: 'assertion_failure', failures: 1, description: 'padEnd instead of padStart' },
  formal: { result: 'proved_bounded', scope: 'all 0–100,000 cents', reason: 'Exhaustive bounded check.', control_outcome: 'assertion_failure' } });
export function pr2Fix6() {
  return { ...pr1Auto6(), layout: 'code', issueReference: 'Closes #1',
    fields: { problem: '`formatCents(1205)` shows "$12.50" instead of "$12.05".', cause: 'the cents are padded on the right (`padEnd`) instead of the left.',
      fix: 'pad on the left (`padStart`). One line in `src/money.js`.', result: 'all 6 approved cases pass on the real code.',
      cases: [{ input: '1205', before: '$12.50', after: '$12.05', expected: '$12.05' }],
      notes: { 'src/money.js': '`padEnd` → `padStart` (the fix).', 'test/money.test.js': 'regression test for 1205.' } },
    diff: { added: 9, removed: 1, files: [{ path: 'src/money.js', added: 1, removed: 1 }, { path: 'test/money.test.js', added: 6, removed: 0 }, { path: 'test/format-price.vectors.test.js', added: 2, removed: 0 }] },
    records: { promptTests: null, lint: null, replay: replayPass(), proof: { status: 'proved', passed: 12, total: 12 }, review: { mustFix: 0 }, formalStep: true,
      ci: null, checker: null, drafts: [] },
    pr1: { number: 6, url: 'https://github.com/Serhan-Asad/pdd-autopilot-sandbox/pull/6', merged: false, state: 'open', ci: 'passing' }, stacked: true, carriesPr1: false };
}
export function pr2Blocked6() {
  const facts = pr2Fix6();
  facts.records.replay = { ...replayPass(), outcome: 'fail', counts: { total: 6, pass: 5, fail: 1, blocked: 0, not_replayed: 0 },
    formal: { result: 'failed', scope: 'all 0–100,000 cents', reason: 'Counterexample found.', control_outcome: 'assertion_failure' }, counterexample: '{"cents":1205}' };
  facts.records.review = { mustFix: 1 }; facts.records.ci = 'passing'; facts.records.checker = { verdict: 'FAIL' };
  return facts;
}
export function featurePr2() {
  const facts = pr2Fix6();
  return { ...facts, workflow: 'feature', number: 9, issueReference: 'Closes #9',
    stories: ['As a reader, I want to filter books by author, so that I find their books fast.'],
    fields: { problem: 'There is no way to list the books of one author.', fix: 'add `filterByAuthor` to the shelf module.', result: 'all 4 approved cases pass.',
      cases: [{ input: '"Le Guin"', after: '2 books', expected: '2 books' }], notes: {} },
    records: { ...facts.records, replay: { ...replayPass(), counts: { total: 4, pass: 4, fail: 0, blocked: 0, not_replayed: 0 }, mutation: { outcome: 'assertion_failure', failures: 3, description: 'filter ignores the author' },
      formal: { result: 'not_applicable', scope: 'shelf filter', reason: 'no numeric rule to prove', control_outcome: 'not_run' } }, proof: { status: 'proved', passed: 4, total: 4 }, ci: 'passing', checker: { verdict: 'PASS' } },
    pr1: { number: 8, url: 'https://github.com/example/shelf/pull/8', merged: true, state: 'merged', ci: 'passing' }, stacked: false };
}
export function smallChange() {
  return { ...pr2Fix6(), single: true, workflow: 'small-change', number: 12, mode: 'manual', issueReference: 'Closes #12',
    stories: [], storyNote: 'this run changes no Story file',
    fields: { problem: 'The help text says "recieve".', change: 'fix the spelling in `src/help.js`.', result: 'the help text says "receive".', cases: [], notes: {} },
    diff: { added: 1, removed: 1, files: [{ path: 'src/help.js', added: 1, removed: 1 }] },
    records: { promptTests: null, lint: null, replay: null, proof: { status: 'proved', passed: 3, total: 3 }, review: null, formalStep: true, formalDone: true, ci: 'pending', checker: null, drafts: [] },
    approval: { kind: 'words', items: [{ route: 'said', at: Date.parse('2026-11-06T12:00:00Z'), words: 'ok, fix the typo' }] }, pr1: null, stacked: false };
}

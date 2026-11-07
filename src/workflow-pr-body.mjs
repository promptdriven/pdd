// Generated from prompts/cli/workflow-pr-body.prompt.md (sha256: a946668f89b4a595071b66597a9c8298a3ff86bc6ccb270c53e8bcbf7773a7c8).
// The readable part of a pdd workflow PR (#3042): a status line, the user story, a short summary, a cases table, what
// changed, a proof table from pdd's own records and one approval/next/merge line. The runner gathers the facts; this
// module only renders them. Agent words appear only in the summary and the cases table, always as inert text.

export const DETAILS_OPEN = '<details><summary>Details for tools and audits</summary>';
const MAX_FIELD = 300, MAX_CELL = 120, MAX_CASES = 12, MAX_FILES = 40, MAX_NOTE = 160, MAX_STORIES = 3, MAX_WORDS = 3;
const LABELS = { Title: 'title', Area: 'area', Problem: 'problem', Cause: 'cause', Fix: 'fix', Change: 'change', Result: 'result', 'This PR': 'thisPr', Verdict: 'verdict' };
const FIELD_LINE = /^(?:[-*]\s+)?(Title|Area|Problem|Cause|Fix|Change|Result|This PR|Verdict|Case|File):\s*(.*\S)\s*$/;

const characters = text => [...text].length;
const oneLine = value => String(value ?? '').replace(/[\u0000-\u001f\u007f-\u009f\u2028\u2029]+/g, ' ').replace(/\s+/g, ' ').trim();
function clip(text, max) {
  const points = [...text];
  if (points.length <= max) return text;
  const cut = points.slice(0, max - 2).join(''), word = cut.replace(/\s+\S*$/, '');
  return `${(word.length >= cut.length / 2 ? word : cut).trimEnd()} …`;
}
// A closing keyword followed by an issue reference would close that issue on merge; a zero-width space keeps it text.
const CLOSING = /\b(fix(?:es|ed)?|close[sd]?|resolve[sd]?)(?=\s+(?:[\w.-]+\/[\w.-]+)?#\d|\s+https:\/\/github\.com\/)/gi;
const MARKERS = text => text.replaceAll('pdd-workflow:', 'pdd-workflow\\u003a').replaceAll('pdd-product:', 'pdd-product\\u003a');
// Agent words as one inert Markdown line: no HTML, no ownership marker, no mention, no closing keyword.
// Code spans stay code (their text is already inert); only the text outside them is escaped.
export function inertText(value, max = MAX_FIELD) {
  const flat = String(value ?? '').replace(/[\u0000-\u001f\u007f-\u009f\u2028\u2029]+/g, ' ').replace(/[\u061c\u200e\u200f\u202a-\u202e\u2066-\u2069]/g, '');
  const parts = [];
  let at = 0;
  // Code spans keep their spaces (a case input such as `"  one  "` must stay exact); other text collapses its spaces.
  for (const match of flat.matchAll(/(?<!`)(`+)(?!`)(.+?)(?<!`)\1(?!`)/g)) {
    parts.push({ code: false, text: flat.slice(at, match.index).replace(/\s+/g, ' ') }, { code: true, text: match[0] });
    at = match.index + match[0].length;
  }
  parts.push({ code: false, text: flat.slice(at).replace(/\s+/g, ' ') });
  const text = clip(parts.map(part => part.text).join('').trim(), max);
  // A cut can end inside a code span; escaping then treats its rest as text, which stays inert.
  const shown = [];
  at = 0;
  for (const match of text.matchAll(/(?<!`)(`+)(?!`)(.+?)(?<!`)\1(?!`)/g)) {
    shown.push(escapeHtml(text.slice(at, match.index)), MARKERS(match[0]));
    at = match.index + match[0].length;
  }
  shown.push(escapeHtml(text.slice(at)));
  return shown.join('').replace(/@(?=[A-Za-z0-9])/g, '@\u200b').replace(CLOSING, '$1\u200b');
}
const escapeHtml = text => text.replace(/</g, '&lt;').replace(/>/g, '&gt;').replaceAll('pdd-workflow:', 'pdd-workflow&#58;').replaceAll('pdd-product:', 'pdd-product&#58;');
const cell = (value, max = MAX_CELL) => {
  const text = inertText(value, max);
  return text ? text.replace(/\|/g, '\\|') : '—';
};
export function codeSpan(value) {
  const text = MARKERS(oneLine(value));
  const fence = '`'.repeat([...text.matchAll(/`+/g)].reduce((most, run) => Math.max(most, run[0].length), 0) + 1);
  const padding = /^`|`$/.test(text) ? ' ' : '';
  return `${fence}${padding}${text}${padding}${fence}`;
}

// The PR fields that agents write as labeled lines in their `done` summaries. A later text replaces an earlier one per
// field; the Case rows of the latest text that has any replace all earlier rows; a File note replaces an earlier one.
export function readPrFields(texts) {
  const fields = { cases: [], notes: {} };
  for (const text of texts ?? []) {
    let cases = null;
    for (const raw of String(text ?? '').split(/\r?\n/)) {
      const match = FIELD_LINE.exec(raw.trim());
      if (!match) continue;
      const [, label, value] = match;
      if (label === 'Case') {
        const cells = value.split('|').map(item => item.trim());
        if (cells.length >= 2 && cells.length <= 4 && cells[0]) (cases ??= []).push(cells.length === 2 ? { input: cells[0], expected: cells[1] }
          : cells.length === 3 ? { input: cells[0], before: cells[1], expected: cells[2] } : { input: cells[0], before: cells[1], after: cells[2], expected: cells[3] });
      } else if (label === 'File') {
        const file = /^`?([^`\s]+?)`?\s*(?:—|–|-|:)\s+(\S.*)$/.exec(value);
        if (file) fields.notes[file[1]] = file[2];
      } else fields[LABELS[label]] = value;
    }
    if (cases) fields.cases = cases.slice(0, MAX_CASES);
  }
  return fields;
}

// The "As a …, I want …, so that …" line of a Story file (it may wrap over several lines), or null.
export function userStory(text) {
  const lines = String(text ?? '').split(/\r?\n/);
  for (let index = 0; index < lines.length; index++) {
    const start = lines[index].replace(/^\s*(?:>\s*)?(?:[-*]\s+)?/, '');
    if (!/^(?:\*\*|__|_|\*)?As an?\s/i.test(start)) continue;
    const parts = [start];
    for (let next = index + 1; next < lines.length && lines[next].trim() && !/^\s*(?:#|[-*+]\s|\d+[.)]\s|```|~~~|<|\|)/.test(lines[next]); next++)
      parts.push(lines[next].replace(/^\s*>\s?/, ''));
    const story = oneLine(parts.join(' ')).replace(/\*\*|__/g, '').replace(/^[_*]|[_*]$/g, '');
    if (/^As an?\s.+,\s*I want\s.+,?\s*so that\s.+/i.test(story)) return story;
  }
  return null;
}

// The area in a title: the agent's `Area:` field, else the owning prompt, the Story, the first code file or the workflow.
export function prArea({ area, files = [], workflow } = {}) {
  const clean = value => String(value ?? '').toLowerCase().replace(/[^a-z0-9._-]+/g, '-').replace(/^[-._]+|[-._]+$/g, '').slice(0, 40).replace(/[-._]+$/, '');
  const name = path => path.split('/').at(-1);
  if (clean(area)) return clean(area);
  const prompt = files.find(path => path.endsWith('.prompt.md'));
  if (prompt) return clean(name(prompt).replace(/\.prompt\.md$/, '').replace(/_(?:python|typescript|javascript|js|ts|go|rust|java)$/, '')) || 'pdd';
  const story = files.find(path => /(?:^|\/)user_stories\/[^/]+\.md$/.test(path) && !/^(?:plan|readme)\.md$/i.test(name(path)));
  if (story) return clean(name(story).replace(/\.md$/, '')) || 'pdd';
  const owned = path => !/(?:^|\/)(?:tests?|__tests__|fixtures|docs?|user_stories|prompts)\//.test(path) && !/\.(?:test|spec)\./i.test(path);
  const code = files.find(path => owned(path) && /\.(?:[cm]?js|jsx|tsx?|py|go|rs|java|kt|rb|php|cs|swift|c|cc|cpp|h|hpp|sh|vue|svelte)$/i.test(path))
    ?? files.find(path => owned(path) && /\.[a-z0-9]+$/i.test(path) && !/\.(?:md|json|lock|txt)$/i.test(path));
  if (code) return clean(name(code).replace(/\.[^.]+$/, '')) || 'pdd';
  return clean(workflow) || 'pdd';
}

// `spec(area): … (#N · part 1: spec)`, `fix(area): … (#N · part 2: fix)`, `feat(area): … (#N · part 2: feat)`, and
// `fix(area): … (#N)` for a one-PR run (part null). GitHub refuses a title over 256 UTF-16 code units: the statement is
// cut at a character boundary and shows " …"; the type, area and suffix always stay.
export function readablePrTitle({ layout, workflow, area, statement, number, part = layout === 'spec' ? 1 : null }) {
  const type = layout === 'spec' ? 'spec' : workflow === 'feature' ? 'feat' : 'fix';
  const prefix = `${type}(${area || 'pdd'}): `;
  const suffix = part ? ` (#${number} · part ${part}: ${type})` : ` (#${number})`;
  const text = oneLine(statement) || `issue #${number}`;
  if ((prefix + text + suffix).length <= 256) return prefix + text + suffix;
  let kept = '';
  for (const point of text) { if (prefix.length + kept.length + point.length + 2 + suffix.length > 256) break; kept += point; }
  return `${prefix}${kept.trimEnd()} …${suffix}`;
}

const plural = (count, word, many = `${word}s`) => `${count} ${count === 1 ? word : many}`;
const listed = items => items.length > 1 ? `${items.slice(0, -1).join(', ')} and ${items.at(-1)}` : items[0] ?? '';
const date = at => Number.isFinite(at) ? new Date(at).toISOString().slice(0, 10) : '';
const FORMAL = { proved_bounded: 'Proved (bounded)', proved_solver: 'Proved (solver)' };
const PROOF_PROBLEM = { 'old-passes': 'the changed tests also pass on the old code', 'wrong-reason': 'the changed tests fail on the old code for another reason',
  'head-fails': 'the changed tests fail on the new code', 'setup-error': 'the old-code proof had a setup error', signalled: 'the old-code proof was stopped',
  'base-timeout': 'the old-code proof timed out on the old code', 'head-timeout': 'the old-code proof timed out on the new code', 'output-limit': 'the old-code proof output was too long' };

// The rows and the status of a PR, from pdd's own records only: saved pdd test/lint results, replay evidence, the
// old-code proof, review.md, CI and the checker verdict. Agent words never fill a row.
function proofRows(facts) {
  const r = facts.records ?? {}, rows = [], blocked = [], waiting = [];
  const manual = facts.mode === 'manual', code = facts.layout === 'code';
  if (facts.pending) waiting.push('publication');
  if (!code) {
    const tests = r.promptTests;
    rows.push(['Prompt tests (`pdd test`)', tests ? `${inertText(tests.result, 200)}${tests.report ? ` · [report](${tests.report}) (expires after 7 days)` : ''}${tests.current === false ? ' (older source)' : ''}` : 'no pdd result (`pdd:no-verdict`)']);
    if (tests?.pass === false) blocked.push('prompt tests fail');
    rows.push(['Lint (`pdd lint`)', r.lint ? `${r.lint.pass === true ? '✓ ' : r.lint.pass === false ? '✗ ' : ''}${inertText(r.lint.result, 120)}` : 'not run']);
    if (r.lint?.pass === false) blocked.push('lint fails');
    if (r.drafts?.length) {
      rows.push(['Prompts approved', `✗ ${plural(r.drafts.length, 'draft prompt')}: ${r.drafts.slice(0, 5).map(codeSpan).join(', ')}`]);
      blocked.push(`${plural(r.drafts.length, 'draft prompt')} to approve`);
    }
  } else {
    const replay = r.replay;
    if (replay) {
      const counts = replay.counts ?? {}, total = counts.total ?? 0, complete = ['pass', 'fail'].includes(replay.outcome) && total > 0;
      const mutation = replay.mutation;
      const old = !complete || !mutation ? '—' : mutation.outcome === 'assertion_failure' && mutation.failures > 0 ? `✗ ${mutation.failures} fail${mutation.failures === 1 ? 's' : ''} (as expected)` : `no failure caught (${inertText(mutation.outcome, 40)})`;
      rows.push(['Approved cases on real code (vectors)', !complete ? `${replay.outcome === 'not_replayed' ? 'not replayed' : 'blocked'}: ${inertText(replay.reason, 160)}` : counts.fail ? `✗ ${counts.fail} of ${total} fail` : `✓ ${counts.pass} of ${total}`, old]);
      if (!complete) blocked.push(`replay evidence is ${replay.outcome === 'not_replayed' ? 'incomplete' : 'blocked'}`);
      else if (counts.fail) blocked.push(`${plural(counts.fail, 'approved case')} fail${counts.fail === 1 ? 's' : ''} on the new code`);
      else if (!(mutation?.outcome === 'assertion_failure' && mutation.failures > 0)) blocked.push(`the ${facts.workflow === 'feature' ? 'planted mistake' : 'old code'} fails no case`);
    }
    if (replay?.formal) {
      const formal = replay.formal, scope = inertText(formal.scope, 80);
      const result = FORMAL[formal.result] ?? (formal.result === 'failed' ? `Failed at ${replay.counterexample ? codeSpan(clip(oneLine(replay.counterexample), 80)) : 'the counterexample in Details'}`
        : formal.result === 'not_applicable' ? `Not applicable: ${inertText(formal.reason, 120)}` : `Not run: ${inertText(formal.reason, 120)}`);
      const control = formal.control_outcome === 'assertion_failure' ? '✗ fails (as expected)' : formal.control_outcome === 'not_run' ? '—' : inertText(formal.control_outcome, 40);
      rows.push([`Formal check${scope ? ` (${scope})` : ''}`, result, control]);
      if (formal.result === 'failed') blocked.push(`formal check failed${replay.counterexample ? ` at ${codeSpan(clip(oneLine(replay.counterexample), 80))}` : ''}`);
    } else if (r.formalStep) rows.push(['Formal check', `Not recorded: ${replay ? 'the replay evidence has no formal result' : 'pdd has no formal result for this run'} (see Details)`, '—']);
    const proof = r.proof;
    if (proof) {
      const counted = Number.isSafeInteger(proof.total) ? ` (${proof.passed} of ${proof.total} tests)` : '';
      const cells = { proved: [`✓ pass${counted}`, '✗ fail (as expected)'], 'old-passes': [`✓ pass${counted}`, '✓ pass (should fail)'], 'wrong-reason': [`✓ pass${counted}`, '✗ fails for another reason'],
        'head-fails': ['✗ fail', '—'], 'no-changed-tests': ['no changed tests', '—'], 'not-run': ['not run', '—'], stale: ['⏳ stale (rerun `pdd workflow prove`)', '—'],
        unavailable: ['unavailable', '—'], pending: ['⏳ pending', '—'] }[proof.status] ?? [`✗ ${inertText(proof.status, 40)}`, '—'];
      rows.push(['Regression tests (old-code proof)', ...cells]);
      if (PROOF_PROBLEM[proof.status]) blocked.push(PROOF_PROBLEM[proof.status]);
    }
  }
  const ci = r.ci === 'passing' ? '✓ green' : r.ci === 'failing' ? '✗ failing' : '⏳ pending';
  rows.push([code ? 'Full test suite (CI) on this commit' : 'Full test suite (CI)', ci, ...(code ? ['—'] : [])]);
  if (r.ci === 'failing') blocked.push('CI fails');
  else if (r.ci !== 'passing') waiting.push('CI');
  if (code && r.review !== null && r.review !== undefined) {
    const review = r.review === 'missing' ? 'not recorded' : r.review.mustFix ? `✗ ${r.review.mustFix} must-fix` : 'no must-fix';
    rows.push(['Fresh review', review, '—']);
    if (r.review !== 'missing' && r.review.mustFix) blocked.push(`review has ${r.review.mustFix} must-fix`);
  }
  const verdict = r.checker?.verdict;
  rows.push(['Independent checker', verdict === 'PASS' ? '✓ PASS' : verdict === 'FAIL' ? '✗ FAIL' : verdict === 'NOT SURE' ? 'NOT SURE' : manual ? '— (a person reviews)' : '⏳ pending', ...(code ? ['—'] : [])]);
  if (verdict === 'FAIL') blocked.push('the checker says FAIL');
  else if (verdict === 'NOT SURE') blocked.push('the checker is not sure');
  else if (!verdict && !manual) waiting.push('the checker');
  if (code && facts.stacked && facts.pr1 && !facts.pr1.merged && !facts.carriesPr1) waiting.push(`PR 1 (#${facts.pr1.number})`);
  return { rows, blocked, waiting };
}
export function prStatus(facts) {
  const { blocked, waiting } = proofRows(facts);
  if (blocked.length) return `⛔ Blocked: ${blocked.join('; ')}`;
  if (waiting.length) return `⏳ Waiting for ${listed(waiting.includes('publication') ? ['the source to be published'] : waiting)}`;
  return '✅ Ready to merge';
}

function table(header, rows) {
  return [`| ${header.join(' | ')} |`, `|${header.map(() => '---').join('|')}|`, ...rows.map(row => `| ${row.join(' | ')} |`)];
}
function casesTable(facts) {
  const cases = facts.fields?.cases ?? [];
  if (!cases.length) return [];
  const before = cases.some(row => row.before !== undefined);
  if (facts.layout === 'spec') return ['## Expected behavior', '', ...table(['Input', ...(before ? ['Today'] : []), 'Expected'],
    cases.map(row => [cell(row.input), ...(before ? [cell(row.before)] : []), cell(row.expected)])), ''];
  return ['## Before / after', '', ...table(['Input', ...(before ? ['Before'] : []), 'After', 'Expected'], cases.map(row => {
    const mark = row.after === undefined || row.expected === undefined ? '' : oneLine(row.after) === oneLine(row.expected) ? ' ✓' : ' ✗';
    return [cell(row.input), ...(before ? [cell(row.before)] : []), cell(row.after), `${cell(row.expected)}${mark}`];
  })), ''];
}
function changes(facts, fileLimit) {
  const diff = facts.diff;
  if (!diff) return [];
  const files = diff.files ?? [], notes = facts.fields?.notes ?? {};
  const rows = files.slice(0, fileLimit).map(file => `- ${codeSpan(file.path)}${notes[file.path] ? `: ${inertText(notes[file.path], MAX_NOTE)}` : file.binary ? ' (binary)' : ` (+${file.added} −${file.removed})`}`);
  if (files.length > fileLimit) rows.push(`- …and ${plural(files.length - fileLimit, 'more file')} (see the Files tab).`);
  return [`## What changed (+${diff.added} −${diff.removed}, ${plural(files.length, 'file')})`, '', ...rows, ''];
}
function summary(facts) {
  const f = facts.fields ?? {}, bullet = (label, value) => value ? [`- **${label}:** ${inertText(value)}`] : [];
  const rows = facts.layout === 'spec' ? [...bullet('Problem', f.problem), ...bullet('This PR', f.thisPr || facts.thisPr), ...bullet('Verdict', f.verdict)]
    : facts.single ? [...bullet('Problem', f.problem), ...bullet('Change', f.change || f.fix), ...bullet('Result', f.result)]
    : [...bullet('Problem', f.problem), ...bullet('Cause', f.cause), ...bullet('Fix', f.fix), ...bullet('Result', f.result)];
  return rows.length ? ['## Summary', '', ...rows, ''] : [];
}
function approvalLine(facts) {
  const approval = facts.approval;
  if (!approval) return '**Approval:** none recorded yet.';
  if (approval.kind === 'auto') {
    const by = approval.login ? ` by ${inertText(approval.login, 40)}` : '', on = approval.date ? ` on ${approval.date}` : '';
    return `**Approval:** Automatic approval: Autopilot \`${approval.mode === 'observe' ? 'observe' : 'auto'}\` mode, started${by}${on}. ${approval.person ? 'A person also approved in the terminal.' : 'No person was asked.'}`;
  }
  const where = { said: 'in chat', chat: 'in the area chat', terminal: 'in the terminal' };
  const items = approval.items ?? [], shown = items.slice(-MAX_WORDS);
  const words = shown.map(item => `${item.words ? codeSpan(clip(oneLine(item.words), 200)) : 'approved'} (${where[item.route] ?? 'recorded'}${date(item.at) ? `, ${date(item.at)}` : ''})`);
  return `**Approval:** ${words.join('; ') || 'none recorded yet'}${items.length > shown.length ? ` (${items.length - shown.length} earlier in Details)` : ''}.`;
}
// The Next line (PR 1) or the Merge line and its PR 1 line (code PR). The runner also uses PR 1's Next line alone when
// PR 2 opens, so PR 1 links it without changing anything else.
export function readableNextLines(facts) {
  const reference = facts.issueReference, automatic = facts.mode !== 'manual';
  if (facts.layout === 'spec') {
    if (facts.pr2) return [`**Next:** PR 2 (the code)${automatic ? ' started by itself' : ''}: #${facts.pr2.number}. ${reference}.`];
    return [automatic ? `**Next:** PR 2 (the code) starts by itself (Autopilot \`${facts.mode}\` mode). ${reference}.` : `**Next:** The code PR starts when you ask for it. ${reference}.`];
  }
  const merge = facts.mode === 'auto' && !facts.draft ? 'automatic when every check above is green (Autopilot `auto` mode)' : `waiting for a person to merge${facts.draft ? ' (draft PR)' : ''}`;
  const pr1 = facts.pr1 && !facts.pr1.merged ? facts.carriesPr1 ? [`This PR also merges PR 1 (#${facts.pr1.number}).`]
    : facts.stacked ? [`Builds on PR 1 (#${facts.pr1.number}): merge it first.`] : [] : [];
  return [`**Merge:** ${merge}. ${reference}.`, ...pr1.flatMap(line => ['', line])];
}

// The readable part as Markdown, plus the notes that the runner puts into Details. It never holds IDs, batches,
// request IDs, step notes or approval records; those stay in Details.
export function readablePrTop(facts, { fileLimit = MAX_FILES } = {}) {
  const notes = [];
  const stories = (facts.stories ?? []).slice(0, MAX_STORIES);
  if (!stories.length) notes.push(`User story: ${facts.storyNote ?? 'no Story file of this run has an "As a …, I want …, so that …" line'}, so this PR has no User story section.`);
  if ((facts.stories ?? []).length > MAX_STORIES) notes.push(`User story: ${facts.stories.length - MAX_STORIES} more Stories are not shown above.`);
  const { rows } = proofRows(facts);
  const header = facts.layout === 'spec' ? ['Check', 'Result'] : ['Check', 'New code', facts.workflow === 'feature' ? 'Planted mistake' : 'Old code'];
  const lines = [prStatus(facts), '',
    ...(stories.length ? ['## User story', '', ...stories.flatMap((story, index) => [...(index ? [''] : []), inertText(story, 600)]), ''] : []),
    ...summary(facts), ...casesTable(facts), ...changes(facts, fileLimit),
    `## ${facts.layout === 'spec' ? 'Checks' : 'Proof'}`, '', ...table(header, rows), '',
    ...(facts.layout === 'spec' ? [approvalLine(facts), ''] : []), ...readableNextLines(facts)];
  return { text: lines.join('\n'), notes };
}

// The whole description: the readable part, then one closed Details section with everything pdd recorded.
export function readablePrBody(top, details) {
  return `${top.trimEnd()}\n\n${DETAILS_OPEN}\n\n${String(details).trim()}\n\n</details>\n`;
}
// The pdd-written part inside the Details section of a readable description, and any text a person added after it;
// null for a description without that section (an older pdd wrote it, so all of it is pdd body).
export function detailsOf(body) {
  const rows = String(body ?? '').split('\n'), open = rows.findIndex(row => /^<details\b/i.test(row));
  if (open < 0 || rows[open] !== DETAILS_OPEN) return null;
  let close = rows.length - 1;
  while (close > open && rows[close] !== '</details>') close--;
  return close > open ? { details: rows.slice(open + 1, close).join('\n').trim(), after: rows.slice(close + 1).join('\n').trim() } : null;
}

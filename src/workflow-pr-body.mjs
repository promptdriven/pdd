// Generated from prompts/cli/workflow-pr-body.prompt.md (sha256: e3586639832d461faf237f7ccdef5b01a177deb9e322337e88dbabffc1883a41).
// The readable part of a pdd workflow PR (#3042): a status line, the user story, a short summary, a cases table, what
// changed, a proof table from pdd's own records and one approval/next/merge line. The runner gathers the facts; this
// module only renders them. Agent words appear only in the title, the summary and the cases table, always as inert text.

import { formalStatusText } from './workflow-replay.mjs';

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
// GitHub closes an issue on merge for a closing keyword (close, closes, closed, fix, fixes, fixed, resolve, resolves,
// resolved; any case) before an issue reference, also with a colon ("Fixes: #5", "Closes:#5") or marks between. Outside
// code spans every such word gets one zero-width space after it, whatever follows, so it stays text. A code span stays
// exact: GitHub reads no reference and no mention in code. A backtick after a backslash opens no code span.
const KEYWORD = /\b(fix(?:es|ed)?|close[sd]?|resolve[sd]?)\b(?!\u200b)/gi;
const CODE_SPAN = /(?<![`\\])(`+)(?!`)(.+?)(?<!`)\1(?!`)/g;
const inertWords = text => text.replace(KEYWORD, '$1\u200b').replace(/@(?=[A-Za-z0-9])/g, '@\u200b');
// Agent words show no image and no link of their own: an image or a link keeps only its text, and a bare address gets a
// zero-width space so that GitHub does not link it. The readable part then has one report link, pdd's.
function plainLinks(text) {
  let out = text;
  for (let round = 0; round < 4; round++) { const next = out.replace(/!?\[([^\[\]\n]*)\]\([^()\n]*\)/g, '$1'); if (next === out) break; out = next; }
  return out.replace(/\b(https?|ftp):\/\//gi, '$1:\u200b//').replace(/\bwww\./gi, 'www\u200b.');
}
const MARKERS = text => text.replaceAll('pdd-workflow:', 'pdd-workflow\\u003a').replaceAll('pdd-product:', 'pdd-product\\u003a');
// Agent words as one inert Markdown line: no HTML, no ownership marker, no mention, no closing keyword.
// Code spans stay code (their text is already inert); only the text outside them is escaped.
export function inertText(value, max = MAX_FIELD) {
  const flat = String(value ?? '').replace(/[\u0000-\u001f\u007f-\u009f\u2028\u2029]+/g, ' ').replace(/[\u061c\u200e\u200f\u202a-\u202e\u2066-\u2069]/g, '');
  const parts = [];
  let at = 0;
  // Code spans keep their spaces (a case input such as `"  one  "` must stay exact); other text collapses its spaces.
  for (const match of flat.matchAll(CODE_SPAN)) {
    parts.push({ code: false, text: plainLinks(flat.slice(at, match.index).replace(/\s+/g, ' ')) }, { code: true, text: match[0] });
    at = match.index + match[0].length;
  }
  parts.push({ code: false, text: plainLinks(flat.slice(at).replace(/\s+/g, ' ')) });
  const text = clip(parts.map(part => part.text).join('').trim(), max);
  // A cut can end inside a code span; escaping then treats its rest as text, which stays inert.
  const shown = [];
  at = 0;
  const outside = part => inertWords(escapeHtml(part));
  for (const match of text.matchAll(CODE_SPAN)) {
    shown.push(outside(text.slice(at, match.index)), MARKERS(match[0]));
    at = match.index + match[0].length;
  }
  shown.push(outside(text.slice(at)));
  return shown.join('');
}
const escapeHtml = text => text.replace(/</g, '&lt;').replace(/>/g, '&gt;').replaceAll('pdd-workflow:', 'pdd-workflow&#58;').replaceAll('pdd-product:', 'pdd-product&#58;');
// A table cell: each pipe is escaped, and so is each backslash right before it. GitHub reads `\\` as one escaped
// backslash, so a text `\|` written as `\\|` would end the cell. Other backslashes keep their text, also in code spans.
const cell = (value, max = MAX_CELL) => {
  const text = inertText(value, max);
  return text ? text.replace(/(\\*)\|/g, (_, slashes) => `${slashes}${slashes}\\|`) : '—';
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
        const cells = caseCells(value);
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

// The cells of a Case line: split on `|` outside code spans (a `|` inside one stays in its cell); a cell loses a trailing
// backslash, so "INPUT \\| TODAY \\| EXPECTED" copied from a Markdown table still gives three cells.
function caseCells(value) {
  const cells = [''];
  const add = text => { const parts = text.split('|'); cells[cells.length - 1] += parts[0]; cells.push(...parts.slice(1)); };
  let at = 0;
  for (const match of value.matchAll(CODE_SPAN)) { add(value.slice(at, match.index)); cells[cells.length - 1] += match[0]; at = match.index + match[0].length; }
  add(value.slice(at));
  return cells.map(item => item.trim().replace(/\s*\\$/, ''));
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
// cut at a character boundary and shows " …"; the type, area and suffix always stay. The statement follows the keyword
// and mention rule of the readable part everywhere, also between backticks: GitHub puts the title into the merge commit,
// and a commit message has no code spans.
export function readablePrTitle({ layout, workflow, area, statement, number, part = layout === 'spec' ? 1 : null }) {
  const type = layout === 'spec' ? 'spec' : workflow === 'feature' ? 'feat' : 'fix';
  const prefix = `${type}(${area || 'pdd'}): `;
  const suffix = part ? ` (#${number} · part ${part}: ${type})` : ` (#${number})`;
  const text = inertWords(oneLine(statement)) || `issue #${number}`;
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
  'base-timeout': 'the old-code proof timed out on the old code', 'head-timeout': 'the old-code proof timed out on the new code', 'output-limit': 'the old-code proof output was too long',
  unavailable: 'the old-code proof is unavailable' };

// PR 1's place in a code PR's merge order (#3042, the red pair of RUNBOOK §2), or null when there is no open PR 1 below it:
// 'carried' when GitHub shows the run's base as this PR's base, or PR 1's CI fails (PR 1 never merges alone); 'first' when
// PR 1's CI passes or has no checks; 'ci' while PR 1's CI is pending or unknown; 'closed' for a PR 1 closed without a merge.
export function pr1Order(facts) {
  const pr1 = facts?.pr1;
  if (facts?.layout !== 'code' || !pr1 || pr1.merged || !facts.stacked) return null;
  if (pr1.state === 'closed') return 'closed';
  if (facts.carriesPr1 || pr1.ci === 'failing') return 'carried';
  return ['passing', 'none'].includes(pr1.ci) ? 'first' : 'ci';
}

// The rows and the status of a PR, from pdd's own records only: saved pdd test/lint results, replay evidence, the
// old-code proof, review.md, CI and the checker verdict. Agent words never fill a row. A record that a PR needs and that
// is missing, stale or not finished keeps the status from ✅: it waits for it, or it is blocked with the reason.
function proofRows(facts) {
  const r = facts.records ?? {}, rows = [], blocked = [], waiting = [];
  const small = facts.workflow === 'small-change' && facts.single === true && facts.layout === 'code';
  if (small) {
    const checklist = r.checklist;
    rows.push(['Issue checklist', checklist?.status === 'recorded' ? `${checklist.items.length} items; ${checklist.mustFix.length} must-fix` : checklist?.status ?? 'missing', '—']);
    if (!checklist || checklist.status === 'missing') waiting.push('the issue checklist');
    else if (checklist.status !== 'recorded' || checklist.mustFix.length) blocked.push('issue checklist has must-fix items');
  }
  const manual = facts.mode === 'manual', code = facts.layout === 'code', pair = code && !facts.single;
  if (facts.pending) waiting.push('publication');
  // GitHub shows a head that pdd did not publish: every record below is for the older head.
  if (facts.headChanged) waiting.push('pdd records for the new head');
  if (!code) {
    const tests = r.promptTests;
    rows.push(['Prompt tests (`pdd test`)', tests ? `${inertText(tests.result, 200)}${tests.report ? ` · [report](${tests.report}) (expires after 7 days)` : ''}${tests.current === false ? ' (older source)' : ''}` : 'no pdd result (`pdd:no-verdict`)']);
    if (tests?.pass === false) blocked.push('prompt tests fail');
    else if (tests && tests.current === false) waiting.push('prompt tests on the current source');
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
    // #3029: the formal status that pdd read on its own; a Story with `## Rules to check` (rulesToCheck not false) needs a
    // recorded Proved or Not applicable result. With scenario vectors the code replay needs a typed block, so the row is
    // never "not needed" there. Without replay, malformed or stale supplied formal evidence also holds the PR.
    const formal = replay?.formal ?? r.formal;
    const status = replay || formal || small ? formalStatusText(formal, small ? true : r.rulesToCheck) : null;
    const needed = small || (replay ? r.rulesToCheck !== false : r.rulesToCheck === true);
    if (status?.status === 'recorded') {
      const scope = inertText(formal.scope, 80), counterexample = r.counterexample ?? replay?.counterexample;
      const result = FORMAL[formal.result] ?? (formal.result === 'failed' ? `Failed at ${counterexample ? codeSpan(clip(oneLine(counterexample), 80)) : 'the counterexample in Details'}`
        : formal.result === 'not_applicable' ? `Not applicable: ${inertText(formal.reason, 120)}` : `Not run: ${inertText(formal.reason, 120)}`);
      const control = formal.control_outcome === 'assertion_failure' ? '✗ fails (as expected)' : formal.control_outcome === 'not_run' ? '—' : inertText(formal.control_outcome, 40);
      rows.push([`Formal check${scope ? ` (${scope})` : ''}`, result, control]);
      if (formal.result === 'failed') blocked.push(`formal check failed${counterexample ? ` at ${codeSpan(clip(oneLine(counterexample), 80))}` : ''}`);
      else if (needed && (r.formalStep || small) && formal.result === 'not_run') blocked.push('formal check not run');
    } else if (status && (r.formalStep || small)) {
      // The same words, reason and repair step as the replay header; never a bare "not recorded".
      if (status.notNeeded && (replay || status.status === 'missing')) rows.push(['Formal check', 'not needed (no Rules to check in the Story)', '—']);
      else {
        rows.push(['Formal check', cell(`${status.words} — ${status.detail}. Repair: ${status.repair}.${status.note ? ` ${status.note}` : ''}`, 500), '—']);
        if (status.status === 'missing' && r.formalDone !== true) waiting.push('the formal result');
        else if (replay || needed || status.status !== 'missing') blocked.push(`formal check ${inertText(status.words, 80)}`);
      }
    } else if (r.formalStep) {
      // Without replay evidence (a small change) pdd records only that the formal step ran.
      rows.push(['Formal check', 'Not recorded: pdd has no formal result for this run (see Details)', '—']);
      if (r.formalDone !== true) waiting.push('the formal step');
    }
    const proof = r.proof;
    if (proof) {
      const coverage = facts.single && facts.workflow === 'small-change' && proof.kind === 'coverage' && proof.status === 'old-passes';
      const counted = Number.isSafeInteger(proof.total) ? ` (${proof.passed} of ${proof.total} tests)` : '';
      const cells = { proved: [`✓ pass${counted}`, '✗ fail (as expected)'], 'old-passes': [`✓ pass${counted}`, '✓ pass (should fail)'], 'wrong-reason': [`✓ pass${counted}`, '✗ fails for another reason'],
        'head-fails': ['✗ fail', '—'], 'no-changed-tests': ['no changed tests', '—'], 'not-run': ['not run', '—'], stale: ['⏳ stale (rerun `pdd workflow prove`)', '—'],
        unavailable: ['unavailable', '—'], pending: ['⏳ pending', '—'] }[proof.status] ?? [`✗ ${inertText(proof.status, 40)}`, '—'];
      // A feature table names its last column "Planted mistake"; this cell is the old code, so it says so.
      if (facts.workflow === 'feature' && cells[1] !== '—') cells[1] = `old code: ${cells[1]}`;
      if (coverage) cells[1] = '✓ pass (coverage only; not a defect proof)';
      rows.push([coverage ? 'Coverage validation' : 'Regression tests (old-code proof)', ...cells]);
      if (coverage) { /* Both snapshots pass; this is coverage, not a defect proof. */ }
      else if (PROOF_PROBLEM[proof.status]) blocked.push(PROOF_PROBLEM[proof.status]);
      else if (proof.status === 'stale') waiting.push('a fresh old-code proof');
      else if (proof.status === 'not-run' && pair) waiting.push('the old-code proof');
      else if (proof.status === 'no-changed-tests' && pair) blocked.push('the old-code proof found no changed tests');
      else if (!['proved', 'pending', 'not-run', 'no-changed-tests'].includes(proof.status)) blocked.push(`the old-code proof says ${inertText(proof.status, 40)}`);
    } else if (pair) waiting.push('the old-code proof');
  }
  const ci = r.ci === 'passing' ? '✓ green' : r.ci === 'failing' ? '✗ failing' : r.ci === 'none' ? 'no CI checks configured' : '⏳ pending';
  rows.push([code ? 'Full test suite (CI) on this commit' : 'Full test suite (CI)', ci, ...(code ? ['—'] : [])]);
  if (r.ci === 'failing') blocked.push('CI fails');
  else if (r.ci === 'none') blocked.push('no CI checks configured');
  else if (r.ci !== 'passing') waiting.push('CI');
  if (code && r.review !== null && r.review !== undefined) {
    const review = r.review === 'missing' ? 'not recorded' : r.review.mustFix ? `✗ ${r.review.mustFix} must-fix` : 'no must-fix';
    rows.push(['Fresh review', review, '—']);
    if (r.review === 'missing') waiting.push('the review');
    else if (r.review.mustFix) blocked.push(`review has ${r.review.mustFix} must-fix`);
  }
  const verdict = r.checker?.verdict, split = (r.checker?.verdicts ?? []).join(' and ');
  rows.push(['Independent checker', verdict === 'PASS' ? '✓ PASS' : verdict === 'FAIL' ? '✗ FAIL' : verdict === 'NOT SURE' ? 'NOT SURE' : verdict === 'split' ? `✗ split (${split || 'the verdicts differ'})` : manual ? '— (a person reviews)' : '⏳ pending', ...(code ? ['—'] : [])]);
  if (verdict === 'FAIL') blocked.push('the checker says FAIL');
  else if (verdict === 'NOT SURE') blocked.push('the checker is not sure');
  else if (verdict === 'split') blocked.push(`the checkers disagree on this head (${split || 'split'})`);
  else if (!verdict && !manual) waiting.push('the checker');
  const order = pr1Order(facts);
  if (order === 'first') waiting.push(`PR 1 (#${facts.pr1.number})`);
  // A red PR 1 merges only with this PR, so this PR must target the run's base first (Autopilot's merge conditions).
  else if (order === 'carried' && !facts.carriesPr1) waiting.push(`this PR to target ${facts.baseBranch ? codeSpan(facts.baseBranch) : 'the base branch'}`);
  else if (order === 'ci') waiting.push(`the CI of PR 1 (#${facts.pr1.number})`);
  else if (order === 'closed') blocked.push(`PR 1 (#${facts.pr1.number}) is closed without a merge`);
  return { rows, blocked, waiting };
}
// "Not fixed yet" (a warning-light PR, `Refs #N`) is a limit, never a claim: such a PR is never ready.
export function prStatus(facts) {
  const { blocked, waiting } = proofRows(facts);
  if (facts.notFixed) return `⛔ Not fixed yet${blocked.length ? `; ${blocked.join('; ')}` : ''}`;
  if (blocked.length) return `⛔ Blocked: ${blocked.join('; ')}`;
  if (waiting.length) return `⏳ Waiting for ${listed(waiting.includes('publication') ? ['the source to be published'] : waiting)}`;
  return '✅ Ready to merge';
}
// The status line says when pdd wrote it: " · Updated YYYY-MM-DD HH:MM UTC".
const stamp = at => Number.isFinite(at) ? ` · Updated ${new Date(at).toISOString().slice(0, 16).replace('T', ' ')} UTC` : '';
export const NOT_FIXED_LINE = 'Not fixed yet: this helps find the cause. The issue stays open.';
// Two readable parts that differ only in the time of their status line say the same.
export const sameReadableTop = (a, b) => [a, b].map(text => String(text ?? '').trimEnd().replace(/^([^\n]*?) · Updated \d{4}-\d\d-\d\d \d\d:\d\d UTC(?=\n|$)/, '$1')).every((text, _, all) => text === all[0]);

function table(header, rows) {
  return [`| ${header.join(' | ')} |`, `|${header.map(() => '---').join('|')}|`, ...rows.map(row => `| ${row.join(' | ')} |`)];
}
function issueChecklist(facts) {
  if (facts.workflow !== 'small-change' || facts.single !== true) return [];
  const items = facts.records?.checklist?.items ?? [];
  if (!items.length) return [];
  return ['## Issue checklist', '', ...table(['Item', 'Request', 'State', 'Source / quote', 'Evidence / exclusion'], items.map(item => [
    cell(item.id, Infinity), cell(item.request, Infinity), cell(item.state),
    cell(`${item.source}: ${item.quote}`, Infinity),
    cell(item.state === 'excluded' ? `${item.exclusion?.reason ?? ''}: "${item.exclusion?.quote ?? ''}"` : item.evidence, Infinity),
  ])), ''];
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
  // A saved copy of the facts keeps at most 40 files and their full count.
  const files = diff.files ?? [], count = Number.isSafeInteger(diff.count) ? Math.max(diff.count, files.length) : files.length, notes = facts.fields?.notes ?? {};
  const rows = files.slice(0, fileLimit).map(file => `- ${codeSpan(file.path)}${notes[file.path] ? `: ${inertText(notes[file.path], MAX_NOTE)}` : file.binary ? ' (binary)' : ` (+${file.added} −${file.removed})`}`);
  if (count > Math.min(fileLimit, files.length)) rows.push(`- …and ${plural(count - Math.min(fileLimit, files.length), 'more file')} (see the Files tab).`);
  return [`## What changed (+${diff.added} −${diff.removed}, ${plural(count, 'file')})`, '', ...rows, ''];
}
// "Fix" is a closing keyword: its label carries a zero-width space, so "**Fix:** #5 …" never closes issue #5.
function summary(facts) {
  const f = facts.fields ?? {}, bullet = (label, value) => value ? [`- **${label}:** ${inertText(value)}`] : [];
  const recorded = facts.layout === 'spec' ? '' : proofRows(facts).rows.filter(row => /^(?:Approved cases|Formal check|Regression tests|Coverage validation)/.test(row[0]))
    .map(([label, result, control]) => `${label}: ${result}${control && control !== '—' ? `; ${label.startsWith('Formal check') || facts.workflow === 'feature' && label.startsWith('Approved cases') ? 'control' : 'old code'}: ${control}` : ''}`).join('. ');
  const rows = facts.layout === 'spec' ? [...bullet('Problem', f.problem), ...bullet('This PR', f.thisPr || facts.thisPr), ...bullet('Verdict', f.verdict)]
    : facts.single ? [...bullet('Problem', f.problem), ...bullet('Change', f.change || f.fix), ...(recorded ? [`- **Result:** ${recorded}.`] : [])]
    : [...bullet('Problem', f.problem), ...bullet('Cause', f.cause), ...bullet('Fix\u200b', f.fix), ...(recorded ? [`- **Result:** ${recorded}.`] : [])];
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
  const number = facts.pr1?.number, order = pr1Order(facts);
  const pr1 = { carried: `This PR also merges PR 1 (#${number}). Do not merge PR 1 alone.`, first: `Builds on PR 1 (#${number}): merge it first.`,
    ci: `Builds on PR 1 (#${number}).`, closed: `Builds on PR 1 (#${number}), which is closed without a merge.` }[order];
  return [`**Merge:** ${merge}. ${reference}.`, ...(pr1 ? ['', pr1] : [])];
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
  const lines = [`${prStatus(facts)}${stamp(facts.updatedAt)}`, '', ...(facts.notFixed ? [NOT_FIXED_LINE, ''] : []),
    ...(stories.length ? ['## User story', '', ...stories.flatMap((story, index) => [...(index ? [''] : []), inertText(story, 600)]), ''] : []),
    ...summary(facts), ...issueChecklist(facts), ...casesTable(facts), ...changes(facts, fileLimit),
    `## ${facts.layout === 'spec' ? 'Checks' : 'Proof'}`, '', ...table(header, rows), '',
    ...(facts.layout === 'spec' ? [approvalLine(facts), ''] : []), ...readableNextLines(facts)];
  return { text: lines.join('\n'), notes };
}

// Each Markdown line outside fenced code goes through `change`; fence lines and fenced lines stay. A fence opens only as
// GitHub opens one (at most 3 spaces in front; a backtick fence has no backtick after it), and any line of the fence
// mark alone closes it. So pdd never sees code where GitHub sees text.
function textLines(text, change) {
  let fence = null;
  const rows = String(text ?? '').split('\n').map(line => {
    const mark = line.trim().match(/^(`{3,}|~{3,})/)?.[1];
    if (fence) { if (mark && line.trim().startsWith(fence) && !line.trim().slice(mark.length).trim()) fence = null; return line; }
    const open = /^ {0,3}(?:(`{3,})[^`]*|(~{3,}).*)$/.exec(line);
    if (open) { fence = open[1] ?? open[2]; return line; }
    return change(line);
  });
  return { rows, fence };
}

// pdd-owned and agent text inside the Details section never closes it early: a `</details>` with no open `<details>`
// before it (outside code spans and fences) shows as text, an open block is closed at the end, and so is an open fence.
export function balancedDetails(text) {
  let depth = 0;
  const { rows, fence } = textLines(text, line => line.replace(/((?<![`\\])(`+)(?!`).*?(?<!`)\2(?!`))|<details\b[^>]*>|<\/details\s*>/gi, (tag, code) => {
    if (code) return code;
    if (/^<details/i.test(tag)) { depth++; return tag; }
    if (depth) { depth--; return tag; }
    return tag.replace(/</g, '&lt;').replace(/>/g, '&gt;');
  }));
  return [...rows, ...(fence ? [fence] : []), ...Array(depth).fill('</details>')].join('\n');
}

// Agent Markdown that pdd shows whole in Details (verify.md, the verdict and change lines of a check): outside code
// spans, fenced code and indented code blocks, every closing keyword gets a zero-width space after it, as in the readable
// part. An address, a link target and an HTML tag keep their text, so their links still work; a keyword at the end of an
// address gets one only when an issue reference follows ("…/fixes #5"), so "…/tree/fix" stays a working link. So only
// pdd's own `Closes #N` can close an issue.
const SHOWN = /((?:https?|ftp):\/\/[^\s<>]*|\bwww\.[^\s<>]*)|<\/?[A-Za-z][A-Za-z0-9-]*(?:[\s/][^<>\n]*)?>|\]\([^()\s]*\)|\b(fix(?:es|ed)?|close[sd]?|resolve[sd]?)\b(?!\u200b)/gi;
const REFERENCE_AFTER = /^[\s:*_~]*(?:[\w.-]+\/[\w.-]+)?#\d/;
const closingWords = text => text.replace(SHOWN, (token, address, word, offset, whole) => word ? `${word}\u200b`
  : address && REFERENCE_AFTER.test(whole.slice(offset + token.length)) ? address.replace(/\b(fix(?:es|ed)?|close[sd]?|resolve[sd]?)(?=[:*_~.,!?]*$)/i, '$1\u200b') : token);
const LIST_ITEM = /^ {0,3}(?:[-*+]|\d{1,9}[.)])(?:\s|$)/;
export function closingInert(text) {
  // An indented code block (4 spaces or a tab) starts after a blank line outside a list and stays exact, like a fence.
  let code = false, blank = true, list = false;
  return textLines(text, line => {
    const empty = !line.trim(), indented = /^(?: {4}|\t)/.test(line), wasBlank = blank;
    blank = empty;
    if (empty) return line;
    if (indented && (code || (wasBlank && !list))) { code = true; return line; }
    code = false;
    if (LIST_ITEM.test(line)) list = true; else if (!indented && wasBlank) list = false;
    let out = '', at = 0;
    for (const match of line.matchAll(CODE_SPAN)) { out += closingWords(line.slice(at, match.index)) + match[0]; at = match.index + match[0].length; }
    return out + closingWords(line.slice(at));
  }).rows.join('\n');
}

// One line for a person who edits the description, right after the Details line (an HTML comment, so readers never see it).
export const TOP_NOTE = '<!-- pdd writes this description. It rewrites the part above Details at each pdd workflow status and all of it at each push. Write your notes in a PR comment. -->';
// The whole description: the readable part, then one closed Details section with everything pdd recorded.
export function readablePrBody(top, details) {
  return `${top.trimEnd()}\n\n${DETAILS_OPEN}\n\n${TOP_NOTE}\n\n${String(details).trim()}\n\n</details>\n`;
}
// The pdd-written part inside the Details section of a readable description, and any text a person added after it;
// null for a description without that section (an older pdd wrote it, so all of it is pdd body).
export function detailsOf(body) {
  const rows = String(body ?? '').split('\n'), open = rows.findIndex(row => /^<details\b/i.test(row));
  if (open < 0 || rows[open] !== DETAILS_OPEN) return null;
  let close = rows.length - 1;
  while (close > open && rows[close] !== '</details>') close--;
  const details = rows.slice(open + 1, close).join('\n').trim();
  return close > open ? { details: details.startsWith(TOP_NOTE) ? details.slice(TOP_NOTE.length).trim() : details, after: rows.slice(close + 1).join('\n').trim() } : null;
}

// Typed interpreter boundaries retain the native helpers' arbitrary map keys as JSON text.
export const readPrFieldsJson = texts => JSON.stringify(readPrFields(texts));
export function readablePrTopJson({ factsJson, fileLimit } = {}) {
  let facts;
  try { facts = JSON.parse(factsJson); } catch { /* Report the typed adapter error below. */ }
  if (!facts || typeof facts !== 'object' || Array.isArray(facts))
    throw Object.assign(new Error('The renderer needs a JSON facts object.'), { code: 'invalid-facts' });
  return readablePrTop(facts, { fileLimit });
}

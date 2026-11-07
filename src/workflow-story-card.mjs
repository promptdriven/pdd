// Generated from prompts/cli/workflow-story-card.prompt.md.
import { createHash } from 'node:crypto';
import { existsSync, readFileSync, readdirSync, realpathSync } from 'node:fs';
import { homedir } from 'node:os';
import { isAbsolute, join, relative, resolve, sep } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { captureSource, findTests } from './runtime-preflight.mjs';

const SCENARIO = 'prompt-runtime.program-scenario.v1';
const BATCH = /^\d{8}-\d{6}-[a-z0-9]{4}$/;
const CARD_LINES = 160, PART_LINES = 12, TABLE_ROWS = 8, CHANGE_LINES = 20, LIST_LINES = 20;
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
const oneLine = value => String(value ?? '').replace(/\s+/g, ' ').trim();
// About max characters, cut at a word end with "…".
function clip(text, max) {
  const value = oneLine(text);
  if ([...value].length <= max) return value;
  const cut = [...value].slice(0, max).join(''), word = cut.replace(/\s+\S*$/, '');
  return `${(word.length > max / 2 ? word : cut).trimEnd()}…`;
}
const cell = (text, max = 80) => clip(text, max).replaceAll('|', '\\|');
const canonical = value => Array.isArray(value) ? value.map(canonical) : value && typeof value === 'object'
  ? Object.fromEntries(Object.keys(value).sort().map(key => [key, canonical(value[key])])) : value;
const compact = value => { try { return JSON.stringify(value) ?? 'null'; } catch { return 'null'; } };

const segments = path => String(path).split('/');
const storyFolder = path => segments(path).slice(0, -1).includes('user_stories');
const isPlan = path => storyFolder(path) && /^plan\.md$/i.test(segments(path).at(-1));
const isStory = path => path.endsWith('.md') && storyFolder(path) && !/^(?:plan|readme)\.md$/i.test(segments(path).at(-1));
const testFolder = path => segments(path).slice(0, -1).some(part => part === 'tests' || part === 'test');

function inside(root, file) {
  const path = relative(root, file);
  return path !== '' && path !== '..' && !path.startsWith(`..${sep}`) && !isAbsolute(path);
}
function readBytes(root, path) {
  try {
    if (typeof path !== 'string' || isAbsolute(path)) return null;
    const base = realpathSync(root), file = resolve(root, path);
    if (!inside(resolve(root), file) || !inside(base, realpathSync(file))) return null;
    return readFileSync(file);
  } catch { return null; }
}
function readText(root, path) { return readBytes(root, path)?.toString('utf8') ?? null; }
function readScenario(root, path) {
  const text = readText(root, path);
  if (text === null) return { path, text: null, doc: null };
  try {
    const doc = JSON.parse(text);
    return { path, text, doc: doc?.schema_version === SCENARIO ? doc : undefined };
  } catch { return { path, text, doc: null }; }
}
// The run's changed test files: every changed scenario, and a changed JSON file in a test folder that does not parse.
function changedTests(root, changed) {
  return [...new Set(changed)].filter(path => path.endsWith('.json')).sort().map(path => readScenario(root, path))
    .filter(item => item.doc || item.doc === null && testFolder(item.path));
}

// The lines of one `## ` section, without its heading and blank lines.
function section(text, heading) {
  const lines = String(text ?? '').split(/\r?\n/), start = lines.findIndex(line => heading.test(line.trim()));
  if (start < 0) return null;
  const rest = lines.slice(start + 1), end = rest.findIndex(line => /^#{1,2}\s/.test(line));
  return (end < 0 ? rest : rest.slice(0, end)).map(line => line.trimEnd()).filter(line => line.trim());
}
const CRITERIA = /^##\s+acceptance criteria\s*$/i, KEEP = /^##\s+(?:what\s+)?must not change\s*$/i, RULES = /^##\s+rules to check\s*$/i;
function criteriaOf(text) {
  const blocks = [];
  for (const line of section(text, CRITERIA) ?? []) {
    if (/^\s*\d+[.)]\s+/.test(line)) blocks.push(line.trim());
    else if (blocks.length) blocks[blocks.length - 1] += `\n${line}`;
  }
  return blocks;
}
function bounded(lines, path, word = 'lines') {
  if (lines.length <= PART_LINES) return lines;
  return [...lines.slice(0, PART_LINES), `… ${lines.length - PART_LINES} more ${word} in ${path}`];
}

function expectedText(step) {
  return [step?.expected_error !== undefined && step?.expected_error !== null ? `error ${step.expected_error}` : null,
    ...(Array.isArray(step?.checks) ? step.checks : []).map(check => `${check?.criterion_id ?? '?'} ${check?.path ?? '?'} ${check?.op ?? '?'} ${compact(check?.value)}`)]
    .filter(Boolean).join('; ') || 'none';
}
const caseName = (step, index) => typeof step?.step_id === 'string' && step.step_id ? step.step_id : `step ${index + 1}`;
function table(root, test) {
  const where = join(root, test.path);
  if (!test.doc) return [`Test cases (${where}): (cannot read ${where})`];
  const steps = Array.isArray(test.doc.steps) ? test.doc.steps : [];
  const rows = steps.slice(0, TABLE_ROWS).map((step, index) => `| ${cell(caseName(step, index), 60)} | ${cell(compact(step?.input ?? null), 70)} | ${cell(expectedText(step), 140)} |`);
  return [`Test cases (${where}):`, '| Case | Input | Expected |', ...rows,
    ...(steps.length > TABLE_ROWS ? [`… ${steps.length - TABLE_ROWS} more cases in ${where}`] : []), ...(steps.length ? [] : ['(no cases)'])];
}

// What the reporter asked, from the issue text that the run saved at start.
function askedLine(asked) {
  if (typeof asked !== 'string' || !asked.trim()) return 'Asked: not saved in this run; read the issue.';
  const lines = asked.replace(/<!--[\s\S]*?(?:-->|$)/g, '').split(/\r?\n/);
  const quoteStart = lines.findIndex(line => /^\s*>/.test(line));
  let words;
  if (quoteStart >= 0) {
    const quote = [];
    for (const line of lines.slice(quoteStart)) { if (!/^\s*>/.test(line)) break; quote.push(line.replace(/^\s*>\s?/, '')); }
    words = quote.join(' ');
  } else {
    const paragraphs = lines.join('\n').split(/\n\s*\n/).map(text => text.trim()).filter(text => text && !/^#/.test(text));
    words = paragraphs[0] ?? '';
  }
  return oneLine(words) ? `Asked: "${clip(words, 300)}"` : 'Asked: not saved in this run; read the issue.';
}
const VERDICT = /\bVerdict:[^\n]*?(?=;?\s*(?:\n|\bBefore\s*[✗✓:]|\bPrompt tests\b|\bRuntime check\b|\bReport\b|$))/;
function verdictLine(run) {
  const records = Object.values(run?.done ?? {}).filter(record => typeof record?.summary === 'string').sort((a, b) => (b.at ?? 0) - (a.at ?? 0));
  for (const record of records) { const found = VERDICT.exec(record.summary); if (found) return clip(found[0], 300); }
  return 'Verdict: not recorded yet.';
}

function storyBlock(root, path, tests) {
  const where = join(root, path), text = readText(root, path);
  if (text === null) return { full: [`Story: ${where}`, `  (cannot read ${where})`], short: `Story: ${where} (cannot read)` };
  const criteria = criteriaOf(text), keep = section(text, KEEP), rules = section(text, RULES), own = tests.filter(test => test.doc?.story_path === path);
  const indent = lines => lines.map(line => `  ${line}`);
  const full = [`Story: ${where}`,
    ...indent(criteria.length ? ['Acceptance criteria:', ...bounded(criteria.flatMap(block => block.split('\n')), where)] : ['Acceptance criteria: none found.']),
    ...indent(keep?.length ? ['Must not change:', ...bounded(keep, where)] : ['Must not change: not stated.']),
    ...indent(rules?.length ? ['Rules to check:', ...bounded(rules, where)] : ['Rules to check: none.']),
    ...own.flatMap(test => indent(table(root, test)))];
  const cases = own.reduce((sum, test) => sum + (Array.isArray(test.doc?.steps) ? test.doc.steps.length : 0), 0);
  return { full, short: `Story: ${where} (not shown in full: ${criteria.length} criteria, ${cases} cases)`, own };
}

export function storyCard({ run, root, changed = [], prompts = [], results = [], changes = [], through } = {}) {
  root ??= run?.root;
  const paths = [...new Set(changed)].sort(), tests = changedTests(root, paths);
  const stories = [...new Set([...paths.filter(isStory), ...tests.map(test => test.doc?.story_path).filter(path => typeof path === 'string' && isStory(path))])].sort();
  const head = [`Story card: ${run?.repo ?? '?'}#${run?.number ?? '?'} "${oneLine(run?.issue?.title)}"`, `Issue: ${run?.issue?.url ?? 'unknown'}`, askedLine(run?.issue?.asked)];
  const verdict = verdictLine(run);
  if (verdict) head.push(verdict);
  const promptRows = [...prompts].sort((a, b) => String(a.path).localeCompare(String(b.path)));
  const promptLines = promptRows.length ? ['Prompts that change:', ...promptRows.slice(0, LIST_LINES).map(row => `  ${join(root, row.path)} (+${row.added ?? '?'} −${row.removed ?? '?'} lines)`),
    ...(promptRows.length > LIST_LINES ? [`  … ${promptRows.length - LIST_LINES} more prompts`] : [])] : ['Prompts that change: none.'];
  const plans = paths.filter(isPlan);
  const plan = plans.slice(0, LIST_LINES).map(path => `Plan: ${join(root, path)}`);
  if (plans.length > LIST_LINES) plan.push(`… ${plans.length - LIST_LINES} more plans`);
  const changeLines = changes.length ? ['Changed since your approval:', ...changes.slice(0, CHANGE_LINES).map(line => `  ${line}`), ...(changes.length > CHANGE_LINES ? [`… ${changes.length - CHANGE_LINES} more changes`] : [])] : [];
  const resultLines = results.length ? ['Prompt tests:', ...results.slice(0, LIST_LINES).map(line => `  ${oneLine(line)}`), ...(results.length > LIST_LINES ? [`  … ${results.length - LIST_LINES} more lines`] : [])] : [];
  const code = (run?.areas ?? []).some(area => area?.then === 'ask-code');
  const tail = [code ? through === 'code' ? 'Next step: when the check passes in full, pdd opens PR 1, then makes the code PR.'
      : 'Next step: when the check passes in full, pdd opens PR 1 and stops. Say so if you want the code PR too.'
      : 'Next step: pdd opens the PR when the check passes in full.',
    'Try: you can ask to try it in the Simulator before you approve.', 'Approve, or tell me what to change.'];
  const shown = new Set(), blocks = stories.slice(0, LIST_LINES).map(path => storyBlock(root, path, tests));
  for (const block of blocks) for (const test of block.own ?? []) shown.add(test.path);
  const others = tests.filter(test => !shown.has(test.path));
  const allOtherLines = others.flatMap(test => table(root, test).map(line => `  ${line}`));
  const otherLines = others.length ? ['Tests:', ...allOtherLines.slice(0, LIST_LINES), ...(allOtherLines.length > LIST_LINES ? [`… ${allOtherLines.length - LIST_LINES} more test lines; read the test files`] : [])] : [];
  let room = CARD_LINES - head.length - promptLines.length - plan.length - changeLines.length - resultLines.length - tail.length - otherLines.length - 1;
  const body = [];
  let hidden = 0;
  for (const block of blocks) {
    if (!hidden && block.full.length <= room) { body.push(...block.full); room -= block.full.length; }
    else { hidden++; body.push(block.short); room -= 1; }
  }
  if (hidden) body.push(`… ${hidden} more Stor${hidden === 1 ? 'y' : 'ies'} not shown in full. Read their files.`);
  if (stories.length > LIST_LINES) body.push(`… ${stories.length - LIST_LINES} more Stories; read the run files.`);
  if (!blocks.length) body.push('Story: no changed Story file yet.');
  const main = [...head, ...body, ...otherLines, ...promptLines, ...plan, ...changeLines, ...resultLines];
  const limit = CARD_LINES - tail.length - 1;
  return [...(main.length + tail.length <= CARD_LINES ? main : [...main.slice(0, limit), `… ${main.length - limit} more lines; read the run files.`]), ...tail].join('\n');
}

// What the person decides in a test file: its criteria and each case's expected values (not its input or check paths).
function expectedCases(doc) {
  return (Array.isArray(doc?.steps) ? doc.steps : []).map((step, index) => ({ case: caseName(step, index),
    error: step?.expected_error ?? null,
    expected: (Array.isArray(step?.checks) ? step.checks : []).map(check => [check?.criterion_id ?? null, check?.target ?? null, check?.op ?? null, check?.value ?? null])
      .map(row => JSON.stringify(canonical(row))).sort() }));
}
export function storyFingerprint({ root, changed = [] } = {}) {
  const paths = [...new Set(changed)].sort();
  const testsInRun = changedTests(root, paths);
  const storyPaths = [...new Set([...paths.filter(path => isStory(path) || isPlan(path)), ...testsInRun.map(test => test.doc?.story_path).filter(path => typeof path === 'string' && isStory(path))])].sort();
  const stories = storyPaths.flatMap(path => {
    const bytes = readBytes(root, path);
    if (bytes === null) return [{ path, sha256: null, criteria: [] }];
    return [{ path, sha256: sha256(bytes), criteria: criteriaOf(bytes.toString('utf8')) }];
  });
  const tests = testsInRun.map(test => {
    if (!test.doc) return { path: test.path, sha256: sha256(test.text ?? ''), cases: [] };
    const cases = expectedCases(test.doc), steps = Array.isArray(test.doc.steps) ? test.doc.steps : [];
    return { path: test.path, sha256: sha256(JSON.stringify(canonical({ criteria: test.doc.criteria ?? null, cases }))),
      cases: cases.map((item, index) => ({ case: item.case, sha256: sha256(JSON.stringify(item)), text: clip(expectedText(steps[index]), 120) })) };
  });
  return { stories, tests };
}

export function fingerprintChanges(saved, current) {
  const lines = [];
  const rows = value => new Map((Array.isArray(value) ? value : []).filter(row => row && typeof row.path === 'string').map(row => [row.path, row]));
  const pair = (before, after, kind, changedLines) => {
    for (const path of [...new Set([...before.keys(), ...after.keys()])].sort()) {
      const old = before.get(path), now = after.get(path);
      if (!now) lines.push(`${kind} removed: ${path}`);
      else if (!old) lines.push(`${kind} added: ${path}`);
      else if (old.sha256 !== now.sha256) lines.push(...changedLines(path, old, now));
    }
  };
  pair(rows(saved?.stories), rows(current?.stories), 'Story', (path, old, now) => {
    const was = new Set(old.criteria ?? []), is = new Set(now.criteria ?? []);
    return [`Story changed: ${path}`, ...[...is].filter(line => !was.has(line)).map(line => `  + ${clip(line, 160)}`),
      ...[...was].filter(line => !is.has(line)).map(line => `  − ${clip(line, 160)}`)];
  });
  pair(rows(saved?.tests), rows(current?.tests), 'Test', (path, old, now) => {
    const was = new Map((old.cases ?? []).map(item => [item.case, item])), is = new Map((now.cases ?? []).map(item => [item.case, item]));
    const cases = [...new Set([...was.keys(), ...is.keys()])].filter(name => was.get(name)?.sha256 !== is.get(name)?.sha256)
      .map(name => `  case ${clip(name, 60)}: expected was ${was.get(name)?.text ?? 'none'}; now ${is.get(name)?.text ?? 'none'}`);
    return cases.length ? [`Test changed: ${path}`, ...cases] : [`Test changed: ${path} (criteria)`];
  });
  return lines.length > CHANGE_LINES ? [...lines.slice(0, CHANGE_LINES), `… ${lines.length - CHANGE_LINES} more changes`] : lines;
}

function readJson(path) { try { return JSON.parse(readFileSync(path, 'utf8')); } catch { return null; } }
const real = path => { try { return realpathSync(path); } catch { return resolve(path); } };
const NO_VERDICT_STATES = new Set(['refused', 'not_run', 'unknown', 'queued', 'running']);
// pdd's own saved check results decide whether the prompt check passed in full on the current files.
export function fullCheckPass({ root, since = 0, tests = [], prompts = [] } = {}, ports = {}) {
  const env = ports.env ?? process.env, capture = ports.capture ?? captureSource;
  const directory = join(resolve(env.PDD_STATE_DIR || join(env.HOME || homedir(), '.pdd', 'runtime')), 'batches');
  const problems = [], judged = [], wanted = real(root), latest = new Map();
  let names = [];
  try { names = readdirSync(directory).filter(name => BATCH.test(name)).sort(); } catch { names = []; }
  for (const name of names) {
    const batch = readJson(join(directory, name, 'batch.json'));
    if (!batch || batch.batch !== name || batch.intent !== 'check' || typeof batch.root !== 'string' || !Array.isArray(batch.rows) || real(batch.root) !== wanted) continue;
    const at = Date.parse(batch.created_at);
    if (!Number.isFinite(at) || at < since) continue;
    const summary = readJson(join(directory, name, 'summary.json'));
    for (const row of batch.rows) {
      if (typeof row?.test !== 'string') continue;
      const prior = latest.get(row.test);
      if (!prior || at > prior.at || at === prior.at && name > prior.name) latest.set(row.test, { name, at, batch, summary });
    }
  }
  let discovered = [];
  try { discovered = (ports.findTests ?? findTests)({ root }).tests.map(test => test.path); }
  catch (error) { problems.push({ kind: 'unavailable', path: '.', detail: `cannot discover the project tests (${clip(error.message, 120)})` }); }
  const selected = [...new Set([...tests, ...discovered, ...[...latest.keys()].filter(path => existsSync(join(root, path)))])].sort();
  const captures = new Map(), covered = new Set();
  const captured = list => {
    const key = JSON.stringify([...list].sort());
    if (!captures.has(key)) { try { captures.set(key, capture(root, { tests: [...list].sort(), appMap: null })); } catch (error) { captures.set(key, { error }); } }
    return captures.get(key);
  };
  for (const path of selected) {
    const found = latest.get(path);
    if (!found) { problems.push({ kind: 'missing', path, detail: 'no saved check has this test' }); continue; }
    const summary = found.summary;
    if (!summary || summary.batch !== found.name || typeof summary.repo !== 'string' || real(summary.repo) !== wanted
      || typeof summary.source_sha256 !== 'string' || summary.source_sha256 !== found.batch.source_sha256) {
      problems.push({ kind: 'unavailable', path, detail: `batch ${found.name}: summary identity does not match the batch` }); continue;
    }
    const row = Array.isArray(found.summary?.rows) ? found.summary.rows.find(item => item?.test === path) : undefined;
    const state = row?.state ?? 'unknown';
    judged.push({ path, batch: found.name, state });
    if (!row) { problems.push({ kind: 'no-verdict', path, detail: `batch ${found.name} has no saved result for this test` }); continue; }
    if (state === 'failed') { problems.push({ kind: 'failed', path, detail: `batch ${found.name}: ${clip(row.summary_line ?? 'failed', 200)}` }); continue; }
    if (state !== 'passed') { problems.push({ kind: NO_VERDICT_STATES.has(state) ? 'no-verdict' : 'unavailable', path, detail: `batch ${found.name}: ${state}` }); continue; }
    const criteria = row.criteria;
    if (!criteria || !Number.isInteger(criteria.total) || !Number.isInteger(criteria.passed)) { problems.push({ kind: 'unavailable', path, detail: `batch ${found.name}: criteria not reported` }); continue; }
    const scenario = readScenario(root, path).doc;
    if (criteria.total <= 0 || criteria.total !== scenario?.criteria?.length || criteria.passed !== criteria.total) { problems.push({ kind: 'failed', path, detail: `batch ${found.name}: ${criteria.passed} of ${criteria.total} criteria` }); continue; }
    const snapshots = Array.isArray(found.batch.contract_snapshots) ? found.batch.contract_snapshots : null;
    const saved = snapshots?.find(item => Array.isArray(item?.tests) && item.tests.includes(path));
    if (!saved && (snapshots?.length || found.batch.contract_snapshots != null && !snapshots)) {
      problems.push({ kind: 'unavailable', path, detail: `batch ${found.name}: source snapshot row is missing or invalid` }); continue;
    }
    if (saved) {
      const now = captured(saved.tests);
      if (now.error) { problems.push({ kind: 'unavailable', path, detail: `cannot read the current source (${clip(now.error.message, 120)})` }); continue; }
      const current = (now.stories ?? []).find(item => item.story_path === saved.story_path);
      if (!current || saved.unavailable || current.unavailable || !isDeepStrictEqual(saved, current)) { problems.push({ kind: 'changed', path, detail: `a file of batch ${found.name} changed after the check` }); continue; }
      for (const file of saved.files ?? []) covered.add(file.path);
    } else {
      const all = [...new Set(found.batch.rows.map(item => item?.test).filter(test => typeof test === 'string'))];
      const now = captured(all);
      if (now.error) { problems.push({ kind: 'unavailable', path, detail: `cannot read the current source (${clip(now.error.message, 120)})` }); continue; }
      if (now.sha256 !== found.batch.source_sha256) { problems.push({ kind: 'changed', path, detail: `a file of batch ${found.name} changed after the check` }); continue; }
      for (const file of Array.isArray(found.batch.files) ? found.batch.files : []) covered.add(typeof file === 'string' ? file : file?.path);
    }
  }
  for (const path of [...new Set(prompts)].sort()) if (!covered.has(path)) problems.push({ kind: 'prompt-not-checked', path, detail: 'no passing check reads this prompt' });
  return { pass: judged.length > 0 && !problems.length, tests: judged, problems };
}

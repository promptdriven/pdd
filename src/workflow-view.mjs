// Generated from prompts/cli/workflow-view.prompt.md (sha256: 60430d44805151bd1392ff678c52fffa507500abeaf09835350db93a7cacaf6e).
import { execFile } from 'node:child_process';
import { lstatSync, readFileSync, readdirSync, realpathSync } from 'node:fs';
import { isAbsolute, join, relative, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { promisify } from 'node:util';
import { resolveRun } from './workflow-runs.mjs';
import { findTests, interfaceBlocks, isSecretPath, LIMITS, proseSha256 } from './runtime-seam.mjs';
import { PROMPT_TESTS_WORDS } from './runtime-seam.mjs';
import { resultLines } from './workflow-results.mjs';

const execute = promisify(execFile);
const text = value => String(value ?? '').replace(/[\x00-\x1f\x7f]/g, ' ').trim();
const array = value => Array.isArray(value) ? value : [];
// Prompt tests lines, also the `Runtime check` lines of older summaries; a line ends at a break or a "; " before the next entry.
const LINE_BREAK = new RegExp(`\\n|;\\s*(?=Report:|Try:|${PROMPT_TESTS_WORDS})`), LINE_START = new RegExp(`^${PROMPT_TESTS_WORDS}`);
const ended = run => ['completed', 'cancelled'].includes(run.state);
function localPath(root, path) {
  if (typeof path !== 'string' || !path || isAbsolute(path) || path.includes('\\') || path.split('/').some(p => p === '..' || !p) || /[\x00-\x1f]/.test(path)) return null;
  return resolve(root, path);
}
function fileInfo(root, path, directory = false) {
  try {
    const rel = relative(root, path), expected = localPath(realpathSync(root), rel);
    if (!expected || realpathSync(path) !== expected) return null;
    const stat = lstatSync(path);
    return (directory ? stat.isDirectory() : stat.isFile()) ? stat : null;
  } catch { return null; }
}
function readArtifact(root, path) {
  const file = localPath(root, path), stat = file && fileInfo(root, file);
  if (!stat || stat.size > LIMITS.bytes || isSecretPath(path)) return null;
  try { return readFileSync(file, 'utf8'); } catch { return null; }
}
function promptState(source) {
  const blocks = interfaceBlocks(source);
  if (!blocks.length) return null;
  try {
    const doc = JSON.parse(blocks[0][1]);
    if (blocks.length !== 1 || !['draft', 'approved'].includes(doc?.status)) return 'invalid interface; needs person review';
    if (doc.prose_sha256 !== proseSha256(source)) return `${doc.status === 'approved' ? 'stale approval' : 'stale draft hash'}; needs person review`;
    return doc.status === 'approved' ? 'approved (current prose)' : 'draft; needs person review at the next ready gate';
  } catch { return 'invalid interface; needs person review'; }
}

// This module deliberately uses no runner/chat helpers and never refreshes external state.
export async function viewRun({ ref, cwd }, ports = {}) {
  const found = await resolveRun(ref, { cwd }, ports);
  if (found.error) return { exitCode: 1, message: found.error };
  const run = found.run, root = resolve(run.root), area = array(run.areas)[run.area];
  const exec = ports.execFile ?? ((file, args, opts) => execute(file, args, { ...opts, encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 }));
  const git = async args => {
    try { const r = await exec('git', args, { cwd: root }); return r.code === undefined || r.code === 0 ? r.stdout : null; }
    catch { return null; }
  };
  const revision = await git(['rev-parse', '--verify', 'HEAD']);
  const dirty = await git(['--no-optional-locks', 'status', '--porcelain=v1', '-z', '--untracked-files=normal']);
  const changed = run.baseSha ? await git(['diff', '--no-ext-diff', '--no-textconv', '--name-only', '-z', run.baseSha, '--']) : null;
  const listed = changed ?? await git(['ls-files', '-z']);
  const extra = await git(['ls-files', '--others', '--exclude-standard', '-z']);
  const files = new Map(), prompts = new Map(), tests = new Map();
  // Tests are found by the test name rule (runtime-preflight), never by their content or size.
  let discovery = null;
  try { for (const test of findTests({ root }).tests) for (const file of test.files ?? [test.path]) tests.set(file, test); }
  catch (error) { discovery = `Test discovery unavailable: ${text(error.message)}`; }
  const add = (role, path) => {
    const file = localPath(root, path);
    if (file && !isSecretPath(path)) files.set(file, { role, path });
  };
  for (const path of new Set((String(listed ?? '') + '\0' + String(extra ?? '')).split('\0').filter(Boolean))) {
    if (path.endsWith('.prompt.md')) add('Prompt', path);
    else if (path.endsWith('.svg')) add('View', path);
    else if (path.endsWith('.md') && (path.split('/').includes('user_stories') || /(?:^|\/)plan\.md$/i.test(path))) add('Story/plan', path);
    else if (path.endsWith('.json')) {
      const test = tests.get(path);
      if (test) {
        // Malformed or conflicting tests are linked for review too.
        add('Test cases', path);
        for (const story of test.storyPaths ?? [test.storyPath]) add('Story', story);
        for (const step of array(test.doc?.steps)) add('Prompt', step?.entry_path);
        for (const entry of array(test.doc?.entry_paths)) add('Prompt', entry);
      } else {
        let doc; try { doc = JSON.parse(readArtifact(root, path)); } catch { /* not an app map */ }
        if (doc?.schema_version === 'prompt-runtime.app-map.v1' || /(?:^|\/)(?:test|tests)\//.test(path)) add('Test/app map', path);
      }
    }
  }
  for (const { path } of files.values()) if (path.endsWith('.prompt.md')) {
    const source = readArtifact(root, path), state = source === null ? null : promptState(source);
    if (state) prompts.set(path, state);
  }
  const gateFiles = [];
  try {
    const gateRoot = resolve(run.commonDir ?? root);
    if (!fileInfo(gateRoot, run.runDir, true)) throw Error('Gate note folder unavailable');
    for (const path of readdirSync(run.runDir).filter(path => path.endsWith('.md')).sort()) {
      const file = join(run.runDir, path); gateFiles.push(`  Gate note: ${pathToFileURL(file).href}${fileInfo(gateRoot, file) ? '' : ' (unavailable)'}`);
    }
  } catch { gateFiles.push('  Gate notes unavailable.'); }
  const summaries = Object.values(run.done ?? {}).map(item => String(item?.summary ?? ''));
  const linkText = [...summaries, ...array(run.links).map(item => typeof item === 'string' ? item : item?.url ?? item?.href ?? '')].join('\n');
  const urls = [...new Set(linkText.match(/https?:\/\/[^\s<>"'`]+/g) ?? [])].map(url => url.replace(/[),.;]+$/, ''));
  const reports = urls.filter(url => /\/r\//.test(url)), tries = urls.filter(url => /\/s\//.test(url));
  const runtime = summaries.flatMap(summary => summary.split(LINE_BREAK)).filter(line => LINE_START.test(line.trim()));
  const gate = run.gate && (!ended(run) || run.state === 'completed' && run.gate.kind === 'ask-code') ? run.gate : null;
  const pending = gate?.kind === 'ask-code' ? 'Optional code-work authorization: make the code PR, or stop at PR 1.'
    : gate?.kind === 'approve-pr' ? `Approve ${text(gate.area)} after review/Try to open the PR.`
    : gate ? `Approve the ${text(gate.area)} area or ask for changes.` : ended(run) ? 'No active gate.'
    : run.state === 'waiting' && array(run.pr).some(pr => pr.stage === area?.name) ? 'Review and merge the recorded PR on GitHub; external status is saved, not refreshed.'
    : 'No gate open yet; the current area still needs to finish.';
  const approvals = array(run.decisions).filter(item => item.decision === 'approve');
  const lines = [`${text(run.repo)}#${run.number} "${text(run.issue?.title)}" — read-only review`,
    `Problem and discussion: ${text(run.issue?.url)}`, `State: ${text(run.state)} (saved; external status is not refreshed)`,
    `Area: ${text(area?.name ?? 'none')}`, `Gate: ${gate ? `${text(gate.area)} (${text(gate.kind ?? 'approve')})` : 'none'}`,
    ...(run.question && !ended(run) && (!gate || run.question.at >= gate.at) ? [`Question: ${text(run.question.text)}`] : []),
    ...(run.chatFailure ? [`Chat: ${text(run.chatFailure.code)} — ${text(run.chatFailure.message)}`] : []),
    ...(approvals.length ? approvals.map(item => `Recorded approval: ${text(item.stage)} approved via ${text(item.via)} at ${Number.isFinite(item.at) ? new Date(item.at).toISOString() : 'unknown time'}.`) : ['Recorded approvals: none.']),
    `Pending: ${pending}`, 'One ready-gate approval covers the gate and all its selected draft prompts. A later code-or-stop gate needs its own decision. Standalone prompt approval covers only that prompt.',
    ...[...prompts].map(([path, state]) => `Prompt status: ${text(path)} — ${state}`),
    ...(array(run.pr).length ? run.pr.map(pr => `PR: ${text(pr.url)} (${text(pr.state ?? 'unknown')}, saved)`) : ['PRs: none recorded.']),
    ...runtime.map(line => text(line)), ...(reports.length ? reports.map(url => `Report: ${text(url)}`) : ['Interpreter reports: not recorded.']),
    ...(tries.length ? tries.map(url => `Try: ${text(url)}`) : ['Try: not recorded.']),
    ...Object.entries(run.done ?? {}).flatMap(([step, record]) => [
      `Step: ${text(record.area ?? array(run.areas).find(area => array(area.steps).includes(step))?.name ?? 'unknown')} / ${text(step)}`,
      ...resultLines(record.pddResults ?? []).map(line => `  ${line}`),
      ...(record.summary ? [`  Agent note — not checked by pdd: ${text(record.summary)}`] : [])]),
    `Revision: ${revision?.trim() ?? 'unavailable'}; ${dirty === null ? 'working-tree state unavailable' : dirty ? 'uncommitted changes' : 'clean checkout'}.`,
    'Review links show current files; recorded approvals do not certify later edits.',
    ...(changed === null ? ['Changes since the base are unavailable; listing available authored files.'] : []),
    ...(listed === null ? ['Worktree file inspection unavailable.'] : []), ...(discovery ? [discovery] : []), 'Gate files:',
    ...[...files].sort(([a], [b]) => a.localeCompare(b)).map(([file, { role }]) => `  ${role}: ${pathToFileURL(file).href}${fileInfo(root, file) ? '' : ' (unavailable)'}`), ...gateFiles];
  return { exitCode: 0, message: lines.join('\n') };
}

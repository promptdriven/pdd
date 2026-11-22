// Generated from prompts/cli/product.prompt.md.
// Layer 1 core: safe product document loading, runtime-line parsing, source-compatible evidence, and progress calculation (ZERO legacy workflow imports).
import { createHash } from 'node:crypto';
import { closeSync, constants, existsSync, fstatSync, lstatSync, openSync, readdirSync, readFileSync, readlinkSync, readSync, realpathSync } from 'node:fs';
import { readdir } from 'node:fs/promises';
import { basename, isAbsolute, join } from 'node:path';
import { gitFiles } from '../../shared/git-context.mjs';
import { causeText } from '../../shared/safe-read.mjs';
import { PROMPT_TESTS_LABEL, PROMPT_TESTS_WORDS } from '../../prompt-tests-words.mjs';
import { runtimePreflightSlice } from '../../runtime-seam.mjs';
import { computeProductWaves, parseProductDocuments } from './documents.mjs';
import { basePlan, command, issueLookup, portsFor, resolveBaseSha } from './github-state.mjs';
import { completedPr, pullRequests, validBase, validThrough } from './pr-matching.mjs';
import { invalid } from './markdown-utils.mjs';

const { captureSource } = runtimePreflightSlice();

const MAX_PRODUCT_FILE_BYTES = 2 * 1024 * 1024;
const MAX_SCAN_ENTRIES = 20000;
const SKIP_SCAN_DIRS = new Set(['.git', 'node_modules', 'fixtures', '.pdd', 'dist', 'build', 'coverage']);
const EXAMPLE_DIR_RE = /(?:^|\/)examples(?:\/|$)/i;
const DETAILS_OPEN = '<details><summary>Details for tools and audits</summary>';
const LABEL_START = new RegExp(`^${PROMPT_TESTS_WORDS}`);
const LINE_PATTERN = new RegExp(`${PROMPT_TESTS_WORDS}((?:\\s*\\([^)]*\\))*):\\s*(.*?)(?=\\n|\\s*(?:;|\\bReport\\b|https?:\\/\\/|${PROMPT_TESTS_WORDS}|$))`, 'gs');
const RESULT_PART = /^(?:(?:waiting|sent|passed|failed|refused|partial|not run)(?: \([^()]+\))?|\d+ (?:waiting|sent|passed|failed|refused|partial|not run)(?: \([^()]+\))?|\d+ tests could not run|\d+ criteria not checked|(?:✓|✗|no verdict|running|busy|unknown|UNKNOWN|queued|refused|not run)(?: (?:\d+ of \d+ criteri(?:a|on)|passed))?|\d+ of \d+ criteri(?:a|on)|passed|criteria details not reported|\d+\/\d+ checks|(?:\d+ AI calls?(?: \(\d+ for reruns\))?|\d+ for reruns)(?: \+ \d+ unknown)?|\d+ (?:refused|not run|unknown|queued|running|ahead|not yet settled|Stor(?:y|ies) skipped)|\d+ AI calls? so far|step \d+(?: of \d+)?(?: \([^)]*\))?)$/;

export const comparisonBases = Symbol('comparisonBases');

export function readSafeInRoot(rootDir, relPath, maxBytes = MAX_PRODUCT_FILE_BYTES) {
  const realRoot = realpathSync(rootDir);
  let rel = String(relPath ?? '').replace(/\\/g, '/');
  while (rel.startsWith('./')) rel = rel.slice(2);
  if (!rel || rel === '.' || isAbsolute(rel) || rel.split('/').some(seg => !seg || seg === '.' || seg === '..' || seg.toLowerCase() === '.git')) {
    throw Object.assign(Error(`Refused unsafe path: ${relPath}`), { code: 'EACCES' });
  }
  const segments = rel.split('/');
  let cur = realRoot, leafStat = null;
  for (let i = 0; i < segments.length; i++) {
    cur = join(cur, segments[i]);
    const st = lstatSync(cur);
    if (st.isSymbolicLink()) throw Object.assign(Error(`Refused symlink: ${rel}`), { code: 'ELOOP' });
    if (i < segments.length - 1 && !st.isDirectory()) throw Object.assign(Error(`Not a directory: ${rel}`), { code: 'ENOTDIR' });
    if (i === segments.length - 1) {
      if (!st.isFile()) throw Object.assign(Error(`Not a regular file: ${rel}`), { code: 'EINVAL' });
      if (st.size > maxBytes) throw Object.assign(Error(`File exceeds ${maxBytes} bytes: ${rel}`), { code: 'EFBIG' });
      leafStat = st;
    }
  }
  const fd = openSync(cur, constants.O_RDONLY | (constants.O_NOFOLLOW ?? 0));
  try {
    const fst = fstatSync(fd);
    if (!fst.isFile()) throw Object.assign(Error(`Not a regular file: ${rel}`), { code: 'EINVAL' });
    if (leafStat && (fst.dev !== leafStat.dev || fst.ino !== leafStat.ino)) {
      throw Object.assign(Error(`Path changed during open: ${rel}`), { code: 'EACCES' });
    }
    if (fst.size > maxBytes) throw Object.assign(Error(`File exceeds ${maxBytes} bytes: ${rel}`), { code: 'EFBIG' });
    const buf = Buffer.alloc(fst.size);
    let offset = 0;
    while (offset < buf.length) {
      const n = readSync(fd, buf, offset, buf.length - offset, offset);
      if (!n) break;
      offset += n;
    }
    return buf.subarray(0, offset).toString('utf8');
  } finally {
    closeSync(fd);
  }
}

export function collectSafePromptFiles(cwd, trackedFolders = []) {
  let realRoot;
  try {
    realRoot = realpathSync(cwd);
    if (!lstatSync(realRoot).isDirectory()) return null;
  } catch { return null; }
  const allowExamples = trackedFolders.some(folder => EXAMPLE_DIR_RE.test(folder));
  const files = [];
  let visited = 0;
  const walk = (absDir, relPrefix, depth) => {
    if (depth > 8 || files.length >= 2000 || visited >= MAX_SCAN_ENTRIES) return;
    let entries;
    try { entries = readdirSync(absDir, { withFileTypes: true }); }
    catch { return; }
    entries.sort((a, b) => a.name.localeCompare(b.name));
    for (const entry of entries) {
      if (files.length >= 2000 || visited >= MAX_SCAN_ENTRIES) return;
      visited++;
      if (entry.isSymbolicLink()) continue;
      const lowerName = entry.name.toLowerCase();
      if (SKIP_SCAN_DIRS.has(entry.name) || lowerName === '.git' || lowerName === 'fixtures') continue;
      if (!allowExamples && lowerName === 'examples') continue;
      if (entry.isFile() && !entry.name.endsWith('.prompt.md')) continue;
      const absChild = join(absDir, entry.name);
      const relChild = relPrefix ? `${relPrefix}/${entry.name}` : entry.name;
      let st;
      try { st = lstatSync(absChild); } catch { continue; }
      if (st.isSymbolicLink()) continue;
      if (st.isDirectory()) walk(absChild, relChild, depth + 1);
      else if (st.isFile() && entry.name.endsWith('.prompt.md')) {
        try { files.push({ path: relChild, content: readSafeInRoot(realRoot, relChild) }); } catch {}
      }
    }
  };
  walk(realRoot, '', 0);
  return files;
}

function resultParts(text) {
  const sentence = text.split(/\.\s/)[0].replace(/[.,]$/, ''), kept = [];
  for (const part of sentence.split(' · ')) {
    if (RESULT_PART.test(part)) { kept.push(part); continue; }
    if (part && kept.length > 1 && (kept.at(-1) === 'running' || /^sent(?: \([^()]+\))?$/.test(kept.at(-1)))) { kept.push(part); continue; }
    const words = part.split(' ');
    for (let size = words.length - 1; size > 0; size--) {
      if (RESULT_PART.test(words.slice(0, size).join(' '))) { kept.push(words.slice(0, size).join(' ')); break; }
    }
    break;
  }
  return kept.length ? kept.join(' · ') : sentence.split(' ')[0];
}

export function runtimeLines(text) {
  return [...String(text ?? '').matchAll(LINE_PATTERN)].map(match => {
    const groups = [...match[1].matchAll(/\(([^)]*)\)/g)].map(group => group[1].trim());
    const story = groups.find(group => group && group.toUpperCase() !== 'DRAFT' && group !== 'all Stories') ?? null;
    const result = resultParts(match[2].replace(/\s+/g, ' ').trim());
    return {
      story,
      draft: groups.some(group => group.toUpperCase() === 'DRAFT'),
      result,
      line: `${PROMPT_TESTS_LABEL}${match[1].replace(/\s+/g, ' ')}: ${result}`,
      pass: result.includes('✓') && !result.includes('✗'),
    };
  });
}

export function recordedRuntimeLines(text) {
  const lines = [], rows = String(text ?? '').split('\n');
  const open = rows.findIndex(row => /^<details\b/i.test(row));
  for (const line of open >= 0 && rows[open] === DETAILS_OPEN ? rows.slice(open + 1) : rows) {
    if (/^#{1,6}\s/.test(line) || /^<details\b/i.test(line)) break;
    if (line.startsWith('pdd result:') || LABEL_START.test(line)) lines.push(line);
  }
  return runtimeLines(lines.join('\n'));
}

const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');

export function sourceFingerprint(root) {
  try {
    const files = gitFiles(root).sort().map(path => {
      const full = join(root, path);
      let stat;
      try { stat = lstatSync(full); } catch (error) { if (error.code === 'ENOENT') return [path, 'missing']; throw error; }
      if (stat.isSymbolicLink()) return [path, 'link', readlinkSync(full)];
      if (!stat.isFile()) throw Error('Not a regular source file');
      return [path, stat.mode & 0o111, sha256(readFileSync(full))];
    });
    return sha256(JSON.stringify(files));
  } catch { return null; }
}

function matchesSourceRecord(record, root, fingerprint) {
  const source = record?.source;
  if (!source?.sha256 || !root) return false;
  if (source.kind === 'git-content-v1') return fingerprint !== null && fingerprint === source.sha256;
  if (source.kind === 'runtime-capture-v1') {
    const selection = {
      tests: source.tests,
      appMap: null,
      ...(Object.hasOwn(source, 'excludeFixtureProjects') ? { excludeFixtureProjects: source.excludeFixtureProjects } : {}),
    };
    try {
      const captured = captureSource(root, selection, { allowMissing: true });
      if (captured.sha256 !== source.sha256) return false;
      return !source.nativeSource
        || (Boolean(source.nativeSource.sha256) && captureSource(root, { ...selection, tests: source.nativeSource.tests }, { allowMissing: true }).sha256 === source.nativeSource.sha256);
    } catch { return false; }
  }
  return false;
}

export function storyEvidence(run, { comparisonRoot } = {}) {
  const batches = new Map();
  for (const result of [...(run?.pddHistory ?? []), ...Object.values(run?.done ?? {}).flatMap(rec => rec?.pddResults ?? [])]) {
    if (result?.kind === 'pdd test' && result.sourceSha256 && Array.isArray(result.tests) && !batches.has(result.batch)) {
      batches.set(result.batch, result);
    }
  }
  const ownRecords = [...batches.values()].map(result => ({
    at: result.at,
    summary: (result.stories?.length ? result.stories : [result.summary]).join('\n'),
    source: {
      kind: 'runtime-capture-v1',
      sha256: result.sourceSha256,
      tests: result.sourceTests ?? result.tests,
      ...(Object.hasOwn(result, 'excludeFixtureProjects') ? { excludeFixtureProjects: result.excludeFixtureProjects } : {}),
      ...(result.nativeSource ? { nativeSource: result.nativeSource } : {}),
    },
  }));
  const records = [...ownRecords, ...(run?.evidence ?? [])]
    .filter(record => runtimeLines(record.summary).length && record?.association?.stage !== 'before')
    .sort((a, b) => (a.at ?? 0) - (b.at ?? 0));
  const root = comparisonRoot === undefined ? run?.root : comparisonRoot;
  const fingerprint = root === null || !root ? null : sourceFingerprint(root);
  const current = new Map(), older = new Map();
  for (const record of records) {
    const compatible = root !== null && matchesSourceRecord(record, root, fingerprint);
    const latest = [...new Map(runtimeLines(record.summary).filter(line => line.story).map(line => [line.story, line])).values()];
    for (const row of latest) {
      (compatible ? current : older).set(row.story, { story: row.story, pass: row.pass, current: compatible, result: row.result, at: record.at ?? 0 });
    }
  }
  return [...new Map([...older, ...current]).values()];
}

export async function documents({ cwd }, p) {
  let map, plan = '';
  const readDoc = async relPath => p._customReadFile ? p.readFile(join(cwd, relPath)) : readSafeInRoot(cwd, relPath);
  try { map = await readDoc('product/map.md'); }
  catch (error) {
    if (error?.code === 'ELOOP') invalid('product/map.md: cannot read the product map (symlinks are not allowed).');
    invalid('product/map.md: cannot read the product map.');
  }
  try { plan = await readDoc('product/plan.md'); }
  catch (error) {
    if (error?.code === 'ELOOP') invalid('product/plan.md: cannot read the plan (symlinks are not allowed).');
    if (error?.code !== 'ENOENT') invalid('product/plan.md: cannot read the plan.');
  }
  return { ...parseProductDocuments({ mapText: map, planText: plan }), mapText: map, planText: plan };
}

export async function readProduct(input, given = {}) {
  return (await documents(input, portsFor(given, { defaultStoryEvidence: storyEvidence }))).product;
}

export const storyMatches = (name, id) => {
  const token = basename(name).replace(/\.md$/, '');
  return token === id || token.startsWith(`${id}-`) || token.startsWith(`${id}.`);
};
const isStoryMarkdown = path => typeof path === 'string' && path.endsWith('.md') && !path.endsWith('.prompt.md');

async function collectLocalMarkdownFiles(dir, depth = 0, out = []) {
  if (depth > 4) return out;
  let entries;
  try { entries = await readdir(dir, { withFileTypes: true }); }
  catch { return out; }
  for (const entry of entries) {
    const full = join(dir, entry.name);
    if (entry.isDirectory()) await collectLocalMarkdownFiles(full, depth + 1, out);
    else if ((entry.isFile() || entry.isSymbolicLink()) && isStoryMarkdown(entry.name)) out.push(entry.name);
  }
  return out;
}

async function plannedStoryFilesPresent(p, { cwd, baseBranch, product, run }) {
  if (!Array.isArray(run.stories) || !run.stories.length) return false;
  const partFolder = product.parts.find(part => part.part === run.part)?.folder ?? 'user_stories/journeys';
  const sharedFolders = (run.sharedSurfaces ?? []).map(surface => product.parts.find(part => part.part === surface)?.folder).filter(Boolean);
  const folders = [...new Set([partFolder, ...sharedFolders, 'user_stories'].filter(f => typeof f === 'string' && f.trim()))];
  const found = [];
  if (typeof p.storyFiles === 'function') {
    const custom = await p.storyFiles({ cwd, baseBranch, run: run.run, folder: partFolder });
    if (Array.isArray(custom)) found.push(...custom.filter(isStoryMarkdown));
  }
  for (const rel of folders) await collectLocalMarkdownFiles(join(cwd, rel), 0, found);
  const allMatched = () => run.stories.every(id => found.some(file => storyMatches(file, id)));
  if (allMatched()) return true;
  if (typeof baseBranch === 'string' && baseBranch.trim() && existsSync(cwd)) {
    for (const ref of [`refs/remotes/origin/${baseBranch}`, `refs/heads/${baseBranch}`]) {
      try {
        const present = await command(p, cwd, 'git', ['rev-parse', '--verify', '--quiet', `${ref}^{commit}`], true);
        if (present === null) continue;
        const out = await command(p, cwd, 'git', ['ls-tree', '-r', '--name-only', ref, '--', ...folders], true);
        if (typeof out === 'string' && out.trim()) {
          for (const line of out.split(/\r?\n/)) if (isStoryMarkdown(line.trim())) found.push(line.trim());
          if (allMatched()) return true;
        }
      } catch {}
    }
  }
  return false;
}

export const warnings = product => product.runs
  .filter(run => run.stories.length > 12)
  .map(run => `Warning: ${run.run} has ${run.stories.length} Stories; aim for about 12 per run.`);

export function cycles(product) {
  const finished = new Set(), found = [];
  const byName = new Map(product.runs.map(run => [run.run, run]));
  for (const start of product.runs) {
    if (finished.has(start.run)) continue;
    const active = new Map(), path = [], stack = [{ name: start.run, next: 0 }];
    while (stack.length) {
      const frame = stack.at(-1);
      if (!active.has(frame.name)) { active.set(frame.name, path.length); path.push(frame.name); }
      const needs = byName.get(frame.name).needs.filter(need => need !== 'plan PR');
      if (frame.next >= needs.length) { active.delete(frame.name); finished.add(frame.name); path.pop(); stack.pop(); continue; }
      const next = needs[frame.next++];
      if (active.has(next)) found.push(`Needs form a cycle: ${[...path.slice(active.get(next)), next].join(' → ')}`);
      else if (!finished.has(next)) stack.push({ name: next, next: 0 });
    }
  }
  return [...new Set(found)];
}

export function counts(ids, details) {
  const uniqueIds = new Set(ids);
  let pass = 0, stale = 0;
  for (const id of uniqueIds) {
    const evidence = details.flatMap(detail => detail.evidence).filter(row => storyMatches(row.story, id)).sort((a, b) => (a.at ?? 0) - (b.at ?? 0));
    const current = evidence.filter(row => row.current).at(-1), reported = evidence.filter(row => row.remote).at(-1);
    const older = evidence.filter(row => !row.current && !row.remote).at(-1);
    if (current ? current.pass : reported?.pass) pass++;
    else if (!current && !reported && older?.pass) stale++;
  }
  return { total: uniqueIds.size, pass, stale, notRun: uniqueIds.size - pass - stale };
}

export function trimFolderSlashes(value) {
  let f = String(value ?? '').trim();
  while (f.startsWith('./')) f = f.slice(2);
  while (f.endsWith('/')) f = f.slice(0, -1);
  return f;
}

const cleanToken = value => String(value ?? '').trim().replace(/^`([^`]*)`$/, '$1').trim();

export function rulesForRun(product, planned) {
  if (!Array.isArray(product.rulesToCheck) || !product.rulesToCheck.length) return [];
  const runParts = new Set([planned.part, ...(planned.sharedSurfaces ?? [])].map(part => cleanToken(part).toLowerCase()).filter(Boolean));
  return product.rulesToCheck.filter(entry => {
    const owners = cleanToken(entry.owner).split(',').map(cleanToken).filter(Boolean);
    return owners.some(owner => {
      const lower = owner.toLowerCase();
      return lower === '*' || lower === 'all' || lower === 'shared' || runParts.has(lower);
    });
  });
}

export async function progress(input, given, target) {
  const explicitThrough = validThrough(input.through), explicitBase = validBase(input.base);
  const p = portsFor(given, { defaultStoryEvidence: storyEvidence });
  const docs = await documents(input, p), { product } = docs, cwd = input.cwd;
  const planBase = validBase(product.base);
  const completionTarget = explicitThrough ?? product.through ?? 'code';
  const localRuns = await p.listRuns({ cwd }), repo = await p.resolveRepository({ cwd });
  const parent = localRuns.find(run => run.workflow === 'product'), warning = cycles(product), views = new Map();
  const effectiveBase = explicitBase ?? planBase ?? parent?.baseBranch ?? repo.defaultBranch;
  const baseSha = typeof p.resolveBaseSha === 'function'
    ? await p.resolveBaseSha({ cwd, baseBranch: effectiveBase })
    : (!p._customExecFile && existsSync(join(cwd, '.git')) ? await resolveBaseSha(p, { cwd, baseBranch: effectiveBase }) : null);
  const planReady = product.runs.some(run => run.needs.includes('plan PR')) ? await basePlan(p, { cwd, baseBranch: effectiveBase }) : true;
  const lookup = await issueLookup(p, cwd, repo.repository, localRuns, warning);
  const targetBound = target ? await lookup.bound(target, true) : null;
  const plannedRuns = targetBound ? product.runs.filter(run => run.run === target) : product.runs;
  for (const run of plannedRuns) await lookup.bound(run.run);
  const details = [], savedReads = new Map();
  const savedFor = async (root, comparisonRoot) => {
    const key = JSON.stringify([root, comparisonRoot]);
    if (!savedReads.has(key)) savedReads.set(key, (async () => {
      try {
        const reply = await p.savedStoryEvidence({ root, comparisonRoot });
        if (!reply || !Array.isArray(reply.stories) || !Array.isArray(reply.warnings)) throw Error('Invalid saved Story evidence.');
        warning.push(...reply.warnings); return reply.stories;
      } catch (error) { warning.push(`Could not read saved checks: ${causeText(error.message)}`); return []; }
    })());
    return savedReads.get(key);
  };
  try {
    for (const run of plannedRuns) {
      const selected = await lookup.find(run.run, run.run === target), { issue = null, local = null, unverified = false } = selected ?? {};
      if (unverified) {
        const evidence = (await savedFor(cwd, cwd)).filter(row => run.stories.some(id => storyMatches(row.story, id)));
        details.push({ run, issue, local: null, prs: [], evidence, fromPr: null, done: false, unverified: true, reason: selected.reason });
        continue;
      }
      const { prs, hasMergedSameRepoPr } = issue
        ? await pullRequests(p, cwd, repo.repository, issue, local, run.run, warning)
        : { prs: [], hasMergedSameRepoPr: false };
      const done = prs.some(pr => pr.state === 'MERGED' && completedPr(pr, local, completionTarget, run.run, issue?.number));
      const latest = [...prs].filter(pr => recordedRuntimeLines(pr.body).some(row => row.story))
        .sort((a, b) => String(a.updatedAt ?? '').localeCompare(String(b.updatedAt ?? '')) || a.number - b.number).at(-1);
      let evidence, comparisonRoot = local?.root ?? cwd;
      if (done) {
        const baseBranch = local?.baseBranch ?? explicitBase ?? planBase ?? repo.defaultBranch;
        if (!views.has(baseBranch)) {
          const view = await p.openBaseSource({ cwd, baseBranch });
          if (!view || !(view.root === null || typeof view.root === 'string') || !(view.handle === null || typeof view.handle === 'string')) throw Error('Invalid base-source view.');
          views.set(baseBranch, view);
        }
        comparisonRoot = views.get(baseBranch).root;
        if (comparisonRoot === null) warning.push(`Warning: ${run.run}'s base source is unavailable; saved results are unverified.`);
      }
      if (local) evidence = await p.storyEvidence(local, ...(done ? [{ comparisonRoot }] : []));
      else evidence = latest ? recordedRuntimeLines(latest.body).filter(row => row.story).map(row => ({ ...row, current: false, remote: true, at: Date.parse(latest.updatedAt) || 0 })) : [];
      const saved = [...await savedFor(cwd, done ? comparisonRoot : cwd), ...(local?.root && local.root !== cwd ? await savedFor(local.root, comparisonRoot) : [])];
      evidence = [...evidence, ...saved.filter(row => run.stories.some(id => storyMatches(row.story, id)))];
      details.push({ run, issue, local, prs, hasMergedSameRepoPr, evidence, fromPr: !local && latest ? latest.number : null, done });
    }
  } finally {
    const errors = [];
    for (const view of views.values()) if (view.handle !== null) {
      try { await p.closeBaseSource({ handle: view.handle }); } catch (error) { errors.push(causeText(error.message)); }
    }
    if (errors.length) throw Error(`Could not release the base-source view: ${errors.join('; ')}`);
  }
  for (const detail of details) {
    detail.storyCounts = counts(detail.run.stories, details);
    const activeLocal = Boolean(detail.local && ['running', 'waiting'].includes(detail.local.state));
    const hasOpenPr = Array.isArray(detail.prs) && detail.prs.some(pr => pr.state === 'OPEN');
    const hasMergedPr = Boolean(detail.hasMergedSameRepoPr || (Array.isArray(detail.prs) && detail.prs.some(pr => pr.state === 'MERGED')));
    const isClosed = typeof detail.issue?.state === 'string' && detail.issue.state.toUpperCase() === 'CLOSED';
    const storiesIncomplete = detail.storyCounts.total === 0 || detail.storyCounts.pass < detail.storyCounts.total;
    let hasPlannedStories = false;
    if (!detail.unverified && !detail.done && !activeLocal && !hasOpenPr && !hasMergedPr && isClosed && storiesIncomplete) {
      hasPlannedStories = await plannedStoryFilesPresent(p, {
        cwd, baseBranch: detail.local?.baseBranch ?? effectiveBase, product, run: detail.run,
      });
    }
    detail.closedUnbuilt = !detail.unverified && !detail.done && !activeLocal && !hasOpenPr && !hasMergedPr && isClosed && storiesIncomplete && !hasPlannedStories;
  }
  const canStart = detail => !detail.unverified && (!detail.issue || detail.closedUnbuilt);
  const needsFor = run => run.needs.filter(need => need === 'plan PR' ? !planReady : targetBound ? false : !details.find(detail => detail.run.run === need)?.done);
  const ready = details.filter(detail => canStart(detail) && !needsFor(detail.run).length).map(detail => detail.run.run);
  const waves = computeProductWaves(product.runs);
  return { p, docs, product, details, ready, needsFor, localRuns, repo, lookup, baseBranch: effectiveBase, baseSha, waves, bases: [...views.keys()], warning: [...new Set(warning)] };
}

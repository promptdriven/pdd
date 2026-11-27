// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// Structural `pdd lint --diff [BASE]` checks: BASE..WORKTREE diff, conflict markers, shadow binaries, and harness/snapshot edits.
import { spawnSync } from 'node:child_process';
import { lstatSync, realpathSync } from 'node:fs';
import { join } from 'node:path';
import { isTestPromptPath } from '../../file-owner.mjs';
import { causeText } from '../../shared/safe-read.mjs';
import { formatTeachingDetail, readSafeUtf8, resolveDefaultBaseRef } from './diagnostics.mjs';

export { resolveDefaultBaseRef };

const DOC_OR_FIXTURE_PATH = /(?:^|\/)(?:docs?|fixtures?|__fixtures__)\/|\.md$/i;
const SNAPSHOT_PATH = /\.snap$|(?:^|\/)__snapshots__\//i;
const HARNESS_PATH = /(?:^|\/)(?:pdd\.json|rules\/lint\/[^/]+\.json|package\.json|vitest\.config\.[^/]+|jest\.config\.[^/]+|pytest\.ini|pyproject\.toml|conftest\.py|tox\.ini|setup\.cfg|\.github\/workflows\/[^/]+\.ya?ml)$/i;
const SHADOW_BIN_PATH_RE = /(?:^|\/)(?:node_modules\/\.bin|\.venv\/bin|venv\/bin)\/.+/;
export const SHADOW_RUNTIME_BINS = ['node', 'npm', 'python', 'python3', 'pytest', 'go', 'cargo', 'sh', 'bash'];

export function findConflictMarkers(source, filePath) {
  if (!source || DOC_OR_FIXTURE_PATH.test(filePath)) return [];
  const lines = source.split(/\r?\n/), hits = [];
  let inBlock = false;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (/^<{7}(?:\s|$)/.test(line)) { hits.push({ path: filePath, line: i + 1 }); inBlock = true; }
    else if (/^\|{7}(?:\s|$)/.test(line)) { if (!inBlock) hits.push({ path: filePath, line: i + 1 }); }
    else if (/^={7}$/.test(line)) { if (!inBlock) hits.push({ path: filePath, line: i + 1 }); }
    else if (/^>{7}(?:\s|$)/.test(line)) { if (!inBlock) hits.push({ path: filePath, line: i + 1 }); inBlock = false; }
  }
  return hits;
}

export function detectShadowBinaries(root, { touchedFiles = [], baseSha = null } = {}) {
  const hits = [];
  const seen = new Set();
  const addHit = (relPath, reason) => {
    if (!relPath || seen.has(relPath)) return;
    seen.add(relPath);
    hits.push({ path: relPath, reason });
  };

  for (const rel of touchedFiles) {
    if (SHADOW_BIN_PATH_RE.test(rel)) {
      addHit(rel, 'diff modifies or adds a shadow binary under node_modules/.bin/ or .venv/bin/ or venv/bin/');
    }
  }
  if (root && baseSha) {
    const diffBin = spawnSync('git', ['diff', '--name-only', '-z', baseSha, '--', 'node_modules/.bin', '.venv/bin', 'venv/bin'], {
      cwd: root, maxBuffer: 4 * 1024 * 1024, stdio: ['ignore', 'pipe', 'ignore'],
    });
    if (diffBin.status === 0 && diffBin.stdout) {
      for (const rel of diffBin.stdout.toString('utf8').split('\0').filter(Boolean)) {
        addHit(rel, 'git diff modifies or adds a shadow binary under node_modules/.bin/, .venv/bin/, or venv/bin/');
      }
    }
    const trackedVenvBin = spawnSync('git', ['ls-files', '-z', '--', '.venv/bin', 'venv/bin'], {
      cwd: root, maxBuffer: 4 * 1024 * 1024, stdio: ['ignore', 'pipe', 'ignore'],
    });
    if (trackedVenvBin.status === 0 && trackedVenvBin.stdout) {
      for (const rel of trackedVenvBin.stdout.toString('utf8').split('\0').filter(Boolean)) {
        addHit(rel, 'git-tracked virtualenv binary under .venv/bin/ or venv/bin/');
      }
    }
    const untrackedBin = spawnSync('git', ['ls-files', '--others', '--exclude-standard', '-z', '--', 'node_modules/.bin', '.venv/bin', 'venv/bin'], {
      cwd: root, maxBuffer: 4 * 1024 * 1024, stdio: ['ignore', 'pipe', 'ignore'],
    });
    if (untrackedBin.status === 0 && untrackedBin.stdout) {
      for (const rel of untrackedBin.stdout.toString('utf8').split('\0').filter(Boolean)) {
        addHit(rel, 'untracked shadow binary under node_modules/.bin/, .venv/bin/, or venv/bin/');
      }
    }
  }
  if (root) {
    for (const bin of SHADOW_RUNTIME_BINS) {
      const rel = `node_modules/.bin/${bin}`;
      try {
        const st = lstatSync(join(root, 'node_modules', '.bin', bin));
        if (st.isFile() || st.isSymbolicLink()) {
          addHit(rel, `core runtime binary "${bin}" exists inside node_modules/.bin/ and shadows PATH during test commands`);
        }
      } catch {
        // absent
      }
    }
  }
  return hits;
}

export function analyzeDiffEntries(entries = []) {
  const snapshotEdits = [], harnessEdits = [], errors = [];

  for (const entry of entries) {
    const newPath = entry.newPath || '', oldPath = entry.oldPath || '', activePath = newPath || oldPath;
    if (newPath && SHADOW_BIN_PATH_RE.test(newPath)) {
      const detail = formatTeachingDetail({
        invariant: `Shadow binary "${newPath}" under node_modules/.bin/ can intercept repository test commands`,
        fix: `Remove "${newPath}" so host toolchain binaries are not shadowed`,
        rerun: 'pdd lint --diff',
      });
      errors.push({ path: newPath, line: 1, code: 'diff-shadow-bin', formatted: `Error: diff gate: ${newPath}:1 [diff-shadow-bin] ${detail}` });
    }
    if (newPath && entry.after) {
      for (const hit of findConflictMarkers(entry.after, newPath)) {
        const detail = formatTeachingDetail({ invariant: `Unresolved merge conflict marker at ${hit.path}:${hit.line}`, fix: `Resolve the conflict block at ${hit.path}:${hit.line} and remove conflict markers`, rerun: 'pdd lint --diff' });
        errors.push({ path: hit.path, line: hit.line, code: 'diff-conflict-marker', formatted: `Error: diff gate: ${hit.path}:${hit.line} [diff-conflict-marker] ${detail}` });
      }
      if (isTestPromptPath(newPath)) {
        const detail = formatTeachingDetail({ invariant: `Misplaced test prompt "${newPath}" violates PDD ownership (prompts own production modules, not test files)`, fix: `Delete ${newPath} and keep test assertions in native test files`, rerun: 'pdd lint --diff' });
        errors.push({ path: newPath, line: 1, code: 'misplaced-test-prompt', formatted: `Error: diff gate: ${newPath}:1 [misplaced-test-prompt] ${detail}` });
      }
    }

    if (SNAPSHOT_PATH.test(activePath)) snapshotEdits.push(activePath);
    if (HARNESS_PATH.test(activePath)) {
      if (activePath.endsWith('package.json')) {
        let changed = entry.before !== entry.after;
        try { changed = (entry.before ? JSON.parse(entry.before)?.scripts?.test : undefined) !== (entry.after ? JSON.parse(entry.after)?.scripts?.test : undefined); } catch {}
        if (changed) harnessEdits.push(`${activePath} (scripts.test)`);
      } else harnessEdits.push(activePath);
    }
  }

  const advisories = [];
  if (snapshotEdits.length) advisories.push(`Diff spotlight: snapshot file(s) modified (${snapshotEdits.join(', ')})`);
  if (harnessEdits.length) advisories.push(`Diff spotlight: test harness / CI config edited (${harnessEdits.join(', ')})`);

  return {
    ok: errors.length === 0,
    errors,
    advisories,
    removedTests: [],
    movedTests: [],
    addedTests: [],
    newSkips: [],
    assertionDrops: [],
    tableDrops: [],
    snapshotEdits,
    harnessEdits,
    mockOnlyBoundaryTests: [],
  };
}

function baseUnavailableResult(baseRef, reason) {
  const detail = formatTeachingDetail({ invariant: reason, fix: 'Pass a valid local git ref via --diff <REF> or commit an initial base commit', rerun: 'pdd lint --diff' });
  return {
    ok: false, baseAvailable: false, baseRef: baseRef ?? null, baseSha: null, baseError: reason, touchedFiles: [], changedEntries: [], deletedPaths: [],
    errors: [{ path: '.', line: 1, code: 'diff-base-unavailable', formatted: `Error: diff gate: .:1 [diff-base-unavailable] ${detail}` }],
    advisories: [], removedTests: [], movedTests: [], addedTests: [], newSkips: [], assertionDrops: [], tableDrops: [], snapshotEdits: [], harnessEdits: [], mockOnlyBoundaryTests: [],
  };
}

export function runDiffSpotlight({ cwd, baseRef, filterPaths = null } = {}) {
  const realRoot = realpathSync(cwd);
  const resolvedBase = baseRef || resolveDefaultBaseRef(realRoot);
  if (!resolvedBase) return baseUnavailableResult(baseRef, 'Could not resolve a default base commit locally.');
  const revCheck = spawnSync('git', ['rev-parse', '--verify', `${resolvedBase}^{commit}`], { cwd: realRoot, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  if (revCheck.status !== 0 || !revCheck.stdout.trim()) {
    return baseUnavailableResult(resolvedBase, `Base ref "${resolvedBase}" could not be resolved locally.`);
  }
  const resolvedCommit = revCheck.stdout.trim();
  const mb = spawnSync('git', ['merge-base', 'HEAD', resolvedCommit], { cwd: realRoot, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  if (mb.status !== 0 || !mb.stdout.trim()) {
    return baseUnavailableResult(resolvedBase, `git merge-base between HEAD and "${resolvedBase}" failed: ${causeText(mb.stderr || 'no common ancestor')}`);
  }
  const baseSha = mb.stdout.trim();

  const diffRes = spawnSync('git', ['diff', '--no-ext-diff', '--no-textconv', '--name-status', '-z', '--find-renames', baseSha, '--'], { cwd: realRoot, maxBuffer: 32 * 1024 * 1024 });
  if (diffRes.status !== 0) {
    return baseUnavailableResult(resolvedBase, `git diff against base "${resolvedBase}" failed: ${causeText(diffRes.stderr?.toString('utf8') || 'unknown git diff error')}`);
  }
  const entries = [], seenPaths = new Set(), seenNewPaths = new Set();
  const fields = diffRes.stdout.toString('utf8').replace(/\0$/, '').split('\0').filter(Boolean);
  for (let i = 0; i < fields.length;) {
    const st = fields[i++], first = fields[i++], second = st.startsWith('R') || st.startsWith('C') ? fields[i++] : first;
    const oldPath = st === 'A' ? '' : first, newPath = st === 'D' ? '' : second;
    const before = oldPath && oldPath.endsWith('package.json')
      ? (spawnSync('git', ['show', `${baseSha}:${oldPath}`], { cwd: realRoot, encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 }).stdout ?? '')
      : '';
    const after = newPath ? (readSafeUtf8(realRoot, newPath) ?? '') : '';
    entries.push({ status: st, oldPath, newPath, before, after });
    if (newPath) { seenPaths.add(newPath); seenNewPaths.add(newPath); }
    if (oldPath) seenPaths.add(oldPath);
  }
  const untracked = spawnSync('git', ['ls-files', '--others', '--exclude-standard', '-z'], { cwd: realRoot, maxBuffer: 16 * 1024 * 1024 });
  if (untracked.status !== 0) {
    return baseUnavailableResult(resolvedBase, `git ls-files failed while collecting untracked files: ${causeText(untracked.stderr?.toString('utf8') || 'unknown error')}`);
  }
  for (const rel of untracked.stdout.toString('utf8').split('\0').filter(Boolean)) {
    if (seenNewPaths.has(rel)) continue;
    seenNewPaths.add(rel);
    seenPaths.add(rel);
    entries.push({ status: 'A', oldPath: '', newPath: rel, before: '', after: readSafeUtf8(realRoot, rel) ?? '' });
  }
  const filterSet = filterPaths ? new Set(filterPaths) : null;
  const scopedEntries = filterSet
    ? entries.filter(e => (e.newPath && filterSet.has(e.newPath)) || (e.oldPath && filterSet.has(e.oldPath)))
    : entries;
  const presentNewPaths = new Set(entries.map(e => e.newPath).filter(Boolean));
  const deletedPaths = [...new Set(
    entries
      .filter(e => e.oldPath && (e.status === 'D' || (e.status.startsWith('R') && e.oldPath !== e.newPath)) && !presentNewPaths.has(e.oldPath))
      .map(e => e.oldPath),
  )].sort();
  const changedEntries = entries.map(({ status, oldPath, newPath }) => ({ status, oldPath, newPath }));

  const analysis = analyzeDiffEntries(scopedEntries);
  for (const hit of detectShadowBinaries(realRoot, { touchedFiles: [...seenPaths], baseSha })) {
    if (!analysis.errors.some(e => e.code === 'diff-shadow-bin' && e.path === hit.path)) {
      const detail = formatTeachingDetail({
        invariant: `Shadow binary "${hit.path}" detected (${hit.reason})`,
        fix: `Remove "${hit.path}" so repository commands execute the authentic host toolchain`,
        rerun: 'pdd lint --diff',
      });
      analysis.errors.push({ path: hit.path, line: 1, code: 'diff-shadow-bin', formatted: `Error: diff gate: ${hit.path}:1 [diff-shadow-bin] ${detail}` });
      analysis.ok = false;
    }
  }
  const checkRes = spawnSync('git', ['diff', '--check', baseSha, '--'], { cwd: realRoot, encoding: 'utf8', maxBuffer: 4 * 1024 * 1024 });
  if (checkRes.status === 2 && checkRes.stdout) {
    for (const line of checkRes.stdout.split(/\r?\n/)) {
      const cm = /^([^:]+):(\d+):\s*leftover conflict marker/i.exec(line);
      if (!cm || DOC_OR_FIXTURE_PATH.test(cm[1])) continue;
      const file = cm[1], lineNo = Number(cm[2]) || 1;
      if (filterSet && !filterSet.has(file)) continue;
      if (!analysis.errors.some(e => e.code === 'diff-conflict-marker' && e.path === file && e.line === lineNo)) {
        const detail = formatTeachingDetail({ invariant: `Leftover conflict marker reported by git diff --check at ${file}:${lineNo}`, fix: `Resolve the conflict marker at ${file}:${lineNo}`, rerun: 'pdd lint --diff' });
        analysis.errors.push({ path: file, line: lineNo, code: 'diff-conflict-marker', formatted: `Error: diff gate: ${file}:${lineNo} [diff-conflict-marker] ${detail}` });
        analysis.ok = false;
      }
    }
  }
  return { ...analysis, baseAvailable: true, baseRef: resolvedBase, baseSha, touchedFiles: [...seenPaths].sort(), changedEntries, deletedPaths };
}

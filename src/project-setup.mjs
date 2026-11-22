// Prompt: prompts/cli/project-setup.prompt.md
import { existsSync, lstatSync, readFileSync, realpathSync, renameSync, statSync, unlinkSync, writeFileSync } from 'node:fs';
import { randomBytes } from 'node:crypto';
import { isAbsolute, join, relative, resolve } from 'node:path';
import { resolveRepoRoot } from './shared/git-context.mjs';

const START = '<!-- pdd:start -->';
const END = '<!-- pdd:end -->';

export const PDD_BLOCK = [
  START,
  'This project uses PDD — edit the owning `.prompt.md` before changing owned code, and verify with `pdd status`, `pdd lint`, and `pdd test`.',
  'Invoke `/pdd` in Claude Code or `$pdd` in Codex (first time? `npm i -g @promptdriven/pdd && pdd setup`).',
  END,
].join('\n');

function readJsonQuiet(file) {
  try {
    const parsed = JSON.parse(readFileSync(file, 'utf8'));
    return parsed && typeof parsed === 'object' && !Array.isArray(parsed) ? parsed : null;
  } catch {
    return null;
  }
}

export function detectProjectStack(root) {
  if (typeof root !== 'string' || !root) return { language: null, testCommand: null };
  const has = name => existsSync(join(root, name));

  if (has('package.json')) {
    const pkg = readJsonQuiet(join(root, 'package.json'));
    const rawTest = typeof pkg?.scripts?.test === 'string' ? pkg.scripts.test.trim() : '';
    const hasRealTest = Boolean(rawTest && !/no test specified/i.test(rawTest));
    const pm = has('pnpm-lock.yaml') ? 'pnpm'
      : has('yarn.lock') ? 'yarn'
      : (has('bun.lock') || has('bun.lockb')) ? 'bun'
      : 'npm';
    const language = has('tsconfig.json') ? 'typescript' : 'javascript';
    return { language, testCommand: hasRealTest ? `${pm} test` : null };
  }
  if (has('pyproject.toml') || has('pytest.ini') || has('setup.py')) {
    return { language: 'python', testCommand: has('uv.lock') ? 'uv run pytest' : 'pytest' };
  }
  if (has('go.mod')) return { language: 'go', testCommand: 'go test ./...' };
  if (has('Cargo.toml')) return { language: 'rust', testCommand: 'cargo test' };
  if (has('Gemfile')) return { language: 'ruby', testCommand: has('.rspec') ? 'bundle exec rspec' : 'bundle exec rake test' };
  if (has('pom.xml')) return { language: 'java', testCommand: 'mvn test' };
  if (has('build.gradle') || has('build.gradle.kts')) {
    return { language: 'java', testCommand: has('gradlew') ? './gradlew test' : 'gradle test' };
  }
  return { language: null, testCommand: null };
}

function resolveWritableTarget(file, root) {
  let st;
  try {
    st = lstatSync(file);
  } catch (error) {
    if (error.code === 'ENOENT') return { target: file, stat: null };
    throw error;
  }
  if (st.isSymbolicLink()) {
    let resolved, targetStat, realRoot;
    try {
      realRoot = realpathSync(root);
      resolved = realpathSync(file);
      targetStat = statSync(resolved);
    } catch {
      resolved = null;
    }
    const rel = resolved ? relative(realRoot, resolved) : '..';
    if (resolved && targetStat?.isFile() && rel && !rel.startsWith('..') && !isAbsolute(rel)) {
      // Allow common in-repo symlinks such as `CLAUDE.md -> AGENTS.md` and update the in-repo target cleanly.
      return { target: resolved, stat: targetStat };
    }
    throw new Error(
      `${file}: cannot write PDD block because the target is a symbolic link pointing outside the repository (or broken).\n`
      + '  Invariant: pdd init only updates regular CLAUDE.md / AGENTS.md files inside the repository.\n'
      + `  Fix: Replace "${file}" with a regular file (or in-repo symlink) or add the 4-line PDD block manually.\n`
      + '  Rerun: pdd init',
    );
  }
  if (!st.isFile()) {
    throw new Error(
      `${file}: cannot write PDD block because the target is not a regular file.\n`
      + '  Invariant: pdd init only updates regular CLAUDE.md / AGENTS.md files inside the repository.\n'
      + `  Fix: Replace "${file}" with a regular file or add the 4-line PDD block manually.\n`
      + '  Rerun: pdd init',
    );
  }
  return { target: file, stat: st };
}

function writeAtomicRegular(file, content, mode = 0o644) {
  const tmp = `${file}.pdd-tmp-${process.pid}-${randomBytes(6).toString('hex')}`;
  try {
    writeFileSync(tmp, content, { encoding: 'utf8', mode });
    renameSync(tmp, file);
  } catch (error) {
    try { unlinkSync(tmp); } catch {}
    throw error;
  }
}

export function setupProject({ cwd }) {
  const claude = join(cwd, 'CLAUDE.md');
  let claudePresent = false;
  try { lstatSync(claude); claudePresent = true; } catch {}
  const chosen = claudePresent ? claude : join(cwd, 'AGENTS.md');
  const { target: file, stat: existingStat } = resolveWritableTarget(chosen, resolve(cwd));
  const old = existingStat ? readFileSync(file, 'utf8') : null;
  const eol = old?.includes('\r\n') ? '\r\n' : '\n';
  const wanted = eol === '\r\n' ? PDD_BLOCK.replaceAll('\n', '\r\n') : PDD_BLOCK;

  let text;
  if (old === null) {
    text = `${wanted}${eol}`;
  } else {
    const normalizedLines = old.split(/\r?\n/);
    const trailingEmpty = old.endsWith('\n') || old.endsWith('\r');
    const lines = trailingEmpty ? normalizedLines.slice(0, -1) : normalizedLines;
    const startIndexes = [];
    const endIndexes = [];
    for (let i = 0; i < lines.length; i++) {
      if (lines[i] === START) startIndexes.push(i);
      if (lines[i] === END) endIndexes.push(i);
    }
    if (startIndexes.length === 0 && endIndexes.length === 0) {
      const prefix = old.endsWith('\n') || old.endsWith('\r') ? old : `${old}${eol}`;
      text = `${prefix}${eol}${wanted}${eol}`;
    } else if (startIndexes.length === 1 && endIndexes.length === 1 && startIndexes[0] < endIndexes[0]) {
      const replaced = [
        ...lines.slice(0, startIndexes[0]),
        ...PDD_BLOCK.split('\n'),
        ...lines.slice(endIndexes[0] + 1),
      ];
      text = `${replaced.join(eol)}${eol}`;
    } else {
      throw new Error(
        `${file}: needs exactly one ${START} line followed by one ${END} line.\n`
        + '  Invariant: existing PDD marker blocks must be balanced so surrounding instructions are never corrupted.\n'
        + `  Fix: Repair or remove the unmatched ${START} / ${END} marker in ${file}.\n`
        + '  Rerun: pdd init',
      );
    }
  }

  if (text === old) return { file, changed: false };
  const mode = existingStat && (existingStat.mode & 0o777) ? (existingStat.mode & 0o777) : 0o644;
  writeAtomicRegular(file, text, mode);
  return { file, changed: true };
}

export async function initProject({ cwd = process.cwd(), packageRoot } = {}, ports = {}) {
  const repoRoot = await resolveRepoRoot(cwd, ports);
  const root = repoRoot ?? cwd;
  const { file, changed } = setupProject({ cwd: root, packageRoot });
  const { language, testCommand } = detectProjectStack(root);
  return { root, inGit: Boolean(repoRoot), file, changed, language, testCommand };
}

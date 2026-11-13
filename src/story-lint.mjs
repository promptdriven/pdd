// Generated from prompts/cli/story-lint.prompt.md (sha256: 570e724b7d9776a70d00d7cff8f72b286437922c472e646f1e1e792b7d4df369).
import { isAbsolute } from 'node:path';

const IMPL_DIR = /(?:^|[\s"'(\[`])((?:src|lib|dist|build|internal|pkg|cmd|__tests__)\/[A-Za-z0-9_./-]+|prompts\/(?:cli|tests?|__tests__)\/[A-Za-z0-9_./-]+)/;
const RUNNER_CMD = /(["`])\s*(?:node|npm|pnpm|yarn|pytest|cargo|go)\s+[^"`\r\n]+\1/g;
const CODE_EXT = /\b((?:[A-Za-z0-9_.-]+\/)*[A-Za-z0-9_.-]+\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|java|kt|rb|php|cs|cpp|cc|c|hpp|h|swift))\b/;
const CODE_SYNTAX = /\b(?:export\s+(?:async\s+)?(?:function|const|class|default)\b|async\s+function\b|function\s+[A-Za-z_$][\w$]*\s*\()|\s=>\s/;
const CALL_SIG = /\b(?:[a-z]+[A-Z][\w$]*\s*\([^)\r\n]*\)|[a-z]+_[a-z0-9_]*\s*\(\s*[A-Za-z_$][\w$]*\s*,[^)\r\n]*\))/;
const CODE_TERMS = /\b(?:AST|Abstract Syntax Tree|bit-flips?|bit-flipping|bitmasks?|0x[0-9a-fA-F]{2,}|Uint8Array|Int32Array|Float64Array|ArrayBuffer|Buffer\.from|RegExp|process\.exit|child_process|fs\.(?:read|write|lstat|stat|open|exists)\w*|TypeError|ReferenceError|SyntaxError)\b/;
const RAW_DIGEST = /\b(?:sha256:\s*[a-f0-9]{7,}|[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}|[a-f0-9]{64}|[a-f0-9]{40})\b/i;
const GENERIC_ROLE = /\bAs (?:a|an|the) (?:(?:end[- ])?user|system)\b/i;
const VAGUE_CRITERION = /\b(?:works?\s+correctly|handled?\s+gracefully|properly\s+handled|as\s+expected|seamlessly|gracefully|correctly)\b/i;

const canonicalStoryPath = value => typeof value === 'string' && value.trim().length > 0 && value.length <= 1000 && !isAbsolute(value)
  && !/[\\\x00-\x1f\x7f]/.test(value) && !value.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');

export function isLintableStoryPath(path) {
  if (!canonicalStoryPath(path) || !/\.md$/i.test(path)) return false;
  const parts = path.split('/'), base = parts.at(-1).toLowerCase();
  return base !== 'plan.md' && base !== 'readme.md' && parts.slice(0, -1).includes('user_stories');
}

const trimExcerpt = line => {
  const trimmed = line.trim();
  return trimmed.length <= 140 ? trimmed : `${trimmed.slice(0, 139)}…`;
};

function findImplPath(line) {
  const dir = IMPL_DIR.exec(line);
  if (dir) return dir[1].replace(/[.,;:!?)]+$/, '');
  const ext = CODE_EXT.exec(line.replace(RUNNER_CMD, ' '));
  return ext ? ext[1] : null;
}

function findCodeInternals(line) {
  const match = CODE_SYNTAX.exec(line) ?? CALL_SIG.exec(line) ?? CODE_TERMS.exec(line);
  return match ? match[0].trim() : null;
}

export function lintStory(text, { path = 'user_stories/story.md' } = {}) {
  const cleaned = String(text ?? '').replace(/<!--[\s\S]*?-->/g, comment => comment.replace(/[^\r\n]/g, ' '));
  const rawLines = String(text ?? '').split(/\r?\n/), lines = cleaned.split(/\r?\n/);
  const problems = [];
  let fence = null, section = 'intro';

  const checkLine = (line, rawLine, lineNo, activeSection) => {
    if (!line.trim()) return;
    const excerpt = trimExcerpt(rawLine);
    const push = (code, message) => problems.push({ path, line: lineNo, code, message, excerpt });

    const implPath = findImplPath(line);
    if (implPath) push('story-implementation-path',
      `Implementation path "${implPath}" belongs in module prompts or tests, not the Story. Describe what the person runs or sees instead of naming code files.`);

    const internal = findCodeInternals(line);
    if (internal) push('story-code-internals',
      `Low-level code detail "${internal}" leaks implementation internals into the Story. State observable user inputs, outputs or exit behavior instead (put formal invariants under "## Rules to check").`);

    const digest = RAW_DIGEST.exec(line)?.[0];
    if (digest) push('story-raw-digest',
      `Raw hash or UUID "${digest}" pins internal machine state in the Story. Describe the visible behavior or rule without hard-coding digests, commit hashes or UUIDs.`);

    const role = GENERIC_ROLE.exec(line)?.[0];
    if (role) push('story-generic-role',
      `Generic role "${role}" hides who uses the behavior. Name a real person or role (for example "As a customer", "As a shop owner" or "As a developer who runs pdd test").`);

    if (activeSection === 'criteria') {
      const vague = VAGUE_CRITERION.exec(line)?.[0];
      if (vague) push('story-vague-criterion',
        `Vague phrase "${vague}" cannot be checked directly. State the exact output, message, state change or exit code that shows it worked.`);
    }
  };

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i], rawLine = rawLines[i] ?? line;
    const fenceMatch = line.match(/^\s*(`{3,}|~{3,})/);
    if (fenceMatch) {
      const token = fenceMatch[1];
      if (!fence) { fence = { char: token[0], len: token.length }; continue; }
      if (token[0] === fence.char && token.length >= fence.len && /^\s*(?:`{3,}|~{3,})\s*$/.test(line)) { fence = null; continue; }
    }
    if (fence) continue;
    if (/^#\s+/.test(line)) {
      checkLine(line, rawLine, i + 1, 'title');
      section = 'intro';
      continue;
    }
    if (/^##\s+/.test(line)) {
      const heading = line.replace(/^##\s+/, '').trim().toLowerCase();
      if (heading === 'acceptance criteria') section = 'criteria';
      else if (heading === 'what must not change' || heading === 'must not change') section = 'must-not-change';
      else section = 'other';
      continue;
    }
    if (section === 'intro' || section === 'criteria' || section === 'must-not-change') checkLine(line, rawLine, i + 1, section);
  }
  return { ok: problems.length === 0, path, problems };
}

export function lintStories(entries = []) {
  const problems = [];
  for (const entry of entries) {
    if (!entry || !isLintableStoryPath(entry.path)) continue;
    problems.push(...lintStory(entry.text, { path: entry.path }).problems);
  }
  return { ok: problems.length === 0, problems };
}

export function formatStoryLint(result) {
  if (!result || result.ok || !result.problems?.length) return '';
  const rows = ['Story quality check failed:'];
  for (const { path, line, code, message, excerpt } of result.problems) {
    rows.push(`  ${path}:${line} [${code}] ${message}`);
    if (excerpt) rows.push(`    > ${excerpt}`);
  }
  rows.push('Rewrite the Story in user-observable terms: name who uses the behavior, what they do and what they see; keep file paths, function signatures, hashes and bit-level internals in module prompts or tests.');
  return rows.join('\n');
}

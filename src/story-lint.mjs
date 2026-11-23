// Prompt: prompts/cli/story-lint.prompt.md
import { isAbsolute } from 'node:path';

const IMPL_DIR = /(?:^|[\s"'(\[`])((?:src|lib|internal|pkg|cmd|__tests__)\/[A-Za-z0-9_./-]+|(?:dist|build)\/[A-Za-z0-9_./-]*[./][A-Za-z0-9_./-]+|prompts\/(?:cli|tests?|__tests__)\/[A-Za-z0-9_./-]+)/;
const RUNNER_CMD = /(["`])\s*(?:node|npm|pnpm|yarn|pytest|cargo|go)\s+[^"`\r\n]+\1/g;
const URL_SPAN = /https?:\/\/\S+/gi;
const CODE_EXT = /(?:^|[\s"'(\[`])((?:[A-Za-z0-9_.-]+\/)+[A-Za-z0-9_.-]+\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|java|kt|rb|php|cs|cpp|cc|c|hpp|h|swift)|[A-Za-z0-9_.-]+\.(?:mjs|cjs|ts|tsx|jsx)|(?:test_[A-Za-z0-9_.-]+|[A-Za-z0-9_.-]+(?:_test|\.(?:test|spec)))\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|java|kt|rb|php|cs|cpp|cc|c|hpp|h|swift))\b/;
const CODE_SYNTAX = /\b(?:export\s+(?:async\s+)?(?:function|const|class|default)\b|async\s+function\b|function\s+[A-Za-z_$][\w$]*\s*\()|\s=>\s/;
const CALL_SIG = /\b(?:[a-z]+[A-Z][\w$]*\s*\([^)\r\n]*\)|[a-z]+_[a-z0-9_]*\s*\(\s*[A-Za-z_$][\w$]*\s*,[^)\r\n]*\))/;
const CODE_TERMS = /\b(?:AST|Abstract Syntax Tree|bit-flips?|bit-flipping|bitmasks?|0x[0-9a-fA-F]{2,}|Uint8Array|Int32Array|Float64Array|ArrayBuffer|Buffer\.from|RegExp|process\.exit|child_process|fs\.(?:read|write|lstat|stat|open|exists)\w*|TypeError|ReferenceError|SyntaxError)\b/;
const RAW_DIGEST = /\b(?:sha256:\s*[a-f0-9]{7,}|[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}|[a-f0-9]{64}|[a-f0-9]{40})\b/i;
const GENERIC_ROLE = /\bAs\s+(?:a|an|the)\s+(?:(?:end[- ])?user|system|caller)(?=\s*(?:[,;.]|$|\bI\s+(?:want|can|need)\b))/i;
const UI_LITERAL = /"[^"\r\n]+"|(?<![A-Za-z0-9])'[^'\r\n]+'(?![A-Za-z0-9])/g;
const GROUNDED_OUTCOME = /\b(?:exits?\s+with\s+(?:code|status)\s+\d+|HTTP\s+\d{3}|status\s+(?:code\s+)?\d+|\d+\s+times?|saves\s+nothing)\b/i;
const VAGUE_CRITERION = /\b(?:works?\s+correctly|handled?\s+gracefully|properly\s+handled|as\s+expected|seamlessly|gracefully|properly|correctly)\b/i;
const NUMBERED_ITEM = /^\s*\d+[.)]\s+\S/;
const BULLET_ITEM = /^ {0,3}[-*+]\s+\S/;

const canonicalStoryPath = value => typeof value === 'string' && value.trim().length > 0 && value.length <= 1000 && !isAbsolute(value)
  && !/[\\\x00-\x1f\x7f]/.test(value) && !value.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');

export function isLintableStoryPath(path) {
  if (!canonicalStoryPath(path) || !/\.md$/i.test(path)) return false;
  const parts = path.split('/'), base = parts.at(-1).toLowerCase();
  if (base === 'plan.md' || base === 'readme.md') return false;
  const dirs = parts.slice(0, -1);
  if (dirs.includes('user_stories')) return true;
  for (let i = 0; i < dirs.length - 1; i++) {
    if (dirs[i] === 'pdd' && dirs[i + 1] === 'stories') return true;
  }
  return false;
}

const trimExcerpt = line => {
  const trimmed = line.trim();
  return trimmed.length <= 140 ? trimmed : `${trimmed.slice(0, 139)}…`;
};

function findImplPath(line) {
  const dir = IMPL_DIR.exec(line);
  if (dir) return dir[1].replace(/[.,;:!?)]+$/, '');
  const ext = CODE_EXT.exec(line.replace(RUNNER_CMD, ' ').replace(URL_SPAN, ' '));
  return ext ? ext[1] : null;
}

function findCodeInternals(line) {
  const match = CODE_SYNTAX.exec(line) ?? CALL_SIG.exec(line) ?? CODE_TERMS.exec(line);
  return match ? match[0].trim() : null;
}

function findVagueCriterion(line) {
  const withoutCmds = line.replace(RUNNER_CMD, ' ');
  const unquoted = withoutCmds.replace(UI_LITERAL, ' ');
  const match = VAGUE_CRITERION.exec(unquoted);
  if (!match) return null;
  UI_LITERAL.lastIndex = 0;
  if (UI_LITERAL.test(withoutCmds) || GROUNDED_OUTCOME.test(unquoted)) return null;
  return match[0];
}

export function lintStory(text, { path = 'user_stories/story.md', criteriaHygiene = true } = {}) {
  const cleaned = String(text ?? '').replace(/<!--[\s\S]*?-->/g, comment => comment.replace(/[^\r\n]/g, ' '));
  const rawLines = String(text ?? '').split(/\r?\n/), lines = cleaned.split(/\r?\n/);
  const problems = [];
  const numberedCriteria = [], bulletCriteria = [];
  let fence = null, section = 'intro', criteriaHeadingLine = null, criteriaHeadingRaw = '';

  const checkLine = (line, rawLine, lineNo, activeSection) => {
    if (!line.trim()) return;
    const excerpt = trimExcerpt(rawLine);
    const push = (code, message, fix) => problems.push({ path, line: lineNo, code, message, fix, excerpt });

    const implPath = findImplPath(line);
    if (implPath) push('story-implementation-path',
      `Implementation path "${implPath}" belongs in module prompts or tests, not the Story. Describe what the person runs or sees instead of naming code files.`,
      `Remove "${implPath}" from ${path}:${lineNo} and describe the visible command, screen, or outcome instead`);

    const internal = findCodeInternals(line);
    if (internal) push('story-code-internals',
      `Low-level code detail "${internal}" leaks implementation internals into the Story. State observable user inputs, outputs or exit behavior instead (put formal invariants under "## Rules to check").`,
      `Replace "${internal}" at ${path}:${lineNo} with observable inputs, outputs, or exit behavior (move technical invariants to .prompt.md)`);

    const digest = RAW_DIGEST.exec(line)?.[0];
    if (digest) push('story-raw-digest',
      `Raw hash or UUID "${digest}" pins internal machine state in the Story. Describe the visible behavior or rule without hard-coding digests, commit hashes or UUIDs.`,
      `Remove raw digest/UUID "${digest}" at ${path}:${lineNo} and state the user-visible rule instead`);

    const role = GENERIC_ROLE.exec(line)?.[0];
    if (role) push('story-generic-role',
      `Generic role "${role}" hides who uses the behavior. Name a real person or role (for example "As a customer", "As a shop owner" or "As a developer who runs pdd test").`,
      `Replace "${role}" at ${path}:${lineNo} with a specific actor role (for example "As a customer" or "As a developer")`);

    if (activeSection === 'criteria') {
      const vague = findVagueCriterion(line);
      if (vague) push('story-vague-criterion',
        `Vague phrase "${vague}" cannot be checked directly. State the exact output, message, state change or exit code that shows it worked.`,
        `Replace "${vague}" at ${path}:${lineNo} with a concrete output, state change, or exit code`);
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
      if (heading === 'acceptance criteria' || heading === 'acceptance') {
        section = 'criteria';
        if (criteriaHeadingLine === null) { criteriaHeadingLine = i + 1; criteriaHeadingRaw = rawLine; }
      } else if (heading === 'what must not change' || heading === 'must not change') section = 'must-not-change';
      else section = 'other';
      continue;
    }
    if (section === 'criteria') {
      if (NUMBERED_ITEM.test(line)) numberedCriteria.push({ line: i + 1, raw: rawLine });
      else if (BULLET_ITEM.test(line)) bulletCriteria.push({ line: i + 1, raw: rawLine });
    }
    if (section === 'intro' || section === 'criteria' || section === 'must-not-change') checkLine(line, rawLine, i + 1, section);
  }

  if (criteriaHygiene) {
    const items = numberedCriteria.length > 0 ? numberedCriteria : bulletCriteria;
    if (criteriaHeadingLine === null) {
      const firstIdx = rawLines.findIndex(row => row.trim().length > 0);
      problems.push({
        path,
        line: firstIdx >= 0 ? firstIdx + 1 : 1,
        code: 'story-missing-criteria',
        message: 'Story is missing an "## Acceptance criteria" section. Add "## Acceptance criteria" with 1 to 6 concrete, user-observable acceptance items.',
        fix: `Add a "## Acceptance criteria" section to ${path} with 1 to 6 numbered, user-observable checks`,
        excerpt: trimExcerpt(rawLines[firstIdx >= 0 ? firstIdx : 0] ?? ''),
      });
    } else if (items.length === 0) {
      problems.push({
        path,
        line: criteriaHeadingLine,
        code: 'story-missing-criteria',
        message: '"## Acceptance criteria" lists 0 acceptance items. Add 1 to 6 concrete, user-observable numbered or bulleted acceptance items.',
        fix: `Add 1 to 6 numbered acceptance criteria under "## Acceptance criteria" in ${path}`,
        excerpt: trimExcerpt(criteriaHeadingRaw),
      });
    } else if (items.length > 6) {
      const seventh = items[6];
      problems.push({
        path,
        line: seventh.line,
        code: 'story-bloated-criteria',
        message: `"## Acceptance criteria" lists ${items.length} items (recommended at most 6). Keep 1 Story per cohesive user loop and move technical invariants to .prompt.md "## Domain decisions" or "## Rules to check".`,
        fix: `Trim ${path} to at most 6 criteria by splitting separate user loops or moving technical edge cases to .prompt.md "## Domain decisions"`,
        excerpt: trimExcerpt(seventh.raw),
      });
    }
    let lineCount = rawLines.length;
    while (lineCount > 0 && rawLines[lineCount - 1].trim() === '') lineCount--;
    if (lineCount > 35) {
      problems.push({
        path,
        line: 36,
        code: 'story-too-long',
        message: `Story is ${lineCount} lines long (recommended at most 35 lines). Move technical invariants, schemas or edge-case matrices to .prompt.md "## Domain decisions" or test JSON fixtures.`,
        fix: `Shorten ${path} to <= 35 lines by moving schemas, fixtures, and technical edge cases into the owning .prompt.md or scenario JSON`,
        excerpt: trimExcerpt(rawLines[35] ?? ''),
      });
    }
  }

  problems.sort((a, b) => a.line - b.line);
  return { ok: problems.length === 0, path, problems };
}

export function lintStories(entries = [], { criteriaHygiene = false } = {}) {
  const problems = [];
  for (const entry of entries) {
    if (!entry || !isLintableStoryPath(entry.path)) continue;
    problems.push(...lintStory(entry.text, { path: entry.path, criteriaHygiene }).problems);
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

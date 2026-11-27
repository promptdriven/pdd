// Prompt: prompts/cli/story-lint.prompt.md
import { isAbsolute } from 'node:path';

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

export function lintStory(text, { path = 'user_stories/story.md', criteriaHygiene = true } = {}) {
  const cleaned = String(text ?? '').replace(/<!--[\s\S]*?-->/g, comment => comment.replace(/[^\r\n]/g, ' '));
  const rawLines = String(text ?? '').split(/\r?\n/), lines = cleaned.split(/\r?\n/);
  const problems = [];
  const numberedCriteria = [], bulletCriteria = [];
  let fence = null, section = 'intro', criteriaHeadingLine = null, criteriaHeadingRaw = '';

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i], rawLine = rawLines[i] ?? line;
    const fenceMatch = line.match(/^\s*(`{3,}|~{3,})(.*)$/);
    if (fenceMatch) {
      const token = fenceMatch[1], rest = fenceMatch[2];
      if (!fence) {
        if (!(token[0] === '`' && rest.includes('`'))) {
          fence = { char: token[0], len: token.length };
          continue;
        }
      } else if (token[0] === fence.char && token.length >= fence.len && /^\s*$/.test(rest)) {
        fence = null;
        continue;
      }
    }
    if (fence) continue;
    if (/^#\s+/.test(line)) { section = 'intro'; continue; }
    if (/^##\s+/.test(line)) {
      const heading = line.replace(/^##\s+/, '').trim().toLowerCase();
      if (heading === 'acceptance criteria' || heading === 'acceptance') {
        section = 'criteria';
        if (criteriaHeadingLine === null) { criteriaHeadingLine = i + 1; criteriaHeadingRaw = rawLine; }
      } else {
        section = 'other';
      }
      continue;
    }
    if (section === 'criteria') {
      if (NUMBERED_ITEM.test(line)) numberedCriteria.push({ line: i + 1, raw: rawLine });
      else if (BULLET_ITEM.test(line)) bulletCriteria.push({ line: i + 1, raw: rawLine });
    }
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
  rows.push('Rewrite the Story in user-observable terms: name who uses the behavior, what they do and what they see; keep implementation details in module prompts or tests.');
  return rows.join('\n');
}

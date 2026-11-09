// Generated from prompts/cli/workflow-runner.prompt.md (sha256: 47f261baa0f2894bae32d6cba49262a456808354cf77dfdf05407c4cc4b7fa5c).
// Recovery comments are planned before any GitHub write. The caller supplies the
// same already-cleaned step text used by the PR body, in its original order.
import { createHash } from 'node:crypto';

const LIMIT = 60_000;
// Reserve well beyond a canonical GitHub issue-comment URL, then enforce that
// reservation against each returned URL before publishing the index or body.
export const SUMMARY_RECOVERY_LINK_RESERVE = 512;
const size = text => [...text].length;
const markerSafe = text => text.replaceAll('pdd-workflow:', 'pdd-workflow\\u003a').replaceAll('pdd-product:', 'pdd-product\\u003a');
function span(text) {
  const safe = markerSafe(text);
  const fence = '`'.repeat([...safe.matchAll(/`+/g)].reduce((n, m) => Math.max(n, m[0].length), 0) + 1);
  const pad = /^`|`$/.test(safe) ? ' ' : '';
  return `${fence}${pad}${safe}${pad}${fence}`;
}
function failure(reason) { throw new Error(`Full-summary recovery cannot be published: ${reason}.`); }
function checked(text, what) {
  if (size(text) > LIMIT) failure(`${what} exceeds the 60,000-character limit`);
  return text;
}
const identity = value => typeof value === 'string' && /^[A-Za-z0-9_.-]+$/.test(value);
const marker = (runId, version, role, position) => `<!-- pdd-summary:${runId}:${version}:${role}:${position} -->`;
const chunkText = (runId, version, position, step, line, part, text) =>
  `${marker(runId, version, 'chunk', position)}\nFull step summary; step ${span(JSON.stringify(step))}, line ${line}, part ${part}:\n\n${span(JSON.stringify(text))}\n`;
const indexText = (runId, version, links) => `${marker(runId, version, 'index', 0)}\nFull step summaries, in order:\n\n${links.map((link, index) => `${index + 1}. ${link}`).join('\n')}\n`;

// Cuts are calculated in Unicode code points, but URL matches use JavaScript
// offsets. Convert each boundary once so a URL is always an indivisible unit.
function urlRanges(text) {
  return [...text.matchAll(/https?:\/\/\S+/g)].map(match => {
    const start = size(text.slice(0, match.index));
    return [start, start + size(match[0])];
  });
}

export function planSummaryRecovery(runId, rows) {
  if (!identity(runId) || !Array.isArray(rows) || rows.some(row => !row || typeof row.step !== 'string' || typeof row.text !== 'string'))
    failure('invalid run or cleaned summaries');
  const version = createHash('sha256').update(JSON.stringify(rows.map(({step, text}) => [step, text]))).digest('hex');
  const chunks = [];
  for (const { step, text } of rows) {
    const lines = text ? text.split('\n') : [''];
    for (let line = 0; line < lines.length; line++) {
      const points = [...lines[line]], ranges = urlRanges(lines[line]);
      let from = 0, part = 1;
      do {
        const position = chunks.length + 1;
        const render = end => chunkText(runId, version, position, step, line + 1, part, points.slice(from, end).join(''));
        if (size(render(from)) > LIMIT) failure('a step identity or wrapper is too large');
        let lo = from, hi = points.length + 1;
        while (hi - lo > 1) {
          const mid = Math.floor((lo + hi) / 2);
          if (size(render(mid)) <= LIMIT) lo = mid; else hi = mid;
        }
        const crossing = ranges.find(([start, end]) => start < lo && end > lo);
        if (crossing) lo = crossing[0];
        if (lo === from && from < points.length) failure('a URL or rendered unit cannot fit in a comment');
        chunks.push(checked(render(lo), 'a summary chunk'));
        from = lo; part++;
      } while (from < points.length);
    }
  }
  // Pack small line fragments together; the per-fragment labels preserve step,
  // line and part identity without wasting one GitHub comment per short line.
  const packed = [];
  for (const chunk of chunks) {
    const payload = chunk.slice(chunk.indexOf('\n') + 1);
    if (packed.length && size(packed.at(-1) + '\n' + payload) <= LIMIT) packed[packed.length - 1] += `\n${payload}`;
    else packed.push(checked(`${marker(runId, version, 'chunk', packed.length + 1)}\n${payload}`, 'a summary chunk'));
  }
  // Reserve each complete link before writing even the first comment.
  checked(indexText(runId, version, packed.map(() => 'x'.repeat(SUMMARY_RECOVERY_LINK_RESERVE))), 'the ordered recovery index');
  return { runId, version, chunks: packed };
}

export function summaryRecoveryIndex(plan, links) {
  if (!plan || !identity(plan.runId) || !/^[a-f0-9]{64}$/.test(plan.version) || !Array.isArray(plan.chunks)
    || !Array.isArray(links) || links.length !== plan.chunks.length
    || links.some(link => typeof link !== 'string' || !link || size(link) > SUMMARY_RECOVERY_LINK_RESERVE || /[\s<>]/u.test(link)))
    failure('confirmed chunk links are invalid or exceed their reservation');
  return checked(indexText(plan.runId, plan.version, links), 'the ordered recovery index');
}

export function summaryRecoveryNotice(link = null) {
  if (link === null) return 'Full step summary recovery is pending.';
  if (typeof link !== 'string' || !link || size(link) > SUMMARY_RECOVERY_LINK_RESERVE || /[\s<>]/u.test(link))
    failure('the confirmed index link is invalid or exceeds its reservation');
  return `Full step summaries: ${link}`;
}

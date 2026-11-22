// Shared Layer-1 diagnostics, 4-part agent-teaching formatting, and safe in-root file reads.
import { closeSync, constants, fstatSync, lstatSync, openSync, readSync } from 'node:fs';
import { isAbsolute, join } from 'node:path';

export const MAX_FILE_BYTES = 2 * 1024 * 1024;
export const HEAD_BYTES = 4096;

export const canonicalRepoPath = value =>
  typeof value === 'string'
  && value.trim().length > 0
  && value.length <= 1000
  && !isAbsolute(value)
  && !/[\\\x00-\x1f\x7f]/.test(value)
  && !value.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');

function openRegularInRoot(realRoot, relPath, maxBytes) {
  if (!canonicalRepoPath(relPath)) return null;
  const parts = relPath.split('/');
  let cur = realRoot;
  let observed = null;
  try {
    for (let i = 0; i < parts.length; i++) {
      cur = join(cur, parts[i]);
      const st = lstatSync(cur);
      if (st.isSymbolicLink()) return null;
      if (i < parts.length - 1 && !st.isDirectory()) return null;
      if (i === parts.length - 1) {
        if (!st.isFile() || (maxBytes !== null && st.size > maxBytes)) return null;
        observed = st;
      }
    }
  } catch {
    return null;
  }
  try {
    const fd = openSync(cur, constants.O_RDONLY | (constants.O_NOFOLLOW ?? 0) | (constants.O_NONBLOCK ?? 0));
    const fst = fstatSync(fd);
    if (!fst.isFile() || (observed && (fst.ino !== observed.ino || fst.dev !== observed.dev)) || (maxBytes !== null && fst.size > maxBytes)) {
      try { closeSync(fd); } catch {}
      return null;
    }
    return { fd, size: fst.size };
  } catch {
    return null;
  }
}

export function readSafeUtf8(realRoot, relPath, maxBytes = MAX_FILE_BYTES) {
  const opened = openRegularInRoot(realRoot, relPath, maxBytes);
  if (!opened) return null;
  const { fd, size } = opened;
  try {
    const buf = Buffer.alloc(size);
    let offset = 0;
    while (offset < buf.length) {
      const n = readSync(fd, buf, offset, buf.length - offset, offset);
      if (!n) break;
      offset += n;
    }
    const slice = buf.subarray(0, offset);
    if (slice.includes(0)) return null;
    return slice.toString('utf8');
  } catch {
    return null;
  } finally {
    try { closeSync(fd); } catch {}
  }
}

export function readSafeHeadUtf8(realRoot, relPath, limit = HEAD_BYTES + 1) {
  const opened = openRegularInRoot(realRoot, relPath, null);
  if (!opened) return null;
  const { fd, size } = opened;
  try {
    const len = Math.min(size, limit);
    const buf = Buffer.alloc(len);
    let offset = 0;
    while (offset < len) {
      const n = readSync(fd, buf, offset, len - offset, offset);
      if (!n) break;
      offset += n;
    }
    const slice = buf.subarray(0, offset);
    if (slice.includes(0)) return null;
    return slice.toString('utf8');
  } catch {
    return null;
  } finally {
    try { closeSync(fd); } catch {}
  }
}

export function buildLineStarts(text) {
  const starts = [0];
  for (let i = 0; i < text.length; i++) if (text[i] === '\n') starts.push(i + 1);
  return starts;
}

export function lineNumberAt(lineStarts, index) {
  let lo = 0;
  let hi = lineStarts.length - 1;
  while (lo <= hi) {
    const mid = (lo + hi) >> 1;
    if (lineStarts[mid] <= index) lo = mid + 1;
    else hi = mid - 1;
  }
  return lo;
}

/**
 * Format a 4-part agent-teaching diagnostic (Lauren Tan / OpenAI Harness Engineering pattern):
 * 1) location (`path:line [code]`), 2) invariant violated, 3) concrete 1-line fix, 4) rerun command.
 */
export function formatTeachingDetail({ invariant, fix, rerun = 'pdd lint --local' }) {
  const inv = String(invariant ?? '').trim().replace(/\.+$/, '');
  const fx = String(fix ?? '').trim().replace(/\.+$/, '');
  const rr = String(rerun ?? 'pdd lint --local').trim();
  const parts = [];
  if (inv) parts.push(`${inv}.`);
  if (fx) parts.push(`Fix: ${fx}.`);
  if (rr) parts.push(`Rerun: \`${rr}\`.`);
  return parts.join(' ');
}

export function formatDiagnosticLine(item, severity) {
  const prefix = severity === 'error' ? 'Error' : 'Warning';
  let detail = item.detail;
  if (severity === 'error' && item.fix && !/\bFix:\s/i.test(detail)) {
    detail = formatTeachingDetail({ invariant: detail, fix: item.fix, rerun: item.rerun ?? 'pdd lint --local' });
  } else if (severity === 'error' && !/\bFix:\s/i.test(detail)) {
    detail = `${detail.replace(/\.+$/, '')}. Fix: resolve [${item.code}] at ${item.filePath}:${item.line} and rerun \`pdd lint --local\`.`;
  }
  return `${prefix}: ${item.category}: ${item.filePath}:${item.line} [${item.code}] ${detail}`;
}

// Layer-0 safe JSON and JSONL file helpers.
import * as nativeFs from 'node:fs';
import { dirname } from 'node:path';
import { writeAtomicPrivate } from './atomic-fs.mjs';

/**
 * Safely read and parse a JSON file, returning `fallback` on missing/unreadable/corrupt content.
 */
export function readJsonSafe(fs, filePath, fallback = null) {
  const f = fs ?? nativeFs;
  try {
    return JSON.parse(f.readFileSync(filePath, 'utf8'));
  } catch {
    return fallback;
  }
}

/**
 * Atomically serialize `value` as pretty JSON (`0600` by default) into a `0700` parent directory.
 */
export function writeJsonAtomic(
  fs,
  filePath,
  value,
  { indent = 2, dirMode = 0o700, fileMode = 0o600 } = {},
) {
  const serialized = `${JSON.stringify(value, null, indent)}\n`;
  writeAtomicPrivate(fs ?? nativeFs, filePath, serialized, dirMode, fileMode);
}

/**
 * Read a JSONL file, skipping blank or torn lines and optionally filtering parsed entries.
 */
export function readJsonlSafe(fs, filePath, { filter = null } = {}) {
  const f = fs ?? nativeFs;
  let text;
  try {
    text = f.readFileSync(filePath, 'utf8');
  } catch {
    return [];
  }
  const entries = [];
  for (const line of text.split('\n')) {
    if (!line.trim()) continue;
    try {
      const parsed = JSON.parse(line);
      if (!filter || filter(parsed)) entries.push(parsed);
    } catch {
      // Skip torn/corrupt lines cleanly.
    }
  }
  return entries;
}

/**
 * Append one JSON line (`0600` by default) to `filePath`, creating its `0700` parent directory.
 */
export function appendJsonl(
  fs,
  filePath,
  entry,
  { dirMode = 0o700, fileMode = 0o600 } = {},
) {
  const f = fs ?? nativeFs;
  f.mkdirSync(dirname(filePath), { recursive: true, mode: dirMode });
  f.appendFileSync(filePath, `${JSON.stringify(entry)}\n`, { mode: fileMode });
}

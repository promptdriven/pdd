// Generated from prompts/scripts/check-generated-source.prompt.md (sha256: d02c5a69e3ace789f45214b0f8f9ae571325a7241ce1b9a044460fd2f80273e9).
import { execFileSync } from 'node:child_process';
import { closeSync, fstatSync, openSync, readSync } from 'node:fs';
import { join } from 'node:path';
import { findOwners } from '../src/file-owner.mjs';
import { gitFiles } from '../src/runtime-preflight.mjs';

const git = (cwd, args) => execFileSync('git', args, {
  cwd, encoding: 'utf8', maxBuffer: 512 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'],
});
const paths = output => output.split('\0').filter(Boolean);
const displayPath = path => /[\x00-\x1f\x7f]/.test(path) ? JSON.stringify(path) : path;

function reader(root, failures) {
  return (path, limit) => {
    let fd;
    try {
      fd = openSync(join(root, path), 'r');
      const buffer = Buffer.alloc(Math.min(limit, fstatSync(fd).size + 1));
      let count = 0;
      while (count < buffer.length) {
        const read = readSync(fd, buffer, count, buffer.length - count, count);
        if (!read) break;
        count += read;
      }
      return buffer.subarray(0, count);
    } catch (error) {
      if (error.code === 'ENOENT' || error.code === 'ENOTDIR') return null;
      failures.add(path);
      throw error;
    } finally { if (fd !== undefined) closeSync(fd); }
  };
}

function main(argv) {
  if (argv.length !== 2 || argv[0] !== '--base' || !argv[1]) {
    throw new Error('usage: node scripts/check-generated-source.mjs --base REF');
  }
  const root = git(process.cwd(), ['rev-parse', '--show-toplevel']).trim();
  const base = git(root, ['rev-parse', '--verify', '--end-of-options', `${argv[1]}^{commit}`]).trim();
  const changed = new Set([
    ...paths(git(root, ['diff', '--name-only', '-z', '--no-renames', base, '--'])),
    ...paths(git(root, ['ls-files', '-z', '--others', '--exclude-standard'])),
  ]);
  const visible = gitFiles(root);
  const promptChanged = [...changed].some(path => path.endsWith('.prompt.md'));
  const selected = promptChanged ? visible : visible.filter(path => changed.has(path));
  const failures = new Set();
  const result = findOwners({ root, paths: selected }, { files: () => visible, read: reader(root, failures) });
  let checked = 0, mismatches = 0;
  for (const row of result.files) {
    if (failures.has(row.path)) {
      throw new Error(`cannot read ${displayPath(row.path)}; generated-source digests could not be checked`);
    }
    if (!changed.has(row.path) && !row.headers.some(header => changed.has(header.prompt))) continue;
    for (const header of row.headers) {
      if (header.sha256 === null) continue;
      checked++;
      if (header.state === 'current') continue;
      mismatches++;
      process.stderr.write(`${displayPath(row.path)}: ${header.prompt} expected=${header.expected ?? 'unavailable'} current=${header.sha256} state=${header.state}\n`);
    }
  }
  if (mismatches) return 1;
  process.stdout.write(`Generated-source digests: ${checked} checked; 0 mismatches.\n`);
  return 0;
}

try { process.exitCode = main(process.argv.slice(2)); }
catch (error) {
  process.stderr.write(`Generated-source check: ${error.message}\n`);
  process.exitCode = 2;
}

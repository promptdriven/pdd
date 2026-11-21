#!/usr/bin/env node
import { existsSync, readdirSync, statSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const DEFAULT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');

// Imported directly by test/workflow-commit-warning-paths-replay.test.mjs;
// running it standalone would double-execute the same baseline suite.
export const EXCLUDED_TEST_FILES = Object.freeze([
  'test/workflow-commit-warning-paths/baseline.test.mjs',
]);

const EXCLUDED_SET = new Set(EXCLUDED_TEST_FILES);
const BROWSER_TEST_RE = /(?:^|\/)screen-[^/]+\.test\.mjs$/;
const VALID_MODES = new Set(['all', 'unit', 'browser']);

export function isBrowserTest(relPath) {
  return BROWSER_TEST_RE.test(String(relPath ?? '').replace(/\\/g, '/'));
}

function diagnostic(location, invariant, fix, rerun) {
  return [
    `Location: ${location}`,
    `Invariant: ${invariant}`,
    `Fix: ${fix}`,
    `Rerun: ${rerun}`,
  ].join('\n');
}

function walkTestDir(absDir, relPrefix, out) {
  for (const entry of readdirSync(absDir, { withFileTypes: true })) {
    const relPath = `${relPrefix}/${entry.name}`;
    const fullPath = join(absDir, entry.name);
    if (entry.isDirectory()) {
      walkTestDir(fullPath, relPath, out);
    } else if (entry.isFile() && entry.name.endsWith('.test.mjs')) {
      if (!EXCLUDED_SET.has(relPath)) out.push(relPath);
    }
  }
}

export function discoverTestFiles({ root = DEFAULT_ROOT, mode = 'all' } = {}) {
  if (!VALID_MODES.has(mode)) {
    throw new Error(diagnostic(
      `scripts/list-tests.mjs (mode=${JSON.stringify(mode)})`,
      'Test discovery mode must be one of "all", "unit", or "browser".',
      'Pass --all, --unit, or --browser (or omit the flag for all tests).',
      'node scripts/list-tests.mjs --all',
    ));
  }
  const rootDir = resolve(root);
  const testDir = join(rootDir, 'test');
  let isDir = false;
  try {
    isDir = statSync(testDir).isDirectory();
  } catch {
    isDir = false;
  }
  if (!isDir) {
    throw new Error(diagnostic(
      `${testDir}`,
      'Recursive test discovery requires an existing test/ directory under the target root.',
      'Run from the repository root or pass --root <repo-root> pointing to a checkout containing test/.',
      'node scripts/list-tests.mjs --root .',
    ));
  }

  const found = [];
  walkTestDir(testDir, 'test', found);
  found.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));

  if (mode === 'unit') return found.filter(file => !isBrowserTest(file));
  if (mode === 'browser') return found.filter(file => isBrowserTest(file));
  return found;
}

export function parseListArgs(argv) {
  let mode = null;
  let json = false;
  let help = false;
  let root = null;

  const setMode = next => {
    if (mode !== null && mode !== next) {
      throw new Error(diagnostic(
        `scripts/list-tests.mjs (--${mode} and --${next})`,
        'Only one test filter mode (--all, --unit, or --browser) may be specified per invocation.',
        `Remove either --${mode} or --${next}.`,
        `node scripts/list-tests.mjs --${next}`,
      ));
    }
    mode = next;
  };

  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === '--all') setMode('all');
    else if (arg === '--unit') setMode('unit');
    else if (arg === '--browser') setMode('browser');
    else if (arg === '--json') json = true;
    else if (arg === '-h' || arg === '--help') help = true;
    else if (arg === '--root') {
      const value = argv[++i];
      if (!value || value.startsWith('-')) {
        throw new Error(diagnostic(
          'scripts/list-tests.mjs (--root)',
          'Option --root requires a directory path argument.',
          'Provide a valid checkout path after --root (for example `--root .`).',
          'node scripts/list-tests.mjs --root .',
        ));
      }
      root = resolve(value);
    } else if (arg.startsWith('--root=')) {
      const value = arg.slice('--root='.length);
      if (!value) {
        throw new Error(diagnostic(
          'scripts/list-tests.mjs (--root=)',
          'Option --root= requires a non-empty directory path.',
          'Provide a valid checkout path after --root= (for example `--root=.`).',
          'node scripts/list-tests.mjs --root=.',
        ));
      }
      root = resolve(value);
    } else {
      throw new Error(diagnostic(
        `scripts/list-tests.mjs (argument "${arg}")`,
        'Unsupported CLI flag passed to test manifest discovery.',
        'Use only --all, --unit, --browser, --json, --root <dir>, or --help.',
        'node scripts/list-tests.mjs --help',
      ));
    }
  }

  const effectiveRoot = root ?? (existsSync(join(process.cwd(), 'test')) ? process.cwd() : DEFAULT_ROOT);
  return { mode: mode ?? 'all', json, help, root: effectiveRoot };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const opts = parseListArgs(process.argv.slice(2));
    if (opts.help) {
      process.stdout.write(
        'Usage: node scripts/list-tests.mjs [--all|--unit|--browser] [--json] [--root <dir>]\n',
      );
      process.exit(0);
    }
    const files = discoverTestFiles({ root: opts.root, mode: opts.mode });
    if (opts.json) {
      process.stdout.write(`${JSON.stringify(files, null, 2)}\n`);
    } else if (files.length > 0) {
      process.stdout.write(`${files.join('\n')}\n`);
    }
  } catch (err) {
    process.stderr.write(`${err?.message || String(err)}\n`);
    process.exit(2);
  }
}

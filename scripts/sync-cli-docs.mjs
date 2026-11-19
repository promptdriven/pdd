import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { PUBLIC_COMMAND_ROUTES } from '../src/command-catalog.mjs';
import { checkCliDocs, syncCliDocs } from '../src/cli-docs-sync.mjs';

const DEFAULT_DOC_PATH = resolve(dirname(fileURLToPath(import.meta.url)), '..', 'docs', 'cli.md');

const USAGE = [
  'Usage: node scripts/sync-cli-docs.mjs [--check | --write [--resolve-conflicts]] [--file PATH]',
  '',
  'Options:',
  '  --check               Verify that generated CLI command tables match src/command-catalog.mjs (default).',
  '  --write               Update the marker-delimited CLI command tables in place.',
  '  --resolve-conflicts   With --write, regenerate over Git conflict markers strictly inside the generated markers.',
  '  --file PATH           Target Markdown file (default: docs/cli.md).',
  '  -h, --help            Print this usage message.',
].join('\n');

/** Parse CLI flags for the standalone docs/cli.md sync runner. */
function parseArgs(argv) {
  let mode = null;
  let resolveConflicts = false;
  let filePath = null;
  let help = false;

  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === '--help' || arg === '-h') {
      help = true;
    } else if (arg === '--check' || arg === '--write') {
      const nextMode = arg.slice(2);
      if (mode && mode !== nextMode) {
        return { error: 'Cannot combine --check and --write.' };
      }
      mode = nextMode;
    } else if (arg === '--resolve-conflicts') {
      resolveConflicts = true;
    } else if (arg === '--file') {
      const value = argv[i + 1];
      if (!value || value.startsWith('-')) {
        return { error: '--file requires a path argument.' };
      }
      filePath = value;
      i += 1;
    } else {
      return { error: `Unknown option: ${arg}` };
    }
  }

  if (help) return { help: true };
  const effectiveMode = mode ?? 'check';
  if (resolveConflicts && effectiveMode !== 'write') {
    return { error: '--resolve-conflicts requires --write.' };
  }
  return { mode: effectiveMode, resolveConflicts, filePath };
}

/** Run the CLI docs check/sync command with injectable I/O and catalog ports. */
export function runSyncCliDocsCli(argv = process.argv.slice(2), ports = {}) {
  const stdout = ports.stdout ?? process.stdout;
  const stderr = ports.stderr ?? process.stderr;
  const readFile = ports.readFile ?? (path => readFileSync(path, 'utf8'));
  const writeFile = ports.writeFile ?? ((path, content) => writeFileSync(path, content, 'utf8'));
  const routes = ports.routes ?? PUBLIC_COMMAND_ROUTES;
  const defaultDocPath = ports.defaultDocPath ?? DEFAULT_DOC_PATH;

  const parsed = parseArgs(argv);
  if (parsed.error) {
    stderr.write(`${parsed.error}\n${USAGE}\n`);
    return 2;
  }
  if (parsed.help) {
    stdout.write(`${USAGE}\n`);
    return 0;
  }

  const targetPath = parsed.filePath ? resolve(parsed.filePath) : defaultDocPath;
  let document;
  try {
    document = readFile(targetPath);
  } catch (err) {
    stderr.write(`Failed to read ${targetPath}: ${err.message}\n`);
    return 2;
  }

  try {
    if (parsed.mode === 'check') {
      const result = checkCliDocs({ document, routes });
      if (result.ok) {
        stdout.write(`CLI reference tables are current (${result.formCount} forms).\n`);
        return 0;
      }
      if (result.status === 'conflict') {
        stderr.write('CLI reference generated block contains Git conflict markers. Run: node scripts/sync-cli-docs.mjs --write --resolve-conflicts\n');
        return 1;
      }
      const details = [];
      if (result.missingForms.length) details.push(`missing ${result.missingForms.length}: ${result.missingForms.join(', ')}`);
      if (result.extraForms.length) details.push(`extra ${result.extraForms.length}: ${result.extraForms.join(', ')}`);
      stderr.write(`CLI reference tables are stale${details.length ? ` (${details.join('; ')})` : ''}. Run: node scripts/sync-cli-docs.mjs --write\n`);
      return 1;
    }

    const result = syncCliDocs({
      document,
      routes,
      allowInsideConflicts: parsed.resolveConflicts,
    });
    if (result.changed) {
      writeFile(targetPath, result.document);
      const conflictNote = result.resolvedConflicts ? ' (resolved generated-block conflicts)' : '';
      stdout.write(`Updated CLI reference tables (${result.formCount} forms across ${result.groups.length} groups)${conflictNote}.\n`);
    } else {
      stdout.write(`CLI reference tables are already current (${result.formCount} forms).\n`);
    }
    return 0;
  } catch (err) {
    if (err?.code === 'generated-conflict') {
      stderr.write(`${err.message}\nRun: node scripts/sync-cli-docs.mjs --write --resolve-conflicts\n`);
      return 1;
    }
    stderr.write(`${err?.code ? `[${err.code}] ` : ''}${err.message}\n`);
    return 2;
  }
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  process.exitCode = runSyncCliDocsCli(process.argv.slice(2));
}

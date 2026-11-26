import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { PUBLIC_COMMAND_MANIFEST } from '../src/command-catalog.mjs';
import { renderCliDocs } from '../scripts/generate-cli-docs.mjs';

const CLI_DOCS = fileURLToPath(new URL('../docs/cli.md', import.meta.url));
const GENERATOR = fileURLToPath(new URL('../scripts/generate-cli-docs.mjs', import.meta.url));

// Wrong: pdd --help gains or changes a command form, and docs/cli.md does not show it, so the reference falls behind.
test('docs/cli.md shows every command form of the help catalog as a code span', () => {
  const doc = readFileSync(CLI_DOCS, 'utf8');
  // A pipe inside a Markdown table cell is written as \|.
  const shown = new Set([...doc.matchAll(/`([^`\n]+)`/g)].map(match => match[1].replaceAll('\\|', '|')));
  const missing = PUBLIC_COMMAND_MANIFEST.map(entry => entry.form).filter(form => !shown.has(form));
  assert.deepEqual(missing, [], `docs/cli.md is missing these forms from pdd --help:\n${missing.join('\n')}`);
});

test('docs/cli.md command tables match scripts/generate-cli-docs.mjs --check deterministically', (t) => {
  const doc = readFileSync(CLI_DOCS, 'utf8');
  const first = renderCliDocs(doc);
  assert.equal(first.changed, false, `docs/cli.md is out of sync (stale groups: ${first.staleGroups.join(', ')}); run node scripts/generate-cli-docs.mjs`);
  assert.deepEqual(first.staleGroups, []);
  assert.equal(renderCliDocs(first.output).output, first.output, 'generator output must be idempotent');

  const out = execFileSync(process.execPath, [GENERATOR, '--check'], { encoding: 'utf8' });
  assert.match(out, new RegExp(`\\(${PUBLIC_COMMAND_MANIFEST.length} forms across`));

  // Verify --check fails closed on stale table text and --write restores byte-exact sync.
  const dir = mkdtempSync(join(tmpdir(), 'pdd-cli-docs-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const copy = join(dir, 'cli.md');
  writeFileSync(copy, doc.replace('| `pdd init` |', '| `pdd init-stale` |'), 'utf8');
  assert.throws(
    () => execFileSync(process.execPath, [GENERATOR, '--check', '--file', copy], { encoding: 'utf8', stdio: 'pipe' }),
    (err) => err.status === 1 && /out of sync/i.test(String(err.stderr ?? '')),
  );
  execFileSync(process.execPath, [GENERATOR, '--write', '--file', copy], { encoding: 'utf8' });
  assert.equal(readFileSync(copy, 'utf8'), doc);
});

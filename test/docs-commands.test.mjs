import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { PUBLIC_COMMAND_MANIFEST, PUBLIC_COMMAND_ROUTES } from '../src/command-catalog.mjs';
import { checkCliDocs } from '../src/cli-docs-sync.mjs';

// Wrong: pdd --help gains or changes a command form, and docs/cli.md does not show it, so the reference falls behind.
test('docs/cli.md shows every command form of the help catalog as a code span', () => {
  const doc = readFileSync(new URL('../docs/cli.md', import.meta.url), 'utf8');
  // A pipe inside a Markdown table cell is written as \|.
  const shown = new Set([...doc.matchAll(/`([^`\n]+)`/g)].map(match => match[1].replaceAll('\\|', '|')));
  const missing = PUBLIC_COMMAND_MANIFEST.map(entry => entry.form).filter(form => !shown.has(form));
  assert.deepEqual(missing, [], `docs/cli.md is missing these forms from pdd --help:\n${missing.join('\n')}`);
});

// Wrong: docs/cli.md generated command index drifts from PUBLIC_COMMAND_ROUTES or retains conflict markers.
test('docs/cli.md generated command index matches PUBLIC_COMMAND_ROUTES', () => {
  const doc = readFileSync(new URL('../docs/cli.md', import.meta.url), 'utf8');
  const result = checkCliDocs({ document: doc, routes: PUBLIC_COMMAND_ROUTES });
  assert.deepEqual(
    result,
    {
      ok: true,
      status: 'current',
      missingForms: [],
      extraForms: [],
      formCount: PUBLIC_COMMAND_MANIFEST.length,
    },
    'Run: node scripts/sync-cli-docs.mjs --write',
  );
});

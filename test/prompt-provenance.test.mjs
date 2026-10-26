import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { join } from 'node:path';

const pairs = [
  ['prompts/cli/command-catalog.prompt.md', 'src/command-catalog.mjs'],
  ['prompts/cli/pdd-cli.prompt.md', 'src/pdd-cli.mjs'],
  ['prompts/cli/workflow-runner.prompt.md', 'src/workflow-runner.mjs'],
];

test('generated CLI modules carry the exact owning prompt hash', async () => {
  for (const [prompt, source] of pairs) {
    const bytes = await readFile(new URL(`../${prompt}`, import.meta.url));
    const expected = createHash('sha256').update(bytes).digest('hex');
    const header = (await readFile(new URL(`../${source}`, import.meta.url), 'utf8')).split('\n', 1)[0];
    assert.match(header, new RegExp(`sha256: ${expected}\\)`), `${source} is stale for ${prompt}`);
  }
});

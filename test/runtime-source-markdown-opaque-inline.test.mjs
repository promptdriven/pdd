import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { captureSource } from '../src/runtime-preflight.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, portsFor } from './runtime-fake.mjs';

// Approved before execution: CommonMark §6.1 gives valid HTML tags/autolinks
// precedence over backticks inside them; the outside dependency stays genuine.
const DOCUMENT = 'docs/opaque.md', ORDER = 'tests/place-order.json';
for (const [kind, prefix] of [
  ['HTML attribute', 'Lead <span title="`"> '],
  ['autolink', 'Lead <https://example.invalid/`> '],
]) for (const image of [false, true]) {
  test(`SOURCE-OPAQUE: ${kind} preserves outside ${image ? 'image' : 'link'}`, async t => {
    const { repo, home } = harbor(t);
    mkdirSync(join(repo, 'docs'));
    writeFileSync(join(repo, 'pdd-source.json'), JSON.stringify({ include: [DOCUMENT] }));
    const bytes = Buffer.from('# UTF-8: café\r\n## Dependencies\r\n'
      + prefix + (image ? '!' : '') + '[Required](credentials.json) ` tail\r\n');
    writeFileSync(join(repo, DOCUMENT), bytes);
    writeFileSync(join(repo, 'docs/credentials.json'), 'synthetic\n');
    let failure;
    try { captureSource(repo, { tests: [ORDER] }); }
    catch (error) { failure = error; }
    assert.equal(failure?.exitCode ?? 0, 4, 'outside secret dependency must be refused');
    assert.ok(failure.message.includes('docs/credentials.json'), failure.message);
    const calls = { gh: 0, fetch: 0 };
    const { ports } = portsFor({ HOME: home, PDD_RUNTIME_URL: 'http://127.0.0.1:9' }, {
      gh: () => { calls.gh++; assert.fail('discovery must not authenticate'); },
      fetch: () => { calls.fetch++; assert.fail('discovery must not use the network'); },
    });
    assert.equal(await runCheck({ cwd: repo, words: [ORDER], options: { '--files': true } }, ports), 4, ports.stderr.text);
    assert.ok(ports.stderr.text.includes('docs/credentials.json'), ports.stderr.text);
    assert.deepEqual(readFileSync(join(repo, DOCUMENT)), bytes);
    assert.deepEqual(calls, { gh: 0, fetch: 0 });
  });
}

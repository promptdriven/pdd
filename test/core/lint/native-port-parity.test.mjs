import '../../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { lintNativeOnlyPortParity } from '../../../src/core/lint/native-port-parity.mjs';
import { extractFrontmatterPorts } from '../../../src/core/lint/prompt-metadata.mjs';

test('YAML frontmatter ports (inline and block list) declare valid ports alongside ## Ports and <stem>.<op> exports', () => {
  const inlineDep = [
    '---',
    'ports: [ledger.append, ledger.balance]',
    '---',
    '',
    '# Ledger domain',
    '',
    '## Public operations',
    '### post_entry',
    'Records an immutable entry.',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');

  const blockDep = [
    '---',
    'ports:',
    '  - clock.now',
    '  - signer.verify',
    '---',
    '',
    '# Auth',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');

  assert.deepEqual(extractFrontmatterPorts(inlineDep).map(x => x.port), ['ledger.append', 'ledger.balance']);
  assert.deepEqual(extractFrontmatterPorts(blockDep).map(x => x.port), ['clock.now', 'signer.verify']);

  const adapterOk = [
    '---',
    'kind: native-only',
    'reason: Real Postgres ledger adapter.',
    '---',
    '',
    '# Ledger adapter',
    '',
    '## Port wiring',
    '- `ledger.append`, `ledger.balance`, `ledger.post_entry`',
    '- `clock.now`, `signer.verify`',
    '',
    '## Storage schema',
    '```sql',
    'CREATE TABLE entries (id TEXT PRIMARY KEY, amount_cents INTEGER NOT NULL);',
    '```',
    'Index on `entries.amount_cents` speeds queries.',
    '',
    '## Dependencies',
    '- [ledger](ledger.prompt.md)',
    '- [auth](auth.prompt.md)',
  ].join('\n');

  const deps = [
    { path: 'prompts/ledger.prompt.md', text: inlineDep, isPrompt: true },
    { path: 'prompts/auth.prompt.md', text: blockDep, isPrompt: true },
  ];
  assert.deepEqual(lintNativeOnlyPortParity(adapterOk, deps, { path: 'prompts/ledger-adapter.prompt.md' }), []);

  const adapterBroken = adapterOk.replace('`ledger.post_entry`', '`ledger.post_entries`');
  const errs = lintNativeOnlyPortParity(adapterBroken, deps, { path: 'prompts/ledger-adapter.prompt.md' });
  assert.equal(errs.length, 1, errs.join('\n'));
  assert.match(errs[0], /prompts\/ledger-adapter\.prompt\.md:9 \[native-only-unknown-port\].*"ledger\.post_entries"/);
  assert.match(errs[0], /Fix:.*Rerun: `pdd lint/);
});

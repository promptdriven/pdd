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

test('Astra #11: wiring cue prose line carries into immediately following bullet list to catch undeclared ports', () => {
  const dep = '# Order domain\n\n## Ports\n- `store.load`\n\n## Dependencies\nNone.\n';
  const adapterWithCueList = [
    '---',
    'kind: native-only',
    'reason: Native mailer + store adapter.',
    '---',
    '',
    '# Adapter',
    '',
    'Wire the following ports:',
    '',
    '- `store.load`: loads order.',
    '- `mailer.send`: sends confirmation email.',
    '',
    '## Dependencies',
    '- [order](order.prompt.md)',
  ].join('\n');

  const errs = lintNativeOnlyPortParity(
    adapterWithCueList,
    [{ path: 'prompts/order.prompt.md', text: dep, isPrompt: true }],
    { path: 'prompts/adapter.prompt.md' },
  );
  assert.equal(errs.length, 1, errs.join('\n'));
  assert.match(errs[0], /prompts\/adapter\.prompt\.md:11 \[native-only-unknown-port\].*"mailer\.send"/);

  // Astra R2 #8: cue line WITHOUT trailing colon still carries across optional blank line into bullet list.
  const withoutColon = adapterWithCueList.replace('Wire the following ports:', 'Wire the following ports');
  const errsNoColon = lintNativeOnlyPortParity(
    withoutColon,
    [{ path: 'prompts/order.prompt.md', text: dep, isPrompt: true }],
    { path: 'prompts/adapter.prompt.md' },
  );
  assert.equal(errsNoColon.length, 1, errsNoColon.join('\n'));
  assert.match(errsNoColon[0], /"mailer\.send"/);
});

test('#3619 R1-R8 parity: O(N) inline code spans, hyphen/path boundary guards, peer dir/stem ops, non-op suffix rejection, and routing table filter', () => {
  const dep = [
    '# Connector Access',
    '',
    'This prompt re-exports nothing, ignores `foo/exports` `bogus_a`, `a.exports` `bogus_b`, and `:exports` `bogus_c`.',
    'It never exports `forbidden_op`.',
    'It exports `field_a` and `field_b` fields for logging.',
    'It exports `note`: `leaked_op` should not leak.',
    'Exports: `invoke_tool`, `redeem_view`.',
    '',
    '## User interface',
    '- `ui_only_widget`: must not become an exported op.',
    '',
    '## Public operations',
    '### `verify_grant`',
    '#### Inputs: request details',
    '- `request_id`: must not become an exported op.',
    '',
    '## Dependencies',
    '- Exports `dep_only_op` (must be ignored inside Dependencies).',
  ].join('\n');

  const okAdapter = [
    '---',
    'kind: native-only',
    'reason: Real HTTPS transport.',
    '---',
    '# MCP server',
    '',
    '| Command | Target |',
    '|---|---|',
    '| status | `router.dispatch` |',
    '',
    '## Port wiring',
    '- `access.invoke_tool`, `connector.redeem_view`, `access.verify_grant`',
    '',
    '## Dependencies',
    '- [access](access.prompt.md)',
  ].join('\n');

  const deps = [{ path: 'prompts/connector/access.prompt.md', text: dep, isPrompt: true }];
  assert.deepEqual(
    lintNativeOnlyPortParity(okAdapter, deps, { path: 'prompts/connector/mcp-server.prompt.md' }),
    [],
    'valid stem + non-generic parent-dir peer ops and routing table outside ## Ports must pass',
  );

  // Every false-positive / leaked op MUST still be rejected as undeclared!
  const spoofAdapter = [
    '---',
    'kind: native-only',
    'reason: Real HTTPS transport.',
    '---',
    '# MCP server',
    '## Port wiring',
    '- `access.bogus_a`, `access.bogus_b`, `access.bogus_c`, `access.forbidden_op`, `access.field_a`, `access.field_b`, `access.leaked_op`, `access.ui_only_widget`, `access.request_id`, `access.dep_only_op`',
    '## Dependencies',
    '- [access](access.prompt.md)',
  ].join('\n');
  const errs = lintNativeOnlyPortParity(spoofAdapter, deps, { path: 'prompts/connector/mcp-server.prompt.md' });
  assert.equal(errs.length, 10, `all 10 R5-R8 non-ops must be rejected:\n${errs.join('\n')}`);
  assert.match(errs[0], /Rerun: `pdd lint`\.$/);

  // R7 O(N) perf test: 20,000 backticks in a single cue line must finish in <100ms!
  const hugeLine = `${'`a` '.repeat(5000)} exports ${'`'.repeat(10000)} \`real_op\``;
  const t0 = performance.now();
  lintNativeOnlyPortParity(
    '---\nkind: native-only\nreason: Perf.\n---\n# Perf\n## Port wiring\n- `perf.real_op`\n## Dependencies\n- [perf](perf.prompt.md)\n',
    [{ path: 'prompts/perf.prompt.md', text: `# Perf\n${hugeLine}\n## Dependencies\nNone.\n`, isPrompt: true }],
    { path: 'prompts/perf-adapter.prompt.md' },
  );
  const ms = performance.now() - t0;
  assert.ok(ms < 100, `20k-backtick inline span scan must stay linear (<100ms), took ${ms.toFixed(1)}ms`);
});

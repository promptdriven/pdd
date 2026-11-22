import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { auditProductPlan } from '../src/product.mjs';
import { lintPublicInterfaceTests } from '../src/repo-hygiene-lint.mjs';

const MAP = [
  '# Ledger: map',
  '',
  '## Parts',
  '| Part | Folder | What it is |',
  '|---|---|---|',
  '| ledger | prompts/ledger | Cap table core. |',
  '| cli | prompts/cli | Command line. |',
  '',
].join('\n');

const PROMPT_FILES = [
  { path: 'prompts/ledger/cap-table.prompt.md', content: 'Cap table.' },
  { path: 'prompts/cli/command.prompt.md', content: 'Command.' },
];

const plan = lines => ['# Ledger: plan', '', '## Prompts', ...lines, ''].join('\n');

test('3631: a bare `.prompt.md` extension in ## Prompts prose is not a declared prompt', () => {
  const audit = auditProductPlan({
    mapText: MAP,
    planText: plan([
      'Names in the middle columns are `.prompt.md` files under the indicated folder.',
      'Every `*.prompt.md` file belongs to exactly one part.',
      '',
      '| Part | Prompt |',
      '|---|---|',
      '| ledger | prompts/ledger/cap-table.prompt.md |',
      '| cli | prompts/cli/command.prompt.md |',
      '',
      '### ledger (`prompts/ledger`)',
      'Each `.prompt.md` here owns one module.',
    ]),
    promptFiles: PROMPT_FILES,
  });
  assert.deepEqual(audit.findings, []);
});

test('3631: a declared prompt that is really missing is still reported', () => {
  const audit = auditProductPlan({
    mapText: MAP,
    planText: plan([
      'Names in the middle columns are `.prompt.md` files under the indicated folder.',
      '- `prompts/ledger/cap-table.prompt.md`',
      '- `prompts/cli/command.prompt.md`',
      '- `prompts/cli/missing.prompt.md`',
    ]),
    promptFiles: PROMPT_FILES,
  });
  const drift = audit.findings.filter(f => f.code === 'product-prompt-inventory-drift');
  assert.equal(drift.length, 1, JSON.stringify(audit.findings));
  assert.match(JSON.stringify(drift[0]), /prompts\/cli\/missing\.prompt\.md/);
  assert.doesNotMatch(JSON.stringify(audit.findings), /"\.prompt\.md"|\/\.prompt\.md/);
});

test('3631: Python tests may import helpers from a language-suffixed test folder such as tests_py/', () => {
  const pyTest = [
    'from tests_py._pdd_harness import run_case',
    'from tests_py import _pdd_harness',
    'import tests_py._pdd_harness as harness',
    '',
    'def test_issue():',
    '    assert run_case("issue") == 0',
    '',
  ].join('\n');
  const warnings = lintPublicInterfaceTests(pyTest, { path: 'tests_py/test_issue.py' });
  assert.deepEqual(warnings.filter(w => w.includes('[test-private-import]')), []);
});

test('3631: a JavaScript test may import a private helper next to it in tests_ts/', () => {
  const jsTest = "import { runCase } from './_harness.mjs';\nimport test from 'node:test';\n";
  const warnings = lintPublicInterfaceTests(jsTest, { path: 'tests_ts/orders.test.mjs' });
  assert.deepEqual(warnings.filter(w => w.includes('[test-private-import]')), []);
});

test('3631: private production imports from a tests_py test are still reported', () => {
  const pyTest = 'from app._internal import ledger\nfrom testing_app import _secret\n';
  const warnings = lintPublicInterfaceTests(pyTest, { path: 'tests_py/test_ledger.py' });
  const privateImports = warnings.filter(w => w.includes('[test-private-import]'));
  assert.equal(privateImports.length, 2, JSON.stringify(warnings));
});

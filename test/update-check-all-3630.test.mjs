import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, realpathSync, rmSync, unlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { promptHeaderHash } from '../src/file-owner.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

const GIT_BIN = execFileSync('which', ['git'], { encoding: 'utf8' }).trim() || '/usr/bin/git';
const capture = () => ({ text: '', write(value) { this.text += value; return true; } });

function git(cwd, args) {
  return execFileSync(GIT_BIN, args, {
    cwd,
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
    env: {
      PATH: `${dirname(GIT_BIN)}:/usr/bin:/bin`,
      HOME: cwd,
      GIT_CONFIG_NOSYSTEM: '1',
      GIT_CONFIG_GLOBAL: '/dev/null',
      GIT_AUTHOR_NAME: 'Test',
      GIT_AUTHOR_EMAIL: 'test@example.invalid',
      GIT_COMMITTER_NAME: 'Test',
      GIT_COMMITTER_EMAIL: 'test@example.invalid',
    },
  }).trim();
}

function makeRepo(t, files) {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-update-all-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  git(root, ['init', '-q', '-b', 'main']);
  for (const [rel, content] of Object.entries(files)) {
    mkdirSync(dirname(join(root, rel)), { recursive: true });
    writeFileSync(join(root, rel), content);
  }
  commit(root, 'init');
  return root;
}

function commit(root, message) {
  git(root, ['add', '-A']);
  git(root, ['commit', '-qm', message]);
}

async function cli(argv, cwd) {
  const stdout = capture(), stderr = capture();
  const code = await runPdd(argv, {
    stdout,
    stderr,
    cwd,
    env: { PATH: dirname(GIT_BIN), HOME: cwd, PDD_STATE_DIR: join(cwd, '.local', 'state', 'pdd'), PDD_RUNTIME_URL: 'invalid' },
  });
  return { code, out: stdout.text, err: stderr.text };
}

const promptText = name => `# ${name}\n\nOwn \`src/${name}.mjs\`.\n\n## Domain decisions\n\n- Amounts use integer cents.\n`;
const codeText = (name, body = 'return 1;') =>
  `// Generated from prompts/${name}.prompt.md (sha256: ${promptHeaderHash(promptText(name))}).\nexport function ${name}() { ${body} }\n`;

function twoModuleRepo(t) {
  return makeRepo(t, {
    'prompts/billing.prompt.md': promptText('billing'),
    'src/billing.mjs': codeText('billing'),
    'prompts/ledger.prompt.md': promptText('ledger'),
    'src/ledger.mjs': codeText('ledger'),
    'prompts/tests/billing.test.prompt.md': '# Billing tests\n\nDescribe the billing tests.\n',
    'README.md': '# Demo\n',
  });
}

test('3630: on a clean branch, --check --all checks every owned module instead of reporting an empty scope', async t => {
  const root = twoModuleRepo(t);

  const defaultCheck = await cli(['update', '--check', '--json'], root);
  assert.equal(defaultCheck.code, 0, defaultCheck.err);
  assert.equal(JSON.parse(defaultCheck.out).scope.kind, 'working-tree');

  const all = await cli(['update', '--check', '--all', '--json'], root);
  assert.equal(all.code, 1, all.err);
  const report = JSON.parse(all.out);
  assert.equal(report.ok, false);
  assert.equal(report.scope.kind, 'all');
  assert.deepEqual(report.drifted.map(d => [d.path, d.status]), [['src/billing.mjs', 'unpinned'], ['src/ledger.mjs', 'unpinned']]);
  assert.deepEqual(report.unowned, [], 'files no prompt owns are not listed under --all');
  for (const group of report.prompts) {
    assert.ok(group.instructions.some(step => step.includes('pdd update --write')), JSON.stringify(group.instructions));
  }

  const text = await cli(['update', '--check', '--all'], root);
  assert.equal(text.code, 1);
  assert.match(text.out, /2 owned module\(s\), 2 drifted/);
});

test('3630: --write --all pins every module, and --check --all then passes on the committed branch', async t => {
  const root = twoModuleRepo(t);

  const write = await cli(['update', '--write', '--all', '--json'], root);
  assert.equal(write.code, 0, write.err);
  assert.ok(existsSync(join(root, '.pdd/sync/src/billing.mjs.json')));
  assert.ok(existsSync(join(root, '.pdd/sync/src/ledger.mjs.json')));
  commit(root, 'pin');

  const check = await cli(['update', '--check', '--all', '--json'], root);
  assert.equal(check.code, 0, check.out + check.err);
  const report = JSON.parse(check.out);
  assert.equal(report.ok, true);
  assert.deepEqual(report.modules.map(m => [m.path, m.status]), [['src/billing.mjs', 'current'], ['src/ledger.mjs', 'current']]);

  // A committed code edit is invisible to the default scope but not to --all.
  writeFileSync(join(root, 'src/ledger.mjs'), codeText('ledger', 'return 2;'));
  commit(root, 'edit ledger');
  assert.equal((await cli(['update', '--check'], root)).code, 0);
  const drift = await cli(['update', '--check', '--all', '--json'], root);
  assert.equal(drift.code, 1);
  assert.deepEqual(JSON.parse(drift.out).drifted.map(d => [d.path, d.status]), [['src/ledger.mjs', 'code-drifted']]);
});

test('3630: --check --all flags a committed sync record whose module and prompt are gone', async t => {
  const root = twoModuleRepo(t);
  assert.equal((await cli(['update', '--write', '--all'], root)).code, 0);
  commit(root, 'pin');
  unlinkSync(join(root, 'src/ledger.mjs'));
  unlinkSync(join(root, 'prompts/ledger.prompt.md'));
  commit(root, 'drop ledger but keep its sync record');

  const check = await cli(['update', '--check', '--all', '--json'], root);
  assert.equal(check.code, 1, check.out + check.err);
  assert.deepEqual(JSON.parse(check.out).drifted.map(d => d.path), ['src/ledger.mjs']);

  assert.equal((await cli(['update', '--write', '--all'], root)).code, 0);
  assert.equal(existsSync(join(root, '.pdd/sync/src/ledger.mjs.json')), false);
  assert.equal((await cli(['update', '--check', '--all'], root)).code, 0);
});

test('3630: --all cannot be combined with file paths or --from', async t => {
  const root = twoModuleRepo(t);
  const withFiles = await cli(['update', 'src/billing.mjs', '--all', '--check'], root);
  assert.equal(withFiles.code, 2);
  assert.match(withFiles.err, /--all/);
  const withRange = await cli(['update', '--from', 'HEAD', '--all', '--check'], root);
  assert.equal(withRange.code, 2);
  assert.match(withRange.err, /--all/);
});

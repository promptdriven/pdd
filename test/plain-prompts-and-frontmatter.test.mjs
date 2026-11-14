import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { Readable } from 'node:stream';
import { runPdd } from '../src/pdd-cli.mjs';
import { runApprove } from '../src/prompt-approve.mjs';
import { promptClaims } from '../src/file-owner.mjs';
import {
  buildProjectCard,
  captureSource,
  composeProductTry,
  findTests,
  interfaceBlocks,
  parsePromptFrontmatter,
  preflight,
  productTapCallBound,
  proseSha256,
  runCheck,
  runtimePreflightSlice,
  whyNoTests,
} from '../src/runtime-seam.mjs';

const { lintLocalHygiene } = runtimePreflightSlice();
import { PLACE, harbor, portsFor, sink, temp } from './helpers/runtime-fake.mjs';

function git(cwd, ...args) {
  const out = spawnSync('git', args, { cwd, encoding: 'utf8' });
  assert.equal(out.status, 0, out.stderr);
  return out.stdout.trim();
}

function stripEmbeddedInterface(text) {
  const blocks = interfaceBlocks(text);
  return blocks.length ? `${text.replace(blocks[0][0], '').trimEnd()}\n` : text;
}

test('3367 CLI: removed interface draft, --fill-hash, --compact and approve --automatic/--tests exit 2 before side effects', async t => {
  const setup = harbor(t);
  const forbidden = {
    gh: () => assert.fail('removed command/option must not authenticate'),
    fetch: () => assert.fail('removed command/option must not contact Runtime'),
  };
  for (const argv of [
    ['interface', 'draft'],
    ['interface', 'draft', PLACE],
    ['test', '--fill-hash'],
    ['test', '--compact'],
    ['approve', PLACE, '--automatic'],
    ['approve', PLACE, '--tests'],
  ]) {
    const stdout = sink(), stderr = sink();
    const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state }, forbidden);
    const code = await runPdd(argv, { cwd: setup.repo, env: ports.env, stdout, stderr });
    assert.equal(code, 2, `${argv.join(' ')}: ${stdout.text}${stderr.text}`);
    assert.equal(stdout.text, '');
  }
});

test('3367 frontmatter: parsePromptFrontmatter parses native-only YAML frontmatter and rejects malformed blocks', () => {
  const plain = parsePromptFrontmatter('# Plain\n\nReturn the greeting.\n');
  assert.deepEqual(plain, { hasFrontmatter: false, kind: null, reason: null, error: null });

  const valid = parsePromptFrontmatter('---\r\n# comment\r\nkind: "native-only"\r\nreason: \'Uses OS keychain IPC.\'\r\n---\r\n# Keychain\r\n\r\nRead token.\r\n');
  assert.deepEqual(valid, {
    hasFrontmatter: true,
    kind: 'native-only',
    reason: 'Uses OS keychain IPC.',
    error: null,
  });

  const unclosed = parsePromptFrontmatter('---\nkind: native-only\nreason: Unclosed\n# Heading\n');
  assert.equal(unclosed.hasFrontmatter, true);
  assert.equal(unclosed.error, 'interface-kind-invalid');

  const badLine = parsePromptFrontmatter('---\nkind: native-only\nnot a key value line\n---\n# Heading\n');
  assert.equal(badLine.hasFrontmatter, true);
  assert.equal(badLine.error, 'interface-kind-invalid');

  const unknownKey = parsePromptFrontmatter('---\nkind: native-only\nreason: ok\nextra: nope\n---\n# Heading\n');
  assert.equal(unknownKey.hasFrontmatter, true);
  assert.equal(unknownKey.error, 'interface-kind-invalid');

  const missingReason = parsePromptFrontmatter('---\nkind: native-only\n---\n# Heading\n');
  assert.equal(missingReason.hasFrontmatter, true);
  assert.equal(missingReason.error, 'native-reason-missing');
});

test('3367 frontmatter: native-only skips Runtime execution locally and invalid frontmatter refuses with exit 4', async t => {
  const reason = 'Uses OS Unix domain sockets and process signals.';
  const setup = harbor(t, repo => {
    const plainBody = stripEmbeddedInterface(readFileSync(join(repo, PLACE), 'utf8'));
    writeFileSync(join(repo, PLACE), `---\nkind: native-only\nreason: ${reason}\n---\n\n${plainBody}`);
  });
  const offline = () => portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state }, {
    gh: () => assert.fail('frontmatter native-only must not sign in'),
    fetch: () => assert.fail('frontmatter native-only must not contact Runtime'),
  }).ports;

  const found = findTests({ root: setup.repo });
  const pre = preflight({ root: setup.repo, found, selected: found.tests });
  assert.ok(pre.rows.every(row => row.refusals.length === 0));
  assert.deepEqual(pre.rows[0].native_only, [{ path: PLACE, reason }]);

  const checkPorts = offline();
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--json': true } }, checkPorts), 5, checkPorts.stderr.text);
  const checkJson = JSON.parse(checkPorts.stdout.text);
  assert.equal(checkJson.rows[0].state, 'not run');
  assert.match(checkJson.rows[0].reason.message, /Unix domain sockets/);
  assert.deepEqual(checkJson.coverage.runtime, { total: 1, checkable: 0, native_only: 1 });

  for (const [label, header, expectedCode] of [
    ['missing reason', '---\nkind: native-only\n---\n', 'native-reason-missing'],
    ['blank reason', '---\nkind: native-only\nreason: "   "\n---\n', 'native-reason-missing'],
    ['unsupported kind', '---\nkind: full\n---\n', 'interface-kind-invalid'],
    ['unclosed fence', '---\nkind: native-only\nreason: Missing fence\n', 'interface-kind-invalid'],
  ]) {
    const bad = harbor(t, repo => {
      const plainBody = stripEmbeddedInterface(readFileSync(join(repo, PLACE), 'utf8'));
      writeFileSync(join(repo, PLACE), `${header}\n${plainBody}`);
    });
    const p = portsFor({ HOME: bad.home, PDD_STATE_DIR: bad.state }, {
      gh: () => assert.fail(`${label} must not sign in`),
      fetch: () => assert.fail(`${label} must not contact Runtime`),
    }).ports;
    assert.equal(await runCheck({ cwd: bad.repo, words: ['place-order'], options: { '--json': true } }, p), 4, label);
    assert.equal(JSON.parse(p.stdout.text).rows[0].refusals[0].code, expectedCode, label);
  }

  // Combining frontmatter and legacy <details> Runtime interface block refuses with pdd-two-interfaces
  const both = harbor(t, repo => {
    const withBlock = readFileSync(join(repo, PLACE), 'utf8');
    writeFileSync(join(repo, PLACE), `---\nkind: native-only\nreason: Duplicate.\n---\n\n${withBlock}`);
  });
  const bothPorts = portsFor({ HOME: both.home, PDD_STATE_DIR: both.state }, {
    gh: () => assert.fail('duplicate declaration must not sign in'),
    fetch: () => assert.fail('duplicate declaration must not contact Runtime'),
  }).ports;
  assert.equal(await runCheck({ cwd: both.repo, words: ['place-order'], options: { '--json': true } }, bothPorts), 4);
  assert.equal(JSON.parse(bothPorts.stdout.text).rows[0].refusals[0].code, 'pdd-two-interfaces');
});

test('3367 files, local lint and whyNoTests treat plain Markdown and frontmatter native-only prompts as first-class', async t => {
  const setup = harbor(t, repo => {
    const plainBody = stripEmbeddedInterface(readFileSync(join(repo, PLACE), 'utf8'))
      .replace('None.', '- [Menu rules](menu.prompt.md)');
    writeFileSync(join(repo, PLACE), plainBody);
    writeFileSync(join(repo, 'prompts/menu.prompt.md'), '# Menu rules\n\nPrices are in whole cents.\n');
    writeFileSync(join(repo, 'prompts/daemon.prompt.md'), '---\nkind: native-only\nreason: Spawns SSH tunnel.\n---\n\n# Daemon\n\nKeep tunnel open.\n');
  });

  // 1) pdd files text & JSON
  const textOut = sink(), textErr = sink();
  assert.equal(await runPdd(['files'], { cwd: setup.repo, env: { HOME: setup.home, PDD_STATE_DIR: setup.state }, stdout: textOut, stderr: textErr }), 0, textErr.text);
  assert.match(textOut.text, /^Prompt: prompts\/place_order\.prompt\.md$/m);
  assert.match(textOut.text, /^Prompt: prompts\/menu\.prompt\.md$/m);
  assert.match(textOut.text, /^Prompt: prompts\/daemon\.prompt\.md \(native-only\)$/m);
  assert.doesNotMatch(textOut.text, /no single Runtime interface/);

  const jsonOut = sink(), jsonErr = sink();
  assert.equal(await runPdd(['files', '--json'], { cwd: setup.repo, env: { HOME: setup.home, PDD_STATE_DIR: setup.state }, stdout: jsonOut, stderr: jsonErr }), 0, jsonErr.text);
  const view = JSON.parse(jsonOut.text);
  assert.deepEqual(view.refusals, []);
  const placeRow = view.prompts.find(row => row.path === PLACE);
  assert.equal(placeRow.has_interface, false);
  assert.deepEqual(view.tests.find(row => row.path === 'tests/place-order.json').prompts, ['prompts/menu.prompt.md', PLACE]);
  const daemonRow = view.prompts.find(row => row.path === 'prompts/daemon.prompt.md');
  assert.equal(daemonRow.native_only, true);

  // 2) pdd test --files captures transitive Markdown prompt dependency
  const captured = captureSource(setup.repo, { tests: ['tests/place-order.json'] });
  assert.ok(captured.files.some(file => file.path === 'prompts/menu.prompt.md'), 'transitive plain prompt dependency must be captured');

  // 3) pdd lint --local exits 0 with zero interface-missing findings
  const lintOut = sink(), lintErr = sink();
  assert.equal(await runPdd(['lint', '--local', '--json'], { cwd: setup.repo, env: { HOME: setup.home, PDD_STATE_DIR: setup.state }, stdout: lintOut, stderr: lintErr }), 0, lintErr.text);
  assert.deepEqual(JSON.parse(lintOut.text).problems, []);

  // 4) whyNoTests does not blame plain .prompt.md files
  const emptyRepo = temp(t);
  mkdirSync(join(emptyRepo, 'prompts'), { recursive: true });
  writeFileSync(join(emptyRepo, 'prompts/plain.prompt.md'), '# Plain\n\nNo embedded block.\n');
  git(emptyRepo, 'init', '-q');
  git(emptyRepo, 'add', '-A');
  const lines = whyNoTests(emptyRepo, ['prompts/plain.prompt.md'], { untested: [], orphans: [] });
  assert.deepEqual(lines, []);
});

test('3367 approve: records plain Markdown and frontmatter native-only approvals in journal without mutating prompt files', async t => {
  const plainText = '# Plain prompt\n\nCompute total cents from items.\n';
  const nativeText = '---\nkind: native-only\nreason: Reads hardware USB HID descriptor.\n---\n\n# USB reader\n\nRead frames.\n';
  const setup = harbor(t, repo => {
    writeFileSync(join(repo, 'prompts/plain.prompt.md'), plainText);
    writeFileSync(join(repo, 'prompts/usb.prompt.md'), nativeText);
  });
  const firstCommit = git(setup.repo, 'rev-parse', '--short=12', 'HEAD');

  const approveInteractive = async (path, answer = 'y') => {
    const stdout = sink(), stderr = sink();
    const code = await runApprove({ words: [path], cwd: setup.repo }, {
      stdout, stderr, stdin: Readable.from([`${answer}\n`]), interactive: true,
    });
    return { code, out: stdout.text, err: stderr.text };
  };

  // Interactive approval of plain prompt does not mutate file on disk
  const res1 = await approveInteractive('prompts/plain.prompt.md', 'y');
  assert.equal(res1.code, 0, res1.err);
  assert.match(res1.out, /Approved prompts\/plain\.prompt\.md\./);
  assert.equal(readFileSync(join(setup.repo, 'prompts/plain.prompt.md'), 'utf8'), plainText);

  const journal = JSON.parse(readFileSync(join(setup.repo, '.git/pdd/approvals.json'), 'utf8'));
  assert.equal(journal.approvals.at(-1).prompts[0].path, 'prompts/plain.prompt.md');
  assert.equal(journal.approvals.at(-1).prompts[0].proseSha256, proseSha256(plainText));

  // Immediate re-run sees journaled current approval
  const resAgain = await approveInteractive('prompts/plain.prompt.md', 'y');
  assert.equal(resAgain.code, 0);
  assert.equal(resAgain.out.trim(), 'prompts/plain.prompt.md is already approved and current.');

  // After editing prose, lastApproved resolves firstCommit via journaled proseSha256 and shows diff
  const editedPlain = plainText.replace('Compute total cents', 'Compute subtotal and tax cents');
  writeFileSync(join(setup.repo, 'prompts/plain.prompt.md'), editedPlain);
  const resDiff = await approveInteractive('prompts/plain.prompt.md', 'n');
  assert.equal(resDiff.code, 1);
  assert.ok(resDiff.out.includes(`Text changes since the last approved version (${firstCommit}):`), resDiff.out);
  assert.ok(resDiff.out.includes('+ Compute subtotal and tax cents from items.'), resDiff.out);

  // Frontmatter native-only approval shows reason and leaves file untouched
  const stdout = sink(), stderr = sink();
  const nativeCode = await runApprove(
    { words: ['prompts/usb.prompt.md'], said: 'Approved USB native-only boundary.', cwd: setup.repo },
    { stdout, stderr, interactive: false },
  );
  assert.equal(nativeCode, 0, stderr.text);
  assert.match(stdout.text, /Kind: native-only[\s\S]*Reason: Reads hardware USB HID descriptor\./);
  assert.equal(readFileSync(join(setup.repo, 'prompts/usb.prompt.md'), 'utf8'), nativeText);
});

test('3367 product composition and project card support plain Markdown prompts and refuse native-only tap handlers', t => {
  const baseFiles = JSON.parse(readFileSync(new URL('./runtime/product-compose-try.json', import.meta.url), 'utf8')).initial_world.files;
  const files = structuredClone(baseFiles);
  for (const [path, entry] of Object.entries(files)) {
    if (path.endsWith('.prompt.md')) entry.content = stripEmbeddedInterface(entry.content);
  }
  const ports = {
    root: '/project',
    statFile: path => ({ exists: Object.hasOwn(files, path), is_symlink: false }),
    readFile: path => files[path].content,
  };
  const composed = composeProductTry({ root: '/project' }, ports);
  assert.equal(composed.files[0].path, composed.appMapPath);
  assert.equal(composed.files[1].path, composed.seedPath);

  // Refuses frontmatter native-only and malformed frontmatter prompts as After every tap handler
  const serverKey = Object.keys(files).find(key => key.endsWith('.prompt.md') && !key.includes('phone'));
  assert.ok(serverKey);
  for (const header of [
    '---\nkind: native-only\nreason: Raw socket.\n---\n\n',
    '---\nkind: full\n---\n\n',
    '---\nkind: native-only\n---\n\n',
    '---\nkind: native-only\nreason: Unclosed\n',
  ]) {
    const badFiles = structuredClone(files);
    badFiles[serverKey].content = `${header}${badFiles[serverKey].content}`;
    assert.throws(
      () => composeProductTry({ root: '/project' }, {
        root: '/project',
        statFile: path => ({ exists: Object.hasOwn(badFiles, path), is_symlink: false }),
        readFile: path => badFiles[path].content,
      }),
      err => err.code === 'invalid-product-map',
      header,
    );
  }

  // productTapCallBound walks plain Markdown prompt links, rejects malformed/native-only frontmatter, and rejects cycles
  const tapFiles = {
    '/project/prompts/draw.prompt.md': '# Draw\n\nRender main screen.\n',
    '/project/prompts/tap.prompt.md': '# Tap\n\nHandle tap.\n\n## Dependencies\n\n- [Child](child.prompt.md)\n',
    '/project/prompts/child.prompt.md': '# Child\n\nCompute next state.\n',
  };
  const map = {
    screens: [{ id: 'main', prompt_path: 'prompts/draw.prompt.md', operation: 'draw', source: 'operation' }],
    handlers: [{ screen: 'main', handler: { prompt_path: 'prompts/tap.prompt.md', operation: 'tap' }, input: {}, next: { kind: 'same' }, after: [] }],
  };
  for (const badChild of [
    '---\nkind: native-only\nreason: Raw socket.\n---\n\n# Child\n\nCompute.\n',
    '---\nkind: full\n---\n\n# Child\n\nCompute.\n',
    '---\nkind: native-only\n---\n\n# Child\n\nCompute.\n',
  ]) {
    const badTapFiles = { ...tapFiles, '/project/prompts/child.prompt.md': badChild };
    assert.throws(
      () => productTapCallBound(map, {
        root: '/project',
        statFile: p => ({ exists: Object.hasOwn(badTapFiles, p), is_symlink: false }),
        readFile: p => badTapFiles[p],
      }),
      err => err.code === 'invalid-product-map',
      badChild,
    );
  }
  const bound = productTapCallBound(map, {
    root: '/project',
    statFile: p => ({ exists: Object.hasOwn(tapFiles, p), is_symlink: false }),
    readFile: p => tapFiles[p],
  });
  assert.equal(typeof bound, 'number');
  assert.ok(bound >= 2);
  tapFiles['/project/prompts/child.prompt.md'] += '\n## Dependencies\n\n- [Tap](tap.prompt.md)\n';
  assert.throws(
    () => productTapCallBound(map, {
      root: '/project',
      statFile: p => ({ exists: Object.hasOwn(tapFiles, p), is_symlink: false }),
      readFile: p => tapFiles[p],
    }),
    err => err.code === 'invalid-product-map' && /recursive/.test(err.message),
  );

  // buildProjectCard treats plain prompt with passing check as ready for Make the code (PR 2)
  const setup = harbor(t, repo => {
    writeFileSync(join(repo, PLACE), stripEmbeddedInterface(readFileSync(join(repo, PLACE), 'utf8')));
  });
  const batchId = '20990101-000000-abcd';
  const batchDir = join(setup.state, 'batches', batchId);
  mkdirSync(batchDir, { recursive: true });
  writeFileSync(join(batchDir, 'summary.json'), JSON.stringify({
    repo: setup.repo,
    summary_line: 'Runtime check: 2/2 pass',
    rows: [{ story: 'place-order', state: 'passed', criteria: { passed: 3, total: 3 } }],
  }));
  writeFileSync(join(batchDir, 'batch.json'), JSON.stringify({
    created_at: '2099-01-01T00:00:00.000Z',
    rows: [{ test: 'tests/place-order.json' }],
    source_sha256: captureSource(setup.repo, { tests: ['tests/place-order.json'] }).sha256,
  }));
  const card = buildProjectCard({ root: setup.repo, env: { HOME: setup.home, PDD_STATE_DIR: setup.state }, story: 'place-order' });
  assert.match(card.nextStep, /Make the code/);

  // Leading YAML frontmatter does not hide title/opening sentence in promptClaims, lintLocalHygiene or buildProjectCard
  const fmPrompt = '---\nkind: native-only\nreason: Spawns child PTY.\n---\n\n# Daemon runner\n\nOwn `src/daemon.mjs`.\n';
  assert.deepEqual(promptClaims('prompts/daemon.prompt.md', fmPrompt), ['src/daemon.mjs']);
  writeFileSync(join(setup.repo, 'prompts/daemon.prompt.md'), fmPrompt);
  writeFileSync(join(setup.repo, 'prompts/bad-test-owner.prompt.md'), '---\nkind: native-only\nreason: Bad owner.\n---\n\n# Bad\n\nOwn `test/daemon.test.mjs`.\n');
  git(setup.repo, 'add', 'prompts/daemon.prompt.md', 'prompts/bad-test-owner.prompt.md');
  const hygiene = lintLocalHygiene({ root: setup.repo });
  assert.ok(hygiene.some(line => line.includes('misplaced prompt owner: prompts/bad-test-owner.prompt.md claims test/daemon.test.mjs')), JSON.stringify(hygiene));
  const fmCard = buildProjectCard({ root: setup.repo, env: { HOME: setup.home, PDD_STATE_DIR: setup.state }, story: 'place-order' });
  assert.match(fmCard.text, /Prompt prompts\/daemon\.prompt\.md \(Daemon runner\): Own `src\/daemon\.mjs`\./);
  assert.doesNotMatch(fmCard.text, /kind: native-only/);
});

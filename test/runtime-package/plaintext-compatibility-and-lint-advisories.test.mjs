import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck, runTry, proseSha256 } from '../../src/runtime-seam.mjs';
import { client, BUILD, TEST } from './runtime-compatibility/replay.mjs';
import { harbor, portsFor, storyTest, PLACE, TOKEN } from './runtime-fake.mjs';

test('issue3237 AC1/AC2: pdd test prints one-line compatibility summary by default, full JSON with --details, and unchanged --json', async t => {
  const c = await client(t, {
    edit(repo) {
      const testPath = join(repo, TEST);
      const doc = JSON.parse(readFileSync(testPath, 'utf8'));
      const baseStep = structuredClone(doc.steps[0]);
      doc.steps = [
        { ...structuredClone(baseStep), step_id: 'sam-orders-espressos-and-muffin' },
        { ...structuredClone(baseStep), step_id: 'alex-orders-latte' },
        { ...structuredClone(baseStep), step_id: 'dana-orders-drip' },
      ];
      writeFileSync(testPath, JSON.stringify(doc, null, 2));
    },
  });

  const plain = await c.run('check', { '--json': false });
  assert.equal(plain.code, 0, plain.err);
  const expectedSummary = `Compatibility (${TEST}): supported (association matched); 3 steps (3 operations, 0 edges); execution ordinary; resources simulated; complete true; engine ${BUILD.slice(0, 12)}.`;
  const expectedAdvice = '  Client advice (application author): Behavioral execution remains required. Installed-engine, host/profile and physical-observation proof remains unproved.';
  assert.ok(plain.out.split('\n').includes(expectedSummary), `expected 1-line summary in stdout:\n${plain.out}`);
  assert.ok(plain.out.split('\n').includes(expectedAdvice), `expected readable client advice in stdout:\n${plain.out}`);
  assert.ok(!plain.out.includes(`Compatibility (${TEST}): {`), 'default pdd test must not dump multiline compatibility JSON');
  assert.ok(!plain.out.includes('  Client advice: {'), 'default pdd test must not dump raw client_advice JSON');

  const json = await c.run('check', { '--json': true });
  assert.equal(json.code, 0, json.err);
  assert.equal(json.json.rows[0].compatibility.state, 'supported');
  assert.equal(json.json.rows[0].compatibility.association, 'matched');
  assert.equal(json.json.rows[0].compatibility.reported.operations.length, 3);
  assert.deepEqual(json.json.rows[0].client_advice, {
    owner: 'application author',
    next_step: 'Behavioral execution remains required. Installed-engine, host/profile and physical-observation proof remains unproved.',
  });

  const detailed = await c.run('check', { '--json': false, '--details': true });
  assert.equal(detailed.code, 0, detailed.err);
  assert.ok(
    detailed.out.includes(`Compatibility (${TEST}): ${JSON.stringify(json.json.rows[0].compatibility, null, 2)}`),
    'pdd test --details must print full pretty-printed compatibility JSON',
  );
  assert.ok(
    detailed.out.includes(`  Client advice: ${JSON.stringify(json.json.rows[0].client_advice)}`),
    'pdd test --details must print compact client_advice JSON',
  );
});

test('issue3237 AC3: pdd lint prints warning-only diagnostics under Lint advisories, summarizes compatibility on one line, and exits 0', async t => {
  const warningText = 'The AI cannot compute a hash. Declare a compute resource with hash_json or hash_utf8, or keep this criterion in native tests.';
  const c = await client(t, {
    lintEdit(answer) {
      answer.result.problems = [
        {
          code: 'needs-hash-tool',
          path: PLACE,
          section: 'Runtime interface',
          message: `${warningText} ${TOKEN} /srv/private/secret`,
          severity: 'warning',
        },
      ];
    },
  });

  const plain = await c.run('lint', { '--json': false });
  assert.equal(plain.code, 0, plain.err);
  assert.ok(
    plain.out.includes('Lint advisories (from the PDD interpreter):\n  needs-hash-tool  prompts/place_order.prompt.md  Runtime interface  The AI cannot compute a hash.'),
    `expected Lint advisories heading in stdout:\n${plain.out}`,
  );
  assert.ok(!plain.out.includes('Lint problems'), `warning-only lint must not print Lint problems:\n${plain.out}`);
  assert.ok(
    plain.out.includes(`Compatibility (place-order / ${TEST}): supported (association matched); 1 step (1 operation, 0 edges); execution ordinary; resources simulated; complete true; engine ${BUILD.slice(0, 12)}.`),
    `expected one-line lint compatibility summary:\n${plain.out}`,
  );
  assert.ok(!plain.out.includes(`Compatibility (place-order / ${TEST}): {`), 'plain-text pdd lint must not dump multiline compatibility JSON');
  assert.ok(!plain.out.includes(TOKEN) && !plain.out.includes('/srv/private'), 'advisory output must redact tokens and server paths');

  const json = await c.run('lint', { '--json': true });
  assert.equal(json.code, 0, json.err);
  assert.equal(json.json.problems.length, 1);
  assert.equal(json.json.problems[0].code, 'needs-hash-tool');
  assert.equal(json.json.problems[0].severity, 'warning');
  assert.equal(json.json.rows[0].compatibility.state, 'supported');

  const savedPlain = await c.run('check', { '--read': json.json.batch, '--json': false }, []);
  assert.equal(savedPlain.code, 0, savedPlain.err);
  assert.ok(savedPlain.out.includes('Lint advisories (from the PDD interpreter):'));
  assert.ok(!savedPlain.out.includes('Lint problems'));
  assert.ok(savedPlain.out.includes(`Compatibility (place-order / ${TEST}): supported (association matched); 1 step (1 operation, 0 edges);`));
});

test('issue3237 AC4: interpreter and local lint print blocking problems ahead of advisories and keep warning-only local reads non-refused', async t => {
  const c = await client(t, {
    lintEdit(answer) {
      answer.state = 'refused';
      answer.result.report.lint.tests[0].verdict = 'refused';
      answer.result.refusals = [{ code: 'interface-stale', file: PLACE, section: 'Runtime interface', message: 'prompts/place_order.prompt.md changed after its hash was filled or approved.' }];
      answer.result.problems = [
        {
          code: 'needs-hash-tool',
          path: PLACE,
          section: 'Runtime interface',
          message: 'The AI cannot compute a hash. Declare a compute resource with hash_json or hash_utf8, or keep this criterion in native tests.',
          severity: 'warning',
        },
        {
          code: 'interface-stale',
          path: PLACE,
          section: 'Runtime interface',
          message: 'prompts/place_order.prompt.md changed after its hash was filled or approved.',
          severity: 'error',
        },
      ];
    },
  });

  const serverOut = await c.run('lint', { '--json': false });
  assert.equal(serverOut.code, 4, serverOut.err);
  const serverProblemsIdx = serverOut.out.indexOf('Lint problems (from the PDD interpreter):');
  const serverAdvisoriesIdx = serverOut.out.indexOf('Lint advisories (from the PDD interpreter):');
  assert.ok(serverProblemsIdx >= 0, `expected Lint problems heading:\n${serverOut.out}`);
  assert.ok(serverAdvisoriesIdx > serverProblemsIdx, `expected Lint problems ahead of Lint advisories:\n${serverOut.out}`);

  // Exercise localOnly printLintResult via a native-only repository with local findings and saved --read.
  const h = harbor(t, repo => {
    let nativePrompt = '# Kernel\n\n<details><summary>Runtime interface</summary>\n\n```json\n'
      + JSON.stringify({ kind: 'native-only', reason: 'filesystem lock semantics', status: 'draft', prose_sha256: '' })
      + '\n```\n</details>\n';
    nativePrompt = nativePrompt.replace('"prose_sha256":""', `"prose_sha256":"${proseSha256(nativePrompt)}"`);
    writeFileSync(join(repo, 'prompts/kernel.prompt.md'), nativePrompt);
    storyTest(repo, 'kernel');
    const kernelTestPath = join(repo, 'tests/kernel.json');
    const kernelDoc = JSON.parse(readFileSync(kernelTestPath, 'utf8'));
    kernelDoc.steps[0].entry_path = 'prompts/kernel.prompt.md';
    writeFileSync(kernelTestPath, JSON.stringify(kernelDoc, null, 2));
    writeFileSync(join(repo, 'prompts/helper.prompt.md'), '# Helper without interface\n');
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: 'https://example.invalid' };
  const initialJsonPorts = portsFor(env);
  const initialCode = await runCheck({ cwd: h.repo, words: [], options: { '--lint': true, '--json': true } }, initialJsonPorts.ports);
  assert.equal(initialCode, 4, initialJsonPorts.ports.stderr.text);
  const savedSummary = JSON.parse(initialJsonPorts.ports.stdout.text);

  // Inject an advisory alongside the local blocking finding in the saved local_only batch and read in plain text.
  const batchPath = join(h.state, 'batches', savedSummary.batch, 'batch.json');
  const savedBatch = JSON.parse(readFileSync(batchPath, 'utf8'));
  savedBatch.lint.problems = [
    {
      code: 'interface-kind-explicit-full',
      path: PLACE,
      section: '/kind',
      message: 'Omit redundant "kind": "full" on draft interfaces.',
      severity: 'warning',
    },
    ...savedBatch.lint.problems,
  ];
  writeFileSync(batchPath, JSON.stringify(savedBatch, null, 2));

  const mixedLocalPorts = portsFor(env);
  const mixedLocalCode = await runCheck({ cwd: h.repo, words: [savedSummary.batch], options: { '--read': true } }, mixedLocalPorts.ports);
  assert.equal(mixedLocalCode, 4, mixedLocalPorts.ports.stderr.text);
  const localProblemsIdx = mixedLocalPorts.ports.stdout.text.indexOf('Local lint problems:');
  const localAdvisoriesIdx = mixedLocalPorts.ports.stdout.text.indexOf('Local lint advisories:');
  assert.ok(localProblemsIdx >= 0, `expected Local lint problems heading:\n${mixedLocalPorts.ports.stdout.text}`);
  assert.ok(localAdvisoriesIdx > localProblemsIdx, `expected Local lint problems ahead of Local lint advisories:\n${mixedLocalPorts.ports.stdout.text}`);

  // When only warning-severity advisories remain in localOnly mode with no refused rows, exit code is not forced to 4.
  savedBatch.lint.problems = savedBatch.lint.problems.filter(item => item.severity === 'warning');
  writeFileSync(batchPath, JSON.stringify(savedBatch, null, 2));
  const warningOnlyLocalPorts = portsFor(env);
  const warningOnlyLocalCode = await runCheck({ cwd: h.repo, words: [savedSummary.batch], options: { '--read': true } }, warningOnlyLocalPorts.ports);
  assert.notEqual(warningOnlyLocalCode, 4, 'warning-only local advisories must not force exit 4');
  assert.ok(warningOnlyLocalPorts.ports.stdout.text.includes('Local lint advisories:'));
  assert.ok(!warningOnlyLocalPorts.ports.stdout.text.includes('Local lint problems:'));
});

test('issue3237 AC2: pdd simulate (runTry) not-run lint stderr prints one-line compatibility summary and readable client advice', async t => {
  const c = await client(t, { variant: 'source-mismatch' });
  const p = portsFor(c.env, { openUrl: async () => true });
  const exitCode = await runTry({ cwd: c.h.repo, words: ['place-order'], options: { '--no-open': true, '--no-wait': true } }, p.ports);
  assert.equal(exitCode, 5);
  const expectedLine = `Compatibility (${TEST}): unknown (association mismatch); 1 step (1 operation, 0 edges); execution ordinary; resources simulated; complete true; engine ${BUILD.slice(0, 12)}; issue capability-association-mismatch.`;
  const expectedAdvice = '  Client advice (unresolved): Review captured source and interpreter deployment identity.';
  assert.ok(p.ports.stderr.text.includes(expectedLine), `expected one-line compatibility summary on stderr:\n${p.ports.stderr.text}`);
  assert.ok(p.ports.stderr.text.includes(expectedAdvice), `expected readable client advice on stderr:\n${p.ports.stderr.text}`);
  assert.ok(!p.ports.stderr.text.includes(`Compatibility (${TEST}): {`), 'Try not-run stderr must not dump multiline compatibility JSON');
});

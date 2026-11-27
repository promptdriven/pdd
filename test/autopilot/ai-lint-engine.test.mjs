import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import {
  MAX_AI_LINT_FINDINGS,
  applyVerifierDecisions,
  collectLinkedManifest,
  loadBaseTrustedReviewScope,
  normalizeQuoteText,
  rankAndCapFindings,
  runAdaptiveAiLint,
  selectReviewChecklists,
  verifyCandidateFindings,
  verifyQuoteOnDisk,
} from '../../src/autopilot/ai-lint-engine.mjs';
import { parseArgv, CommandInputError } from '../../src/argument-parser.mjs';
import { renderHelp, runPdd } from '../../src/pdd-cli.mjs';

const sink = () => {
  let text = '';
  return { write(chunk) { text += String(chunk); return true; }, get text() { return text; } };
};

function writeRepoFile(repo, rel, content) {
  const full = join(repo, rel);
  mkdirSync(dirname(full), { recursive: true });
  writeFileSync(full, content, 'utf8');
}

function initGitRepo(repo) {
  const gitEnv = {
    ...process.env,
    GIT_AUTHOR_NAME: 'Test',
    GIT_AUTHOR_EMAIL: 'test@example.com',
    GIT_COMMITTER_NAME: 'Test',
    GIT_COMMITTER_EMAIL: 'test@example.com',
  };
  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: repo, env: gitEnv });
  execFileSync('git', ['add', '.'], { cwd: repo, env: gitEnv });
  execFileSync('git', ['commit', '-q', '-m', 'init'], { cwd: repo, env: gitEnv });
  return gitEnv;
}

function makeTempRepo(t, prefix = 'pdd-ai-lint-engine-') {
  const scratch = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  mkdirSync(repo, { recursive: true });
  mkdirSync(home, { recursive: true });
  return { scratch, repo, home, env: { PATH: process.env.PATH, HOME: home } };
}

test('ai-lint-engine: no-cap linked-file manifest collects >10 neighbors, reverse links, contracts, Stories, scenarios, tests, drawings, and graph facts', t => {
  const { repo } = makeTempRepo(t, 'pdd-ai-manifest-');

  // Create 8 outgoing neighbor prompts (exceeds old 4-file cap), plus 3 incoming reverse linkers,
  // 1 shared contract, 1 paired Story, 1 scenario JSON, 1 native test, 1 .ui.svg drawing, and a cycle + native-only layering violation!
  const outLinks = [];
  for (let i = 1; i <= 8; i += 1) {
    writeRepoFile(repo, `prompts/dep-${i}.prompt.md`, `# Dep ${i}\n\nProvides helper ${i}.\n\n## Dependencies\n\nNone.\n`);
    outLinks.push(`- [dep-${i}](dep-${i}.prompt.md)`);
  }
  writeRepoFile(repo, 'prompts/adapter.prompt.md', '---\nkind: native-only\nreason: Native DB adapter.\n---\n\n# Adapter\n\n## Ports\n\n- `store.write`\n\n## Dependencies\n\n- [hub](hub.prompt.md)\n');
  writeRepoFile(repo, 'contracts/order.md', '# Order Contract\n\nShared schema for orders.\n');
  writeRepoFile(repo, 'views/hub.ui.svg', '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 200 100"><title>Hub</title></svg>\n');
  writeRepoFile(repo, 'prompts/hub.prompt.md', [
    '# Hub',
    '',
    'Own `src/hub.mjs`. Render ![Hub UI](../views/hub.ui.svg).',
    'Follow [order contract](../contracts/order.md).',
    '',
    '## Dependencies',
    '',
    ...outLinks,
    '- [adapter](adapter.prompt.md)',
    '',
  ].join('\n'));
  writeRepoFile(repo, 'src/hub.mjs', '// Prompt: prompts/hub.prompt.md\n\nexport const hub = () => "ok";\n');
  for (let j = 1; j <= 3; j += 1) {
    writeRepoFile(repo, `prompts/caller-${j}.prompt.md`, `# Caller ${j}\n\nCalls hub.\n\n## Dependencies\n\n- [hub](hub.prompt.md)\n`);
  }
  writeRepoFile(repo, 'user_stories/hub-flow.md', '# Hub flow\n\nAs an operator, I want hub to run.\n\n## Acceptance criteria\n\n1. Hub returns ok.\n');
  writeRepoFile(repo, 'tests/hub-flow.json', JSON.stringify({ entry_path: 'prompts/hub.prompt.md', steps: [] }, null, 2));
  writeRepoFile(repo, 'test/hub.test.mjs', 'import test from "node:test";\n// tests prompts/hub.prompt.md\ntest("hub", () => {});\n');

  initGitRepo(repo);

  const allowedFiles = [
    ...Array.from({ length: 8 }, (_, i) => `prompts/dep-${i + 1}.prompt.md`),
    'prompts/adapter.prompt.md',
    'contracts/order.md',
    'views/hub.ui.svg',
    'prompts/hub.prompt.md',
    'src/hub.mjs',
    'prompts/caller-1.prompt.md',
    'prompts/caller-2.prompt.md',
    'prompts/caller-3.prompt.md',
    'user_stories/hub-flow.md',
    'tests/hub-flow.json',
    'test/hub.test.mjs',
  ].sort();

  const hubRaw = readFileSync(join(repo, 'prompts/hub.prompt.md'), 'utf8');
  const { manifest, graphFacts } = collectLinkedManifest({
    realRoot: repo,
    allowedFiles,
    targets: [{ path: 'prompts/hub.prompt.md', kind: 'prompt', raw: hubRaw, lines: 20, isNew: false, nativeOnly: false }],
  });

  // Zero arbitrary 4-file cap: all 8 dep prompts + adapter + contract + svg are in outgoing_links!
  assert.equal(manifest.outgoing_links.length, 11, `expected all 11 outgoing links, got ${manifest.outgoing_links.length}`);
  assert.equal(manifest.incoming_links.length, 4, 'all 3 callers + adapter reverse-link to hub');
  assert.deepEqual(manifest.contracts, ['contracts/order.md']);
  assert.deepEqual(manifest.svg_drawings, ['views/hub.ui.svg']);
  assert.deepEqual(manifest.paired_stories, ['user_stories/hub-flow.md']);
  assert.deepEqual(manifest.paired_scenarios, ['tests/hub-flow.json']);
  assert.deepEqual(manifest.paired_tests, ['test/hub.test.mjs']);
  assert.deepEqual(manifest.owned_code, ['src/hub.mjs']);
  assert.ok(manifest.all_linked.length >= 17, `unbounded all_linked expected >= 17, got ${manifest.all_linked.length}`);

  // Graph facts: cycle hub <-> adapter AND checkable -> native-only layering violation detected
  assert.equal(graphFacts.cycles.length, 1);
  assert.deepEqual(graphFacts.cycles[0], ['prompts/adapter.prompt.md', 'prompts/hub.prompt.md', 'prompts/adapter.prompt.md']);
  assert.deepEqual(graphFacts.layering_violations, [{
    from: 'prompts/hub.prompt.md',
    to: 'prompts/adapter.prompt.md',
    rule: 'checkable-depends-on-native-only',
  }]);
  assert.deepEqual(graphFacts.native_only_targets, ['prompts/adapter.prompt.md']);
});

test('ai-lint-engine: adaptive checklist router picks exact checklists (design ONLY on new or >350 lines, never normal edits)', () => {
  // 1. Plain existing small standalone prompt -> ONLY contract (NO interfaces, trace, abuse, design)
  const plainTarget = {
    path: 'prompts/greet.prompt.md',
    kind: 'prompt',
    raw: '# Greet\n\nReturn "hello" for a name.\n\n## Dependencies\n\nNone.\n',
    lines: 7,
    isNew: false,
    nativeOnly: false,
  };
  const plain = selectReviewChecklists({
    mode: 'adaptive',
    targets: [plainTarget],
    manifest: { outgoing_links: [], incoming_links: [], contracts: [], paired_stories: [], paired_scenarios: [], paired_tests: [] },
    graphFacts: { native_only_targets: [] },
  });
  assert.deepEqual(plain.checklists, ['contract']);

  // 2. Existing small prompt with money + ports + outgoing links + paired Story -> contract, interfaces, trace, abuse (still NO design!)
  const richTarget = {
    path: 'prompts/billing.prompt.md',
    kind: 'prompt',
    raw: '# Billing\n\nCharge invoice fee via `ledger.post`.\n\n## Ports\n\n- `ledger.post`\n',
    lines: 45,
    isNew: false,
    nativeOnly: false,
  };
  const rich = selectReviewChecklists({
    mode: 'adaptive',
    targets: [richTarget],
    manifest: { outgoing_links: ['prompts/tax.prompt.md'], incoming_links: [], contracts: [], paired_stories: ['user_stories/bill.md'], paired_scenarios: [], paired_tests: [] },
    graphFacts: { native_only_targets: [] },
  });
  assert.deepEqual(rich.checklists, ['contract', 'interfaces', 'trace', 'abuse']);
  assert.ok(rich.reasons.abuse.includes('ports'));
  assert.ok(rich.reasons.abuse.includes('money_pricing'));

  // 3. Brand-new prompt -> adds design
  const newRes = selectReviewChecklists({
    mode: 'adaptive',
    targets: [{ ...plainTarget, isNew: true }],
    manifest: {},
    graphFacts: {},
  });
  assert.deepEqual(newRes.checklists, ['contract', 'design']);

  // 4. Existing huge prompt (> 350 lines) -> adds design
  const hugeRes = selectReviewChecklists({
    mode: 'adaptive',
    targets: [{ ...plainTarget, isNew: false, lines: 351 }],
    manifest: {},
    graphFacts: {},
  });
  assert.deepEqual(hugeRes.checklists, ['contract', 'design']);

  // 5. Existing 350-line prompt (not > 350) -> does NOT trigger design
  const boundaryRes = selectReviewChecklists({
    mode: 'adaptive',
    targets: [{ ...plainTarget, isNew: false, lines: 350 }],
    manifest: {},
    graphFacts: {},
  });
  assert.deepEqual(boundaryRes.checklists, ['contract']);

  // 6. single and single-verify modes ALWAYS select ONLY contract
  for (const mode of ['single', 'single-verify']) {
    const res = selectReviewChecklists({
      mode,
      targets: [{ ...richTarget, isNew: true, lines: 500 }],
      manifest: { outgoing_links: ['a.md'], paired_stories: ['b.md'] },
      graphFacts: { native_only_targets: ['a.md'] },
    });
    assert.deepEqual(res.checklists, ['contract']);
  }
});

test('ai-lint-engine: normalized verbatim quote verifier handles smart quotes, collapsed whitespace, shifted lines, full-file fallback, and cross-file both-side verification', t => {
  const { repo } = makeTempRepo(t, 'pdd-ai-quotes-');
  const lines = Array.from({ length: 30 }, (_, i) => `Line ${i + 1} filler prose.`);
  lines[4] = 'Refuse “negative”   amounts with ‘invalid_amount’ and exit 1.';
  lines[24] = 'Timeout ceiling is <= 30 seconds on retry.';
  writeRepoFile(repo, 'prompts/a.prompt.md', `${lines.join('\n')}\n`);
  writeRepoFile(repo, 'prompts/b.prompt.md', '# B\n\nTimeout ceiling is < 30 seconds on retry.\n');

  assert.equal(normalizeQuoteText('  “hello”\t\n‘world’  '), '"hello" \'world\'');

  // Smart quotes + whitespace normalization + shifted hint line (reported line 8, actual line 5)
  const shifted = verifyQuoteOnDisk({
    realRoot: repo,
    relPath: 'prompts/a.prompt.md',
    quote: 'Refuse "negative" amounts with \'invalid_amount\' and exit 1.',
    hintLine: 8,
  });
  assert.equal(shifted.verified, true);
  assert.equal(shifted.matchedLine, 5);
  assert.equal(shifted.matchKind, 'shifted-line');

  // Far-away full-file fallback (reported line 2, actual line 25 -> outside ±10 window)
  const fullFallback = verifyQuoteOnDisk({
    realRoot: repo,
    relPath: 'prompts/a.prompt.md',
    quote: 'Timeout ceiling is <= 30 seconds',
    hintLine: 2,
  });
  assert.equal(fullFallback.verified, true);
  assert.equal(fullFallback.matchedLine, 25);
  assert.equal(fullFallback.matchKind, 'full-file');

  // Cross-file verification: keeps valid pair, drops missing cross_file_quote, fabricated cross_file_quote, same-file interfaces, and fabricated primary quote
  const res = verifyCandidateFindings({
    realRoot: repo,
    candidates: [
      {
        checklist: 'interfaces',
        severity: 'high',
        file: 'prompts/a.prompt.md',
        line: 2,
        quote: 'Timeout ceiling is <= 30 seconds',
        cross_file: 'prompts/b.prompt.md',
        cross_file_line: 1,
        cross_file_quote: 'Timeout ceiling is < 30 seconds',
        message: 'Boundary comparison mismatch (<= vs <).',
        suggestion: 'Align both files on <= 30 seconds.',
      },
      {
        checklist: 'interfaces',
        severity: 'high',
        file: 'prompts/a.prompt.md',
        line: 25,
        quote: 'Timeout ceiling is <= 30 seconds',
        message: 'Missing second-file quote must be dropped.',
        suggestion: 'Cite both files.',
      },
      {
        checklist: 'interfaces',
        severity: 'high',
        file: 'prompts/a.prompt.md',
        line: 25,
        quote: 'Timeout ceiling is <= 30 seconds',
        cross_file: 'prompts/b.prompt.md',
        cross_file_line: 3,
        cross_file_quote: 'FABRICATED QUOTE NOT ON DISK',
        message: 'Unverified cross quote must be dropped.',
        suggestion: 'Verify on disk.',
      },
      {
        checklist: 'interfaces',
        severity: 'high',
        file: 'prompts/a.prompt.md',
        line: 25,
        quote: 'Timeout ceiling is <= 30 seconds',
        cross_file: 'prompts/a.prompt.md',
        cross_file_line: 5,
        cross_file_quote: 'Refuse "negative" amounts',
        message: 'Same file cannot be an interfaces cross-file finding.',
        suggestion: 'Use contract checklist.',
      },
      {
        checklist: 'contract',
        severity: 'medium',
        file: 'prompts/a.prompt.md',
        line: 5,
        quote: 'THIS QUOTE DOES NOT EXIST ANYWHERE',
        message: 'Hallucinated primary quote must be dropped.',
        suggestion: 'Drop it.',
      },
    ],
  });

  assert.equal(res.raw_candidates, 5);
  assert.equal(res.quote_verified, 1);
  assert.equal(res.quote_dropped, 4);
  assert.equal(res.verified[0].line, 25, 'matched line rewritten to exact disk line');
  assert.equal(res.verified[0].cross_file_line, 3, 'cross_file_line rewritten to exact disk line');
});

test('ai-lint-engine: standalone run uses read-only repo access (disableTools: false), fresh second-eyes verifier funnel, 7-cap, advisory exit 0, visible drop counts, and SHA-256 cache', async t => {
  const { repo, env } = makeTempRepo(t, 'pdd-ai-funnel-');
  const bodyLines = Array.from({ length: 12 }, (_, i) => `Rule ${i + 1}: Handle case ${i + 1} with explicit code E${i + 1}.`);
  writeRepoFile(repo, 'prompts/pay.prompt.md', `# Payments\n\nOwn \`src/pay.mjs\`.\n\n## Ports\n\n- \`ledger.post\`\n\n${bodyLines.join('\n')}\n\n## Dependencies\n\n- [tax](tax.prompt.md)\n`);
  writeRepoFile(repo, 'prompts/tax.prompt.md', '# Tax\n\nCompute tax rate in minor units.\n\n## Dependencies\n\nNone.\n');
  writeRepoFile(repo, 'src/pay.mjs', '// Prompt: prompts/pay.prompt.md\n\nexport const pay = () => 0;\n');
  initGitRepo(repo);

  // Build 11 raw candidates: 2 unverified quotes (dropped by quote verifier), 9 verified -> verifier drops 1 -> 8 kept -> cap7 drops 1 -> 7 final!
  const rawFindings = [
    ...Array.from({ length: 9 }, (_, i) => ({
      checklist: i === 0 ? 'abuse' : 'contract',
      severity: i < 3 ? 'high' : 'medium',
      file: 'prompts/pay.prompt.md',
      line: 1, // shifted intentionally; real line is 9+i
      quote: `Rule ${i + 1}: Handle case ${i + 1} with explicit code E${i + 1}.`,
      message: `Real issue ${i + 1} in payment rule.`,
      suggestion: `Fix payment rule ${i + 1}.`,
      ...(i === 0 ? { test_idea: 'Submit negative amount -100; expect error E1 and zero ledger writes.' } : {}),
    })),
    {
      checklist: 'contract',
      severity: 'high',
      file: 'prompts/pay.prompt.md',
      line: 9,
      quote: 'NONEXISTENT HALLUCINATED LINE 1',
      message: 'Fake 1.',
      suggestion: 'Nope.',
    },
    {
      checklist: 'contract',
      severity: 'high',
      file: 'prompts/pay.prompt.md',
      line: 10,
      quote: 'NONEXISTENT HALLUCINATED LINE 2',
      message: 'Fake 2.',
      suggestion: 'Nope.',
    },
  ];

  const calls = [];
  const fakeAgent = async (cmd, args, opts) => {
    calls.push({ cmd, args, cwd: opts.cwd, input: opts.input });
    if (calls.length === 1) {
      return { code: 0, stdout: JSON.stringify({ result: JSON.stringify({ findings: rawFindings }) }), stderr: '' };
    }
    // Pass 2: fresh second-eyes verifier drops C9 as stylistic, keeps C1..C8
    return {
      code: 0,
      stdout: JSON.stringify({
        result: JSON.stringify({
          decisions: [
            ...Array.from({ length: 8 }, (_, i) => ({ id: `C${i + 1}`, verdict: 'keep', reason: 'Verified real flaw.' })),
            { id: 'C9', verdict: 'drop', reason: 'Weak stylistic nitpick.' },
          ],
        }),
      }),
      stderr: '',
    };
  };

  // Run 1: adaptive mode via claude provider -> verify read-only repo access + full funnel + advisory exit 0
  const out1 = sink(), err1 = sink();
  const code1 = await runAdaptiveAiLint(
    { cwd: repo, words: ['prompts/pay.prompt.md'], provider: 'claude', json: true, env },
    { stdout: out1, stderr: err1, runAgentProcess: fakeAgent },
  );
  assert.equal(code1, 0, `AI warnings must be advisory exit 0: ${err1.text}`);
  assert.equal(calls.length, 2, 'adaptive mode invokes Pass 1 + fresh second-eyes verifier Pass 2');
  assert.equal(calls[0].cmd, 'claude');
  assert.equal(calls[0].cwd, repo, 'standalone mode runs in repo root for read-only access (disableTools: false)');
  assert.equal(calls[0].args[calls[0].args.indexOf('--tools') + 1], 'Read,Glob,Grep');
  assert.equal(calls[1].cwd, repo, 'verifier also runs read-only in repo root');

  const json1 = JSON.parse(out1.text);
  assert.equal(json1.schema_version, 'pdd.ai-lint.v2');
  assert.equal(json1.advisory_only, true);
  assert.equal(json1.ai_status, 'ok');
  assert.equal(json1.cached, false);
  assert.deepEqual(json1.checklists, ['contract', 'interfaces', 'abuse']);
  assert.deepEqual(json1.funnel, {
    raw_candidates: 11,
    quote_verified: 9,
    quote_dropped: 2,
    verifier_ran: true,
    verifier_kept: 8,
    verifier_dropped: 1,
    cap7_dropped: 1,
    final_count: MAX_AI_LINT_FINDINGS,
  });
  assert.equal(json1.findings.length, 7);
  assert.equal(json1.findings[0].checklist, 'abuse');
  assert.match(json1.findings[0].test_idea, /negative amount -100/);
  assert.equal(existsSync(join(repo, '.pdd/cache/lint', `${json1.cache_key}.json`)), true);

  // Run 2 (text output, same inputs): hits SHA-256 cache (0 new AI calls!) and prints visible drop counts!
  const out2 = sink(), err2 = sink();
  const code2 = await runAdaptiveAiLint(
    { cwd: repo, words: ['prompts/pay.prompt.md'], provider: 'claude', json: false, env },
    { stdout: out2, stderr: err2, runAgentProcess: fakeAgent },
  );
  assert.equal(code2, 0);
  assert.equal(calls.length, 2, 'identical inputs must hit cache with 0 AI calls');
  assert.match(out2.text, /2 findings dropped \(unverified quote\)/);
  assert.match(out2.text, /1 findings dropped \(second-eyes verifier\)/);
  assert.match(out2.text, /1 findings dropped \(cap 7\)/);
  assert.match(out2.text, /cached/);

  // Run 3: edit linked neighbor tax.prompt.md -> cache invalidates automatically!
  writeRepoFile(repo, 'prompts/tax.prompt.md', '# Tax\n\nCompute tax rate in integer cents (updated).\n\n## Dependencies\n\nNone.\n');
  let callsAfterEdit = 0;
  const out3 = sink();
  const code3 = await runAdaptiveAiLint(
    { cwd: repo, words: ['prompts/pay.prompt.md'], provider: 'claude', json: true, env },
    {
      stdout: out3,
      stderr: sink(),
      runAgentProcess: async () => {
        callsAfterEdit += 1;
        return { code: 0, stdout: JSON.stringify({ result: JSON.stringify({ findings: [] }) }), stderr: '' };
      },
    },
  );
  assert.equal(code3, 0);
  assert.equal(callsAfterEdit, 1, 'editing a linked neighbor must invalidate the SHA-256 cache');
  const json3 = JSON.parse(out3.text);
  assert.notEqual(json3.cache_key, json1.cache_key);
  assert.equal(json3.cached, false);

  // Run 4: PDD_AI_LINT_NO_CACHE=1 skips cache even on identical inputs
  let callsNoCache = 0;
  const code4 = await runAdaptiveAiLint(
    { cwd: repo, words: ['prompts/pay.prompt.md'], provider: 'claude', json: true, env: { ...env, PDD_AI_LINT_NO_CACHE: '1' } },
    {
      stdout: sink(),
      stderr: sink(),
      runAgentProcess: async () => {
        callsNoCache += 1;
        return { code: 0, stdout: JSON.stringify({ result: JSON.stringify({ findings: [] }) }), stderr: '' };
      },
    },
  );
  assert.equal(code4, 0);
  assert.equal(callsNoCache, 1, 'PDD_AI_LINT_NO_CACHE=1 must bypass cache');
});

test('ai-lint-engine: PDD_AI_LINT_MODE arms (single vs single-verify vs adaptive) and PDD_AI_LINT_VERIFY_MIN=1', async t => {
  const { repo, env } = makeTempRepo(t, 'pdd-ai-modes-');
  writeRepoFile(repo, 'prompts/calc.prompt.md', '# Calc\n\nRule one: divide by zero returns null.\n\n## Dependencies\n\nNone.\n');
  initGitRepo(repo);

  const singleFinding = [{
    checklist: 'contract',
    severity: 'medium',
    file: 'prompts/calc.prompt.md',
    line: 3,
    quote: 'Rule one: divide by zero returns null.',
    message: 'Unclear behavior for NaN.',
    suggestion: 'Specify NaN refusal.',
  }];

  // Arm A (single): skips verifier even when >= 2 verified findings exist
  let singleCalls = 0;
  const outA = sink();
  const codeA = await runAdaptiveAiLint(
    { cwd: repo, provider: 'claude', json: true, env: { ...env, PDD_AI_LINT_MODE: 'single', PDD_AI_LINT_NO_CACHE: '1' } },
    {
      stdout: outA,
      stderr: sink(),
      runAgentProcess: async () => {
        singleCalls += 1;
        return { code: 0, stdout: JSON.stringify({ result: JSON.stringify({ findings: [singleFinding[0], { ...singleFinding[0], message: 'Second note.' }] }) }), stderr: '' };
      },
    },
  );
  assert.equal(codeA, 0);
  assert.equal(singleCalls, 1, 'Arm A (single) never invokes verifier');
  assert.equal(JSON.parse(outA.text).funnel.verifier_ran, false);

  // Arm B (single-verify): default verifyMin=2 skips verifier on 1 verified finding; PDD_AI_LINT_VERIFY_MIN=1 invokes verifier on 1 finding!
  let armBDefaultCalls = 0;
  await runAdaptiveAiLint(
    { cwd: repo, provider: 'claude', json: true, env: { ...env, PDD_AI_LINT_MODE: 'single-verify', PDD_AI_LINT_NO_CACHE: '1' } },
    {
      stdout: sink(),
      stderr: sink(),
      runAgentProcess: async () => {
        armBDefaultCalls += 1;
        return { code: 0, stdout: JSON.stringify({ result: JSON.stringify({ findings: singleFinding }) }), stderr: '' };
      },
    },
  );
  assert.equal(armBDefaultCalls, 1, 'verifyMin default 2 skips verifier when only 1 verified finding');

  let armBMin1Calls = 0;
  const outBMin1 = sink();
  await runAdaptiveAiLint(
    { cwd: repo, provider: 'claude', json: true, env: { ...env, PDD_AI_LINT_MODE: 'single-verify', PDD_AI_LINT_VERIFY_MIN: '1', PDD_AI_LINT_NO_CACHE: '1' } },
    {
      stdout: outBMin1,
      stderr: sink(),
      runAgentProcess: async () => {
        armBMin1Calls += 1;
        if (armBMin1Calls === 1) return { code: 0, stdout: JSON.stringify({ result: JSON.stringify({ findings: singleFinding }) }), stderr: '' };
        return { code: 0, stdout: JSON.stringify({ result: JSON.stringify({ decisions: [{ id: 'C1', verdict: 'drop', reason: 'Not a real bug.' }] }) }), stderr: '' };
      },
    },
  );
  assert.equal(armBMin1Calls, 2, 'PDD_AI_LINT_VERIFY_MIN=1 triggers fresh verifier on 1 verified finding');
  const parsedB = JSON.parse(outBMin1.text);
  assert.equal(parsedB.funnel.verifier_ran, true);
  assert.equal(parsedB.funnel.verifier_dropped, 1);
  assert.equal(parsedB.findings.length, 0);

  // Invalid PDD_AI_LINT_MODE fails fast with exit 2
  const badErr = sink();
  const badCode = await runAdaptiveAiLint({ cwd: repo, env: { ...env, PDD_AI_LINT_MODE: 'bogus-arm' } }, { stdout: sink(), stderr: badErr });
  assert.equal(badCode, 2);
  assert.match(badErr.text, /Unsupported PDD_AI_LINT_MODE/);
});

test('ai-lint-engine: fail-visible incomplete/unavailable runs never print green 0 issues and never cache, while offline Tier-0 errors still exit 1', async t => {
  const { repo, env } = makeTempRepo(t, 'pdd-ai-fail-visible-');
  writeRepoFile(repo, 'prompts/ok.prompt.md', '# Ok\n\nOwn `src/ok.mjs`. Return 1.\n\n## Dependencies\n\nNone.\n');
  writeRepoFile(repo, 'src/ok.mjs', '// Prompt: prompts/ok.prompt.md\n\nexport const ok = () => 1;\n');
  initGitRepo(repo);

  // 1. Provider returns unparseable garbage -> NEVER prints "0 advisory findings", prints AI lint incomplete/unavailable, does NOT write cache!
  const outBad = sink(), errBad = sink();
  const codeBad = await runAdaptiveAiLint(
    { cwd: repo, provider: 'claude', json: false, env },
    { stdout: outBad, stderr: errBad, runAgentProcess: async () => ({ code: 0, stdout: 'garbage not json', stderr: '' }) },
  );
  assert.equal(codeBad, 0, 'provider outage stays advisory exit 0 when Tier-0 is clean');
  assert.match(errBad.text, /AI lint incomplete\/unavailable \(claude\)/);
  assert.doesNotMatch(outBad.text, /0 advisory findings|PASS/);
  const cacheDir = join(repo, '.pdd/cache/lint');
  assert.equal(existsSync(cacheDir) ? readdirSync(cacheDir).length : 0, 0, 'failed runs must NEVER be cached');

  // 2. Offline Tier-0 structural error (Story missing ## Acceptance criteria) causes exit 1 even when AI has 0 warnings!
  writeRepoFile(repo, 'user_stories/bad-story.md', '# Bad story\n\nAs a shopper, I forgot the criteria heading.\n');
  const outT0 = sink(), errT0 = sink();
  const codeT0 = await runAdaptiveAiLint(
    { cwd: repo, words: ['user_stories/bad-story.md'], provider: 'claude', json: true, env: { ...env, PDD_AI_LINT_NO_CACHE: '1' } },
    { stdout: outT0, stderr: errT0, runAgentProcess: async () => ({ code: 0, stdout: JSON.stringify({ result: JSON.stringify({ findings: [] }) }), stderr: '' }) },
  );
  assert.equal(codeT0, 1, 'offline Tier-0 structural errors must still exit 1');
  const parsedT0 = JSON.parse(outT0.text);
  assert.equal(parsedT0.ok, false);
  assert.ok(parsedT0.tier0_errors.length >= 1);
});

test('ai-lint-engine: review.scope is read from merge-base pdd.json and ignores untrusted working-tree overrides', t => {
  const { repo } = makeTempRepo(t, 'pdd-ai-scope-');
  writeRepoFile(repo, 'pdd.json', JSON.stringify({ review: { scope: { include: ['prompts/core/**'], exclude: ['prompts/core/skip.prompt.md'] } } }, null, 2));
  writeRepoFile(repo, 'prompts/core/a.prompt.md', '# Core A\n\nRule A.\n\n## Dependencies\n\nNone.\n');
  writeRepoFile(repo, 'prompts/core/skip.prompt.md', '# Skip\n\nSkipped.\n\n## Dependencies\n\nNone.\n');
  writeRepoFile(repo, 'prompts/other/b.prompt.md', '# Other B\n\nRule B.\n\n## Dependencies\n\nNone.\n');
  const gitEnv = initGitRepo(repo);

  // Create feature branch and attempt to widen/clear review.scope in working-tree pdd.json
  execFileSync('git', ['checkout', '-q', '-b', 'feat/tamper'], { cwd: repo, env: gitEnv });
  writeRepoFile(repo, 'pdd.json', JSON.stringify({ review: { scope: { include: ['prompts/other/**'] } } }, null, 2));

  const scope = loadBaseTrustedReviewScope(repo, { baseRef: 'main' });
  assert.ok(scope, 'loads merge-base review.scope');
  assert.deepEqual(scope.include, ['prompts/core/**']);
  assert.deepEqual(scope.exclude, ['prompts/core/skip.prompt.md']);
});

test('ai-lint-engine: CLI strict 2-command UX, hidden plumbing round-trip (--ai-emit-pack -> --ai-emit-verify -> --ai-apply), and legacy --codex compatibility', async t => {
  const { repo, scratch, env } = makeTempRepo(t, 'pdd-ai-cli-');
  writeRepoFile(repo, 'prompts/app.prompt.md', '# App\n\nOwn `src/app.mjs`.\nReturn 400 on blank input.\n\n## Dependencies\n\nNone.\n');
  writeRepoFile(repo, 'src/app.mjs', '// Prompt: prompts/app.prompt.md\n\nexport const app = () => 400;\n');
  initGitRepo(repo);

  // 1. Strict 2-command UX: pdd lint & pdd lint --ai present; NO pdd review, NO --deep, NO --upstream, NO --dismiss
  const rootHelp = renderHelp([]);
  const lintHelp = renderHelp(['lint']);
  assert.match(rootHelp, /pdd lint --ai/);
  assert.match(lintHelp, /pdd lint --ai/);
  for (const forbidden of ['pdd review', '--deep', '--upstream', '--dismiss', '--ai-emit-pack', '--ai-emit-verify', '--ai-apply']) {
    assert.equal(rootHelp.includes(forbidden), false, `root help must not expose ${forbidden}`);
    assert.equal(lintHelp.includes(forbidden), false, `lint help must not expose ${forbidden}`);
  }
  assert.throws(() => parseArgv(['review']), CommandInputError);
  assert.throws(() => parseArgv(['lint', '--ai', '--deep']), CommandInputError);
  assert.throws(() => parseArgv(['lint', '--ai', '--provider', 'agy']), CommandInputError);

  // 2. Hidden plumbing round-trip via runPdd (0 nested CLI calls!)
  const packOut = sink(), packErr = sink();
  const packCode = await runPdd(['lint', '--ai', '--ai-emit-pack', 'prompts/app.prompt.md'], { cwd: repo, env, stdout: packOut, stderr: packErr });
  assert.equal(packCode, 0, packErr.text);
  const pack = JSON.parse(packOut.text);
  assert.equal(pack.schema_version, 'pdd.ai-lint-pack.v1');
  assert.equal(pack.cache_hit, false);
  assert.match(pack.prompt, /Return 400 on blank input/);

  const rawPass1File = join(scratch, 'pass1.json');
  writeFileSync(rawPass1File, JSON.stringify({
    findings: [
      {
        checklist: 'contract',
        severity: 'high',
        file: 'prompts/app.prompt.md',
        line: 4,
        quote: 'Return 400 on blank input.',
        message: 'Does not define non-string input handling.',
        suggestion: 'State behavior for null and non-string input.',
      },
      {
        checklist: 'contract',
        severity: 'low',
        file: 'prompts/app.prompt.md',
        line: 4,
        quote: 'Return 400 on blank input.',
        message: 'Nitpick wording.',
        suggestion: 'Reword.',
      },
      {
        checklist: 'contract',
        severity: 'high',
        file: 'prompts/app.prompt.md',
        line: 4,
        quote: 'FABRICATED QUOTE',
        message: 'Hallucinated.',
        suggestion: 'Drop.',
      },
    ],
  }));

  const verifyOut = sink(), verifyErr = sink();
  const verifyCode = await runPdd(['lint', '--ai', '--ai-emit-verify', rawPass1File, 'prompts/app.prompt.md'], { cwd: repo, env, stdout: verifyOut, stderr: verifyErr });
  assert.equal(verifyCode, 0, verifyErr.text);
  const verifyPack = JSON.parse(verifyOut.text);
  assert.equal(verifyPack.schema_version, 'pdd.ai-lint-verify-pack.v1');
  assert.equal(verifyPack.needs_verify, true);
  assert.equal(verifyPack.funnel.raw_candidates, 3);
  assert.equal(verifyPack.funnel.quote_verified, 2);
  assert.equal(verifyPack.funnel.quote_dropped, 1);

  const applyBundleFile = join(scratch, 'apply.json');
  writeFileSync(applyBundleFile, JSON.stringify({
    candidates: JSON.parse(readFileSync(rawPass1File, 'utf8')).findings,
    verifier: {
      decisions: [
        { id: 'C1', verdict: 'keep', reason: 'Missing null input contract.' },
        { id: 'C2', verdict: 'drop', reason: 'Stylistic nitpick.' },
      ],
    },
  }));

  const applyOut = sink(), applyErr = sink();
  const applyCode = await runPdd(['lint', '--ai', '--ai-apply', applyBundleFile, '--json', 'prompts/app.prompt.md'], { cwd: repo, env, stdout: applyOut, stderr: applyErr });
  assert.equal(applyCode, 0, applyErr.text);
  const applied = JSON.parse(applyOut.text);
  assert.equal(applied.schema_version, 'pdd.ai-lint.v2');
  assert.deepEqual(applied.funnel, {
    raw_candidates: 3,
    quote_verified: 2,
    quote_dropped: 1,
    verifier_ran: true,
    verifier_kept: 1,
    verifier_dropped: 1,
    cap7_dropped: 0,
    final_count: 1,
  });
  assert.equal(applied.findings[0].message, 'Does not define non-string input handling.');

  // Subsequent --ai-emit-pack now reports cache_hit: true!
  const pack2Out = sink();
  assert.equal(await runPdd(['lint', '--ai', '--ai-emit-pack', 'prompts/app.prompt.md'], { cwd: repo, env, stdout: pack2Out, stderr: sink() }), 0);
  assert.equal(JSON.parse(pack2Out.text).cache_hit, true);

  // 3. Conflicting flags fail cleanly with exit 2
  const conflictErr = sink();
  assert.equal(await runPdd(['lint', '--ai', '--codex'], { cwd: repo, env, stdout: sink(), stderr: conflictErr }), 2);
  assert.equal(await runPdd(['lint', '--provider', 'claude'], { cwd: repo, env, stdout: sink(), stderr: sink() }), 2);
  assert.equal(await runPdd(['lint', '--ai-emit-pack', '--ai-apply', applyBundleFile], { cwd: repo, env, stdout: sink(), stderr: sink() }), 2);

  // 4. Legacy --codex still routes to codexLint cleanly
  let legacyCalled = false;
  const legacyCode = await runPdd(
    ['lint', '--codex', '--json', 'prompts/app.prompt.md'],
    { cwd: repo, env, stdout: sink(), stderr: sink(), codexLint: { runCodexLint: async () => { legacyCalled = true; return 0; } } },
  );
  assert.equal(legacyCode, 0);
  assert.equal(legacyCalled, true);

  // Direct unit check on applyVerifierDecisions + rankAndCapFindings helpers
  const dec = applyVerifierDecisions([{ id: 'C1', file: 'a', line: 1, checklist: 'contract', quote: 'q', message: 'm' }], [{ id: 'C1', verdict: 'drop', reason: 'weak' }]);
  assert.equal(dec.verifier_dropped, 1);
  const capped = rankAndCapFindings(Array.from({ length: 9 }, (_, i) => ({
    file: 'a', line: i + 1, checklist: 'contract', severity: 'low', quote: `q${i}`, message: `m${i}`,
  })));
  assert.equal(capped.findings.length, 7);
  assert.equal(capped.cap7_dropped, 2);
});

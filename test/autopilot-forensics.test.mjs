import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  EXTERNAL_REPO_LABELS,
  evaluateForensicsResult,
  extractJsonObjects,
  findConfiguredSkipLabel,
  findExternalRepoLabel,
  codexProviderConfigArgs,
  forensicsCommand,
  forensicsEnvironment,
  formatForensicsBrief,
  formatForensicsComment,
  parseForensicsText,
  runPreRunForensics,
  stripForbiddenIdentifiers,
} from '../src/autopilot-forensics.mjs';
import { coreSettings, coreStatus, readyIssues } from '../src/autopilot-core.mjs';
import { activeIntake, activeReadyCards, nativeFacts, parseCardText, shadowIntake } from '../src/autopilot-intake.mjs';
import { coreWorld } from './helpers/core-world.mjs';

test('external-repo and configured skip labels match case-insensitively with zero path heuristics', () => {
  assert.deepEqual(EXTERNAL_REPO_LABELS, ['external', 'other-repo', 'elsewhere', 'pdd:elsewhere']);
  for (const label of ['external', 'EXTERNAL', ' Other-Repo ', 'Elsewhere', 'PDD:ELSEWHERE']) {
    assert.equal(findExternalRepoLabel([label])?.toLowerCase(), label.trim().toLowerCase());
    const fact = nativeFacts({ number: 1, labels: [{ name: label }] });
    assert.equal(fact?.kind, 'elsewhere');
  }
  assert.equal(findExternalRepoLabel(['bug', 'pdd:autopilot']), null);
  assert.equal(findConfiguredSkipLabel([{ name: 'Needs-Upstream' }], ['needs-upstream']), 'Needs-Upstream');
  assert.equal(
    nativeFacts({ number: 2, labels: ['Vendor-Blocked'] }, { skipLabels: ['vendor-blocked'] })?.kind,
    'held',
  );

  // Default coreSettings shape remains unchanged when optional keys are omitted.
  const defaults = coreSettings({});
  assert.equal(Object.hasOwn(defaults, 'skipLabels'), false);
  assert.equal(Object.hasOwn(defaults, 'forensics'), false);

  const configured = coreSettings({ autopilot: { skipLabels: [' upstream ', 'upstream', ''], forensics: false } });
  assert.deepEqual(configured.skipLabels, ['upstream']);
  assert.equal(configured.forensics, false);
});

test('shadowIntake and activeIntake skip external-repo labels with zero AI jobs and zero path-guessing downgrades', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-intake-ext-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));

  const startedJobs = [];
  const ghCalls = [];
  let trustCalls = 0;
  const jobs = {
    start: spec => { startedJobs.push(spec); return { id: spec.id, pid: startedJobs.length }; },
    read: () => ({ state: 'running', exit: null }),
    stop: () => {},
  };
  const gh = {
    all: async url => { ghCalls.push(url); return []; },
    ok: async (_m, url) => { ghCalls.push(url); return {}; },
  };
  const makeCtx = (root, intake, skipLabels) => ({
    fs: { ...{ existsSync, mkdirSync, readFileSync, rmSync, writeFileSync }, ...t },
    now: () => Date.parse('2026-11-16T12:00:00Z'),
    root,
    repo: 'acme/widgets',
    state: { agent: { kind: 'codex', model: 'gpt-5.4-mini' }, cwd: dir },
    settings: { intake, ...(skipLabels ? { skipLabels } : {}) },
    budget: { state: 'normal' },
    gh,
    jobs,
    ports: {
      trusted: async () => { trustCalls++; return true; },
      agentReady: async () => true,
      env: { HOME: dir },
    },
    warn: () => {},
  });

  const fsMod = await import('node:fs');
  const rows = [
    { number: 1, title: 'External issue', body: 'Touches packages/other/foo.ts', labels: ['External'], comments: 3, user: { login: 'acme' }, created_at: '2026-11-01T00:00:00Z' },
    { number: 2, title: 'Other repo issue', body: 'See other repo', labels: [{ name: 'OTHER-REPO' }], comments: 1, user: { login: 'acme' }, created_at: '2026-11-01T00:01:00Z' },
    { number: 3, title: 'Elsewhere issue', body: 'Wrong tracker', labels: ['elsewhere'], comments: 0, user: { login: 'acme' }, created_at: '2026-11-01T00:02:00Z' },
    { number: 4, title: 'Namespaced elsewhere', body: 'Track elsewhere', labels: ['PDD:Elsewhere'], comments: 2, user: { login: 'acme' }, created_at: '2026-11-01T00:03:00Z' },
    { number: 5, title: 'Custom skip label', body: 'Skip via config', labels: ['Upstream-Only'], comments: 1, user: { login: 'acme' }, created_at: '2026-11-01T00:04:00Z' },
  ];

  const shadowRoot = join(dir, 'shadow');
  await shadowIntake({ ...makeCtx(shadowRoot, 'shadow', ['upstream-only']), fs: fsMod }, rows);
  assert.equal(startedJobs.length, 0, 'zero AI card jobs started in shadowIntake');
  assert.equal(ghCalls.length, 0, 'zero GitHub comment reads for native-skipped labels');
  assert.equal(trustCalls, 0, 'zero trust lookups for native-skipped labels');
  for (const n of [1, 2, 3, 4]) {
    const saved = JSON.parse(readFileSync(join(shadowRoot, 'intake', 'cards', `${n}.json`), 'utf8'));
    assert.equal(saved.native?.kind, 'elsewhere');
  }
  const customSaved = JSON.parse(readFileSync(join(shadowRoot, 'intake', 'cards', '5.json'), 'utf8'));
  assert.equal(customSaved.native?.kind, 'held');

  const activeRoot = join(dir, 'active');
  await activeIntake({ ...makeCtx(activeRoot, 'active', ['upstream-only']), fs: fsMod }, rows);
  assert.equal(startedJobs.length, 0, 'zero AI card jobs started in activeIntake');

  // Verify no path-guessing downgrade exists when a ready card names new/nonexistent paths.
  const parsed = parseCardText('Warning: cache {} empty\n```json\n{"class":"ready","reason":"Create apps/web/new-page.tsx","confidence":0.92,"areas":["apps/web/new-page.tsx"]}\n```');
  assert.equal(parsed?.class, 'ready');
  assert.deepEqual(parsed?.areas, ['apps/web/new-page.tsx']);

  // Verify Claude multiline pretty-printed JSON envelope in shadowIntake card log is harvested cleanly without path downgrades.
  const claudeRoot = join(dir, 'claude-multiline');
  let claudeDone = false;
  const claudeJobs = {
    start: spec => {
      const log = join(spec.dir, `${spec.id}.log`);
      writeFileSync(log, [
        '[claude-cli] hook config {} skipped',
        JSON.stringify({
          type: 'result',
          is_error: false,
          result: '```json\n{\n  "class": "ready",\n  "reason": "Add new route in apps/portal/new-route.tsx with {id} param",\n  "confidence": 0.91,\n  "areas": ["apps/portal/new-route.tsx"]\n}\n```',
        }, null, 2),
      ].join('\n'));
      return { id: spec.id, pid: 99, log };
    },
    read: () => (claudeDone ? { state: 'exited', exit: { code: 0 } } : { state: 'running', exit: null }),
    stop: () => {},
  };
  const claudeRow = [{ number: 6, title: 'Add portal route', body: 'Add apps/portal/new-route.tsx', labels: [], comments: 0, user: { login: 'acme' }, created_at: '2026-11-01T00:05:00Z' }];
  const claudeCtx = {
    ...makeCtx(claudeRoot, 'shadow'),
    fs: fsMod,
    state: { agent: { kind: 'claude', model: 'claude-sonnet-4-6' }, cwd: dir },
    jobs: claudeJobs,
  };
  await shadowIntake(claudeCtx, claudeRow);
  claudeDone = true;
  await shadowIntake(claudeCtx, claudeRow);
  const claudeSaved = JSON.parse(readFileSync(join(claudeRoot, 'intake', 'cards', '6.json'), 'utf8'));
  assert.equal(claudeSaved.card?.class, 'ready');
  assert.deepEqual(claudeSaved.card?.areas, ['apps/portal/new-route.tsx']);
});

test('core readyIssues, claimIssue, and stopReason skip external-repo and configured skipLabels with zero AI calls', async t => {
  const w = await coreWorld(t, { settings: { runs: 2, skipLabels: ['upstream-blocked'] } });
  w.issue(10, { labels: ['pdd:autopilot', 'External'] });
  w.issue(11, { labels: ['pdd:autopilot', 'other-repo'] });
  w.issue(12, { labels: ['pdd:autopilot', 'ELSEWHERE'] });
  w.issue(13, { labels: ['pdd:autopilot', 'pdd:elsewhere'] });
  w.issue(14, { labels: ['pdd:autopilot', 'Upstream-Blocked'] });
  w.issue(15, { labels: ['pdd:autopilot'] });

  const ready = await readyIssues({ state: w.state, settings: w.settings }, w.ports());
  assert.deepEqual(ready, [15]);

  let forensicsCalls = 0;
  await w.tick({
    forensics: async input => {
      forensicsCalls++;
      assert.equal(input.issue.number, 15);
      return { already_fixed: false, summary: 'Still needed.' };
    },
  });
  assert.equal(forensicsCalls, 1, 'forensics ran only on non-skipped issue #15');
  assert.equal(w.started.filter(j => j.role === 'build').length, 1);
  assert.ok(w.job(15, 'build'));
  for (const skipped of [10, 11, 12, 13, 14]) {
    assert.equal(w.job(skipped, 'build'), undefined);
    assert.ok(!w.labels(skipped).includes('pdd:working'));
  }

  // Adding an external-repo label while a build runs stops and cleans up the job on the next tick.
  w.github.issues.get(15).labels.push('elsewhere');
  await w.tick();
  assert.equal(existsSync(join(w.root, 'jobs', '15.json')), false);
});

test('linear brace scanner handles leading warning braces, string braces, multiline Claude envelopes, and deep nesting', () => {
  const tricky = [
    ' CLI warning: fallback config {} loaded for "unclosed quote in prose',
    '```json',
    '{',
    '  "already_fixed": false,',
    '  "summary": "Braces {inside \\"escaped\\" string} stay intact",',
    '  "target_files": ["src/a.mjs"]',
    '}',
    '```',
  ].join('\n');
  const objects = extractJsonObjects(tricky);
  assert.equal(objects.length, 2);
  const parsed = parseForensicsText(tricky);
  assert.equal(parsed?.already_fixed, false);
  assert.match(parsed?.summary ?? '', /Braces \{inside "escaped" string\}/);

  // Multiline pretty-printed Claude JSON envelope
  const claudeMultiline = JSON.stringify({
    type: 'result',
    subtype: 'success',
    is_error: false,
    result: 'Checked repo:\n{\n  "already_fixed": true,\n  "summary": "Fixed on main.",\n  "verifying_files": ["src/x.mjs"],\n  "evidence": "Verified"\n}',
  }, null, 2);
  assert.equal(parseForensicsText(claudeMultiline)?.already_fixed, true);

  // Claude error envelope returns null
  assert.equal(parseForensicsText(JSON.stringify({ type: 'result', is_error: true, result: '{"already_fixed":true}' })), null);

  // Gemini JSON envelope
  const geminiOut = JSON.stringify({ response: '{"already_fixed":false,"summary":"Reproduces in parser"}' });
  assert.equal(parseForensicsText(geminiOut)?.already_fixed, false);

  // Deep nesting stays fast in linear time
  const depth = 4000;
  const deep = `${'{"a":'.repeat(depth)}1${'}'.repeat(depth)}\n{"already_fixed":false,"summary":"fast"}`;
  const t0 = Date.now();
  assert.equal(parseForensicsText(deep)?.summary, 'fast');
  assert.ok(Date.now() - t0 < 500, 'linear scan finishes well under 500ms');
});

test('forensicsCommand and forensicsEnvironment support codex, claude, gemini, and agy in read-only mode without GitHub tokens', async t => {
  const env = forensicsEnvironment({
    HOME: '/tmp/home',
    PATH: '/usr/bin',
    GH_TOKEN: 'ghp_secret1',
    GITHUB_TOKEN: 'ghp_secret2',
    GITHUB_PERSONAL_ACCESS_TOKEN: 'ghp_secret3',
    CODEX_THREAD_ID: 'thread-1',
    OPENAI_API_KEY: 'sk-keep-for-agent',
  });
  assert.equal(env.GH_TOKEN, undefined);
  assert.equal(env.GITHUB_TOKEN, undefined);
  assert.equal(env.GITHUB_PERSONAL_ACCESS_TOKEN, undefined);
  assert.equal(env.CODEX_THREAD_ID, undefined);
  assert.equal(env.OPENAI_API_KEY, 'sk-keep-for-agent');

  const codexCmd = forensicsCommand({ kind: 'codex' }, { model: 'gpt-5.4-mini', resultFile: '/tmp/out.txt' });
  assert.equal(codexCmd.command, 'codex');
  assert.ok(codexCmd.args.includes('read-only'));
  assert.ok(!codexCmd.args.includes('--dangerously-bypass-approvals-and-sandbox'));

  const claudeCmd = forensicsCommand({ kind: 'claude' }, { model: 'claude-sonnet-4-6', reasoningEffort: 'low' });
  assert.equal(claudeCmd.command, 'claude');
  assert.ok(claudeCmd.args.includes('--safe-mode'));
  assert.ok(claudeCmd.args.includes('plan'));
  assert.ok(claudeCmd.args.includes('Read,Glob,Grep'));

  const geminiCmd = forensicsCommand({ kind: 'gemini' }, { model: 'gemini-2.5-flash' });
  assert.equal(geminiCmd.command, 'gemini');
  assert.equal(geminiCmd.args[geminiCmd.args.indexOf('--approval-mode') + 1], 'plan');
  assert.ok(!geminiCmd.args.includes('yolo'));

  const agyCmd = forensicsCommand({ kind: 'agy' }, { model: 'gemini-2.5-flash' });
  assert.equal(agyCmd.command, 'agy');
  assert.equal(agyCmd.args[agyCmd.args.indexOf('--mode') + 1], 'plan');
  assert.ok(agyCmd.args.includes('--sandbox'));
  assert.ok(!agyCmd.args.includes('--dangerously-skip-permissions'));

  assert.throws(() => forensicsCommand({ kind: 'unknown' }), /codex, claude, gemini or agy/);

  // Verify runPreRunForensics works across all 4 agent kinds and cleans up prepareStep overlays even on errors.
  const wt = mkdtempSync(join(tmpdir(), 'pdd-forensics-wt-'));
  t.after(() => rmSync(wt, { recursive: true, force: true }));
  mkdirSync(join(wt, 'src'), { recursive: true });
  writeFileSync(join(wt, 'src', 'app.mjs'), 'export const ok = true;\n');

  for (const kind of ['codex', 'claude', 'gemini', 'agy']) {
    let cleaned = false;
    const res = await runPreRunForensics(
      {
        repo: 'acme/widgets',
        baseBranch: 'main',
        worktree: wt,
        issue: { number: 9, title: 'Bug', body: 'Check src/app.mjs', labels: [] },
        agent: { kind },
        selected: {
          agent: { kind },
          prepareStep: base => ({ env: { ...base, GH_TOKEN: 'strip-me', CUSTOM_OVERLAY: '1' }, cleanup: () => { cleaned = true; } }),
        },
      },
      {
        env: { HOME: wt, PATH: '/usr/bin' },
        run: async (_command, args, opts) => {
          assert.equal(opts.cwd, wt);
          assert.equal(opts.env.GH_TOKEN, undefined);
          assert.equal(opts.env.CUSTOM_OVERLAY, '1');
          const payload = JSON.stringify({
            already_fixed: false,
            summary: `Checked by ${kind}`,
            target_files: ['src/app.mjs', 'src/missing.mjs'],
            reproduction: 'Call ok()',
          });
          if (kind === 'codex') {
            const outIdx = args.indexOf('--output-last-message');
            writeFileSync(args[outIdx + 1], payload);
            return { code: 0, stdout: '', stderr: '' };
          }
          if (kind === 'claude') return { code: 0, stdout: JSON.stringify({ type: 'result', result: payload }), stderr: '' };
          if (kind === 'gemini') return { code: 0, stdout: JSON.stringify({ response: payload }), stderr: '' };
          return { code: 0, stdout: payload, stderr: '' };
        },
      },
    );
    assert.equal(cleaned, true, `cleanup ran for ${kind}`);
    assert.equal(res.already_fixed, false);
    assert.deepEqual(res.target_files, ['src/app.mjs'], 'only existing files on disk survive');
    assert.match(res.brief, /src\/app\.mjs/);
    assert.ok(!res.brief.includes('missing.mjs'));
  }
});

test('evaluateForensicsResult enforces concrete on-disk file proof and strips hashes and UUIDs from comments', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-forensics-proof-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const wt = join(dir, 'wt');
  const outside = join(dir, 'outside.mjs');
  mkdirSync(join(wt, 'src'), { recursive: true });
  mkdirSync(join(wt, 'test'), { recursive: true });
  writeFileSync(join(wt, 'src', 'a1b2c3d.mjs'), 'export const fixed = true;\n');
  writeFileSync(join(wt, 'test', 'fix.test.mjs'), 'test();\n');
  writeFileSync(outside, 'secret\n');
  try { symlinkSync(outside, join(wt, 'src', 'escape.mjs')); } catch { /* Symlinks optional on restricted FS. */ }

  // 1. Missing files on disk cannot produce already_fixed: true.
  const unverified = evaluateForensicsResult({
    already_fixed: true,
    summary: 'Looks fixed.',
    verifying_files: ['src/nonexistent.mjs', '../outside.mjs', 'src/escape.mjs'],
    verifying_tests: [],
    evidence: 'Guessed from memory.',
  }, { worktree: wt });
  assert.equal(unverified.already_fixed, false);
  assert.equal(unverified.disposition, 'still_needed');
  assert.equal(unverified.status, 'unverified_proof');

  // 2. Existing file on disk + non-empty explanation passes proof gate, and strips hashes/UUIDs while keeping file paths & words.
  const verified = evaluateForensicsResult({
    already_fixed: true,
    summary: 'Fixed in commit 02db5b950746e8968b045397533fc799e65ab84b (4158448) defaced 12345678.',
    verifying_files: ['src/a1b2c3d.mjs', 'src/escape.mjs'],
    verifying_tests: ['test/fix.test.mjs'],
    evidence: 'Run 550e8400-e29b-41d4-a716-446655440000 sha256:c47ca5ab88434f7249732d1ccec62910d5c3facb670a7e67a0e39105c6d6ffd6 receipt_998877 verifies src/a1b2c3d.mjs.',
  }, { worktree: wt });
  assert.equal(verified.already_fixed, true);
  assert.equal(verified.disposition, 'fixed');
  assert.deepEqual(verified.verifying_files, ['src/a1b2c3d.mjs']);
  assert.deepEqual(verified.verifying_tests, ['test/fix.test.mjs']);

  const comment = formatForensicsComment({ issue: 42, baseBranch: 'main', result: verified });
  assert.ok(comment.includes('`src/a1b2c3d.mjs`'));
  assert.ok(comment.includes('`test/fix.test.mjs`'));
  assert.ok(comment.includes('defaced'), 'normal English words composed of a-f letters survive');
  assert.ok(comment.includes('12345678'), 'plain numbers survive');
  assert.ok(!comment.includes('02db5b9'));
  assert.ok(!comment.includes('4158448'));
  assert.ok(!comment.includes('550e8400'));
  assert.ok(!comment.includes('c47ca5ab'));
  assert.ok(!comment.includes('receipt_998877'));
  assert.ok(comment.includes('<!-- pdd:autopilot-forensics:fixed:42 -->'));
  assert.equal(stripForbiddenIdentifiers('at commit 7ca561451 and uuid 123e4567-e89b-12d3-a456-426614174000'), 'at and uuid');
});

test('tickCore pre-run forensics handles already_fixed (no empty PR, no loop, re-admits on trusted reply, frees slot) and still_needed brief', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, intake: 'active' } });
  w.baseCommit('src/widget.mjs', 'export const widget = () => "ok";\n');
  w.baseCommit('test/widget.test.mjs', 'import { widget } from "../src/widget.mjs";\n');

  w.issue(17, { title: 'Widget returns wrong string', body: 'Make widget() return ok.' });
  w.issue(18, { title: 'Add widget timeout option', body: 'Support timeoutMs in src/widget.mjs.' });

  // Seed ready active-intake cards for #17 and #18 so active intake can select both.
  const cardsDir = join(w.root, 'intake', 'cards');
  mkdirSync(cardsDir, { recursive: true });
  const { issueVersion } = await import('../src/autopilot-intake.mjs');
  const listed = await w.ports().listIssues();
  for (const restRow of listed) {
    const n = restRow.number;
    writeFileSync(join(cardsDir, `${n}.json`), JSON.stringify({
      issue: n,
      version: issueVersion(restRow),
      at: w.now(),
      agent: { kind: 'codex', model: null },
      native: null,
      card: { class: 'ready', start: true, reason: 'Clear scope.', confidence: 0.9, areas: n === 17 ? ['src/widget.mjs'] : ['test/widget.test.mjs'], group_with: [], size: 'medium' },
    }));
  }

  const forensicsSeen = [];
  const tick1 = await w.tick({
    forensicsRun: async (_cmd, args, opts) => {
      const prompt = opts.input;
      const numMatch = /"number":\s*(\d+)/.exec(prompt);
      const issueNum = Number(numMatch?.[1]);
      forensicsSeen.push(issueNum);
      const outFile = args[args.indexOf('--output-last-message') + 1];
      if (issueNum === 17) {
        writeFileSync(outFile, JSON.stringify({
          already_fixed: true,
          summary: 'widget() already returns ok on main (commit 02db5b9507).',
          verifying_files: ['src/widget.mjs'],
          verifying_tests: ['test/widget.test.mjs'],
          evidence: 'Verified in src/widget.mjs and test/widget.test.mjs under run 550e8400-e29b-41d4-a716-446655440000.',
        }));
      } else {
        writeFileSync(outFile, JSON.stringify({
          already_fixed: false,
          summary: 'widget() does not accept timeoutMs yet.',
          target_files: ['src/widget.mjs', 'src/does-not-exist.mjs'],
          verifying_tests: ['test/widget.test.mjs'],
          reproduction: 'Pass { timeoutMs: 50 } to widget() in src/widget.mjs.',
        }));
      }
      return { code: 0, stdout: '', stderr: '' };
    },
  });

  // In a single tick with runs=1: #17 was proven already_fixed and released without consuming the build slot,
  // allowing #18 to start its build immediately with the grounded forensics brief!
  assert.deepEqual(forensicsSeen, [17, 18]);
  assert.match(tick1.message, /1 started.*1 ended/);
  assert.equal(w.job(17, 'build'), undefined, '#17 never launched a 30-minute build');
  assert.ok(!w.labels(17).includes('pdd:working'), '#17 released pdd:working');

  const comments17 = w.comments(17);
  assert.equal(comments17.length, 1, 'claim comment deleted and one concise forensics comment posted');
  assert.match(comments17[0], /`src\/widget\.mjs`/);
  assert.match(comments17[0], /`test\/widget\.test\.mjs`/);
  assert.ok(!comments17[0].includes('02db5b9507'), 'commit hash stripped from user-facing comment');
  assert.ok(!comments17[0].includes('550e8400'), 'UUID stripped from user-facing comment');

  // Saved intake card for #17 was synced to fixed so activeReadyCards skips #17.
  const listAfter1 = await w.ports().listIssues();
  assert.equal(activeReadyCards(w.root, listAfter1).has(17), false);

  // #18 started with the verified forensics brief injected into the builder prompt!
  const build18 = w.job(18, 'build');
  assert.ok(build18, '#18 started in the freed slot');
  const build18Prompt = build18.input;
  assert.match(build18Prompt, /Pre-run repository forensics on origin\/main:/);
  assert.match(build18Prompt, /Target files found on main: src\/widget\.mjs/);
  assert.match(build18Prompt, /Existing tests on main: test\/widget\.test\.mjs/);
  assert.match(build18Prompt, /Pass \{ timeoutMs: 50 \} to widget\(\)/);
  assert.ok(!build18Prompt.includes('does-not-exist.mjs'));

  // Status shows #17 fixed in Last results.
  const statusText = coreStatus({ state: w.state, settings: w.settings }, w.ports());
  assert.match(statusText, /#17 fixed /);

  // Finish #18 so slot is free again, then verify #17 does NOT re-claim in a loop on subsequent ticks
  // (even in intake: 'off' mode or when an untrusted user comments).
  w.settings.intake = 'off';
  w.github.issues.get(18).state = 'closed';
  await w.tick();
  assert.equal(existsSync(join(w.root, 'jobs', '18.json')), false);

  // Untrusted comment on #17 must NOT re-open the fixed hold.
  w.github.comment(17, 'Still broken for me!', 'outsider');
  await w.tick({
    forensics: async () => {
      assert.fail('forensics must not re-run after an untrusted comment');
    },
  });
  assert.equal(w.job(17, 'build'), undefined);

  // Trusted human reply on #17 clears the fixed hold and allows Autopilot to pick #17 up again!
  w.github.comment(17, 'Reproduces when input is null.', 'acme');
  let rechecked = false;
  await w.tick({
    forensics: async input => {
      rechecked = true;
      assert.equal(input.issue.number, 17);
      assert.ok(input.comments.some(c => c.body.includes('input is null')));
      // Also verify that if forensics guesses already_fixed WITHOUT existing file proof, Autopilot falls through safely to build!
      return { already_fixed: true, summary: 'Unverified guess', verifying_files: ['src/imaginary.mjs'], evidence: 'No real file' };
    },
  });
  assert.equal(rechecked, true);
  assert.ok(w.job(17, 'build'), 'unverified already_fixed fell through safely to start build');
  assert.equal(w.comments(17).filter(body => body.includes('pdd:autopilot-forensics:fixed:17')).length, 1, 'no second fixed comment posted');
});


test('codexProviderConfigArgs forwards native openai_base_url, chatgpt_base_url, features.responses_websockets=false, and redacts legacy grant headers', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-forensics-cfg-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));

  const managedHome = join(dir, 'managed-codex');
  mkdirSync(managedHome, { recursive: true });
  writeFileSync(join(managedHome, 'config.toml'), [
    'cli_auth_credentials_store = "file"',
    'openai_base_url = "https://api.promptdriven.ai/v1/codex-gateway"',
    'chatgpt_base_url = "https://api.promptdriven.ai/v1/codex-gateway"',
    '',
    '[model_providers.pdd_codex_gateway]',
    'name = "PDD Codex Gateway"',
    'base_url = "https://api.promptdriven.ai/v1/codex-gateway"',
    'wire_api = "responses"',
    'requires_openai_auth = true',
    '',
    '[shell_environment_policy.filters]',
    'PDD_CODEX_GATEWAY_GRANT = "exclude"',
    '',
    '[features]',
    'shell_snapshot = false',
    'responses_websockets = false',
    '',
  ].join('\n'));

  const env = { HOME: dir, CODEX_HOME: managedHome };
  const cmd = forensicsCommand({ kind: 'codex', command: 'codex' }, { env, resultFile: join(dir, 'out.json') });
  assert.ok(cmd.args.includes('cli_auth_credentials_store="file"'));
  assert.ok(cmd.args.includes('openai_base_url="https://api.promptdriven.ai/v1/codex-gateway"'));
  assert.ok(cmd.args.includes('chatgpt_base_url="https://api.promptdriven.ai/v1/codex-gateway"'));
  assert.ok(cmd.args.includes('shell_environment_policy.filters.PDD_CODEX_GATEWAY_GRANT="exclude"'));
  assert.ok(cmd.args.includes('features.shell_snapshot=false'));
  assert.ok(cmd.args.includes('features.responses_websockets=false'));
  assert.equal(cmd.args.some(a => a.startsWith('model_provider=')), false, 'native provider omits top-level model_provider override');

  // Legacy model_provider with inline x-pdd-gateway-grant moves secret to env and never leaks onto CLI args
  const legacyHome = join(dir, 'legacy-codex');
  mkdirSync(legacyHome, { recursive: true });
  writeFileSync(join(legacyHome, 'config.toml'), [
    'model_provider = "pdd_codex_gateway"',
    '[model_providers.pdd_codex_gateway]',
    'base_url = "https://api.promptdriven.ai/v1/codex-gateway/lse_leg"',
    'http_headers = { "x-pdd-gateway-grant" = "pddg_legacy_secret_9911" }',
    '',
  ].join('\n'));
  const legacyEnv = { HOME: dir, CODEX_HOME: legacyHome };
  const legacyArgs = codexProviderConfigArgs({ env: legacyEnv });
  assert.equal(legacyEnv.PDD_CODEX_GATEWAY_GRANT, 'pddg_legacy_secret_9911');
  assert.equal(legacyArgs.join(' ').includes('pddg_legacy_secret_9911'), false, 'grant secret never placed in CLI args');
  assert.ok(legacyArgs.includes('shell_environment_policy.filters.PDD_CODEX_GATEWAY_GRANT="exclude"'));
});

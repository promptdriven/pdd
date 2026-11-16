import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile, execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { findOwners, promptHeaderHash } from '../src/file-owner.mjs';
import {
  MAX_ATTEMPTS_PER_BASE,
  MERGE_QUEUE_SCHEMA,
  buildConflictAgentInvocation,
  discoverFocusedTestFiles,
  enqueueMergeQueueItem,
  hasGitConflictMarkers,
  isAllowedMergeQueueBranch,
  mergeQueueStatusLine,
  processMergeQueue,
  readMergeQueue,
  sanitizePublicQueueNote,
} from '../src/autopilot-merge-queue.mjs';
import { coreSettings, coreStatus } from '../src/autopilot-core.mjs';
import { coreWorld } from './helpers/core-world.mjs';

const GIT_USER = ['-c', 'user.name=Test', '-c', 'user.email=test@example.com'];
const HEADER_RE = /^\/\/ Generated from prompts\/cli\/calc\.prompt\.md \(sha256: [a-f0-9]+\)\./;

function gitSync(cwd, ...args) {
  return execFileSync('git', [...GIT_USER, ...args], {
    cwd,
    encoding: 'utf8',
    env: { ...process.env, GIT_TERMINAL_PROMPT: '0' },
  }).trim();
}

function createCalcRepoFixture(t) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-mq-test-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));

  const remote = join(dir, 'origin.git');
  const repo = join(dir, 'repo');
  const stateDir = join(dir, 'state');
  mkdirSync(remote, { recursive: true });
  mkdirSync(repo, { recursive: true });
  mkdirSync(stateDir, { recursive: true });

  gitSync(remote, 'init', '--bare', '-q', '-b', 'main');
  gitSync(repo, 'init', '-q', '-b', 'main');
  gitSync(repo, 'remote', 'add', 'origin', remote);

  const basePrompt = [
    '# Calculator module',
    '',
    'Own `src/calc.mjs` for deterministic arithmetic helpers.',
    '',
    '## Base rule',
    '- `id(x)` returns `Number(x)`.',
    '- Keep inputs numeric.',
    '- Never mutate arguments.',
    '- Return finite values for finite numbers.',
    '',
    '## Slot A',
    '- Reserved for addition.',
    '- Section A separator 1.',
    '- Section A separator 2.',
    '- Section A separator 3.',
    '- Section A separator 4.',
    '',
    '## Slot B',
    '- Reserved for multiplication.',
    '- Section B separator 1.',
    '- Section B separator 2.',
    '- Section B separator 3.',
    '- Section B separator 4.',
    '',
    '## Slot C',
    '- Reserved for clamping.',
    '- Section C separator 1.',
    '',
  ].join('\n');

  mkdirSync(join(repo, 'prompts/cli'), { recursive: true });
  mkdirSync(join(repo, 'src'), { recursive: true });
  mkdirSync(join(repo, 'test'), { recursive: true });

  writeFileSync(join(repo, 'prompts/cli/calc.prompt.md'), basePrompt);
  const h0 = promptHeaderHash(Buffer.from(basePrompt));
  const baseCode = [
    `// Generated from prompts/cli/calc.prompt.md (sha256: ${h0}).`,
    '// Spacer 1',
    '// Spacer 2',
    '// Spacer 3',
    '// Spacer 4',
    'export function id(x) {',
    '  return Number(x);',
    '}',
    '// Spacer A1',
    '// Spacer A2',
    '// Spacer A3',
    '// --- slot A ---',
    'export const slotA = null;',
    '// Spacer B1',
    '// Spacer B2',
    '// Spacer B3',
    '// Spacer B4',
    '// --- slot B ---',
    'export const slotB = null;',
    '// Spacer C1',
    '// Spacer C2',
    '// Spacer C3',
    '// Spacer C4',
    '// --- slot C ---',
    'export const slotC = null;',
    '',
  ].join('\n');
  writeFileSync(join(repo, 'src/calc.mjs'), baseCode);

  const baseTest = [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import * as calc from '../src/calc.mjs';",
    '',
    "test('base id', () => { assert.equal(calc.id('7'), 7); });",
    '// Test spacer A1',
    '// Test spacer A2',
    '// Test spacer A3',
    '// --- test A ---',
    '// Test spacer B1',
    '// Test spacer B2',
    '// Test spacer B3',
    '// Test spacer B4',
    '// --- test B ---',
    '// Test spacer C1',
    '// Test spacer C2',
    '// Test spacer C3',
    '// Test spacer C4',
    '// --- test C ---',
    '',
  ].join('\n');
  writeFileSync(join(repo, 'test/calc.test.mjs'), baseTest);

  gitSync(repo, 'add', '.');
  gitSync(repo, 'commit', '-q', '-m', 'init calc');
  gitSync(repo, 'push', '-q', '-u', 'origin', 'main');

  const initialMainSha = gitSync(repo, 'rev-parse', 'HEAD');

  let branchIdx = 0;
  const makeBranch = (branchName, fromSha, mutator) => {
    const scratch = join(dir, `branch-${++branchIdx}`);
    gitSync(dir, 'clone', '-q', remote, scratch);
    gitSync(scratch, 'checkout', '-q', '-b', branchName, fromSha);
    mutator(scratch);
    gitSync(scratch, 'add', '.');
    gitSync(scratch, 'commit', '-q', '-m', `feat: ${branchName}`);
    gitSync(scratch, 'push', '-q', 'origin', `HEAD:refs/heads/${branchName}`);
    return gitSync(scratch, 'rev-parse', 'HEAD');
  };

  const landOnRemoteMain = ({ branch, headSha }) => {
    const merger = join(dir, `merger-${++branchIdx}`);
    gitSync(dir, 'clone', '-q', remote, merger);
    gitSync(merger, 'checkout', '-q', 'main');
    const mainSha = gitSync(merger, 'rev-parse', 'HEAD');
    const actualBranchSha = gitSync(merger, 'rev-parse', `origin/${branch}`);
    if (actualBranchSha !== headSha) {
      return { merged: false, error: `head mismatch: expected ${headSha}, got ${actualBranchSha}` };
    }
    try {
      execFileSync('git', ['merge-base', '--is-ancestor', mainSha, actualBranchSha], { cwd: merger });
    } catch {
      return { merged: false, error: 'branch is behind main' };
    }
    gitSync(merger, 'merge', '--no-ff', '-q', '-m', `Merge ${branch}`, actualBranchSha);
    gitSync(merger, 'push', '-q', 'origin', 'main');
    const newMainSha = gitSync(merger, 'rev-parse', 'HEAD');
    return { merged: true, baseTipSha: newMainSha };
  };

  return { dir, remote, repo, stateDir, initialMainSha, makeBranch, landOnRemoteMain };
}

test('MQ1: serialized FIFO landing train rebases 3 concurrent PRs touching the same prompt & owned module with 0 AI calls for PDD header-hash conflicts', async t => {
  const fx = createCalcRepoFixture(t);

  const sha101 = fx.makeBranch('pdd/core-101-add', fx.initialMainSha, wt => {
    const p = readFileSync(join(wt, 'prompts/cli/calc.prompt.md'), 'utf8')
      .replace('- Reserved for addition.', '- `add(a, b)` returns `a + b`.');
    writeFileSync(join(wt, 'prompts/cli/calc.prompt.md'), p);
    const h = promptHeaderHash(Buffer.from(p));
    const c = readFileSync(join(wt, 'src/calc.mjs'), 'utf8')
      .replace(HEADER_RE, `// Generated from prompts/cli/calc.prompt.md (sha256: ${h}).`)
      .replace('export const slotA = null;', 'export function add(a, b) { return a + b; }');
    writeFileSync(join(wt, 'src/calc.mjs'), c);
    const tst = readFileSync(join(wt, 'test/calc.test.mjs'), 'utf8')
      .replace('// --- test A ---', "test('add', () => { assert.equal(calc.add(2, 5), 7); });");
    writeFileSync(join(wt, 'test/calc.test.mjs'), tst);
  });

  const sha102 = fx.makeBranch('pdd/core-102-mul', fx.initialMainSha, wt => {
    const p = readFileSync(join(wt, 'prompts/cli/calc.prompt.md'), 'utf8')
      .replace('- Reserved for multiplication.', '- `mul(a, b)` returns `a * b`.');
    writeFileSync(join(wt, 'prompts/cli/calc.prompt.md'), p);
    const h = promptHeaderHash(Buffer.from(p));
    const c = readFileSync(join(wt, 'src/calc.mjs'), 'utf8')
      .replace(HEADER_RE, `// Generated from prompts/cli/calc.prompt.md (sha256: ${h}).`)
      .replace('export const slotB = null;', 'export function mul(a, b) { return a * b; }');
    writeFileSync(join(wt, 'src/calc.mjs'), c);
    const tst = readFileSync(join(wt, 'test/calc.test.mjs'), 'utf8')
      .replace('// --- test B ---', "test('mul', () => { assert.equal(calc.mul(3, 4), 12); });");
    writeFileSync(join(wt, 'test/calc.test.mjs'), tst);
  });

  const sha103 = fx.makeBranch('pdd/core-103-clamp', fx.initialMainSha, wt => {
    const p = readFileSync(join(wt, 'prompts/cli/calc.prompt.md'), 'utf8')
      .replace('- Reserved for clamping.', '- `clamp(v, lo, hi)` bounds `v` to `[lo, hi]`.');
    writeFileSync(join(wt, 'prompts/cli/calc.prompt.md'), p);
    const h = promptHeaderHash(Buffer.from(p));
    const c = readFileSync(join(wt, 'src/calc.mjs'), 'utf8')
      .replace(HEADER_RE, `// Generated from prompts/cli/calc.prompt.md (sha256: ${h}).`)
      .replace('export const slotC = null;', 'export function clamp(v, lo, hi) { return Math.min(hi, Math.max(lo, v)); }');
    writeFileSync(join(wt, 'src/calc.mjs'), c);
    const tst = readFileSync(join(wt, 'test/calc.test.mjs'), 'utf8')
      .replace('// --- test C ---', "test('clamp', () => { assert.equal(calc.clamp(15, 0, 10), 10); });");
    writeFileSync(join(wt, 'test/calc.test.mjs'), tst);
  });

  // Enqueue out-of-order to verify strict FIFO sorting by (readyAt, pr)
  await enqueueMergeQueueItem({ stateDir: fx.stateDir, pr: 103, issue: 103, branch: 'pdd/core-103-clamp', baseBranch: 'main', headSha: sha103, readyAt: 3000 });
  await enqueueMergeQueueItem({ stateDir: fx.stateDir, pr: 101, issue: 101, branch: 'pdd/core-101-add', baseBranch: 'main', headSha: sha101, readyAt: 1000 });
  await enqueueMergeQueueItem({ stateDir: fx.stateDir, pr: 102, issue: 102, branch: 'pdd/core-102-mul', baseBranch: 'main', headSha: sha102, readyAt: 2000 });

  assert.deepEqual(readMergeQueue(fx.stateDir).items.map(i => i.pr), [101, 102, 103]);
  assert.match(mergeQueueStatusLine(fx.stateDir), /Merge queue: 3 queued \(PR #101, PR #102, PR #103\)\./);

  const prStates = new Map([
    [101, { number: 101, state: 'open', merged: false, branch: 'pdd/core-101-add', headSha: sha101 }],
    [102, { number: 102, state: 'open', merged: false, branch: 'pdd/core-102-mul', headSha: sha102 }],
    [103, { number: 103, state: 'open', merged: false, branch: 'pdd/core-103-clamp', headSha: sha103 }],
  ]);

  const pushCommands = [];
  const mergeEvents = [];
  let aiCalls = 0;

  const out = await processMergeQueue({
    stateDir: fx.stateDir,
    repoRoot: fx.repo,
    baseBranch: 'main',
    mode: 'auto',
    agent: { kind: 'codex', command: 'codex' },
  }, {
    git: (args, opts) => {
      if (args[0] === 'push') pushCommands.push(args);
      return new Promise(res => execFile('git', args, { cwd: opts?.cwd, encoding: 'utf8' }, (err, stdout = '', stderr = '') => {
        res({ code: err ? (err.code ?? 1) : 0, stdout, stderr: stderr || err?.message || '' });
      }));
    },
    getPullRequest: async pr => prStates.get(pr),
    mergePullRequest: async req => {
      const landed = fx.landOnRemoteMain(req);
      if (landed.merged) {
        prStates.get(req.pr).merged = true;
        prStates.get(req.pr).state = 'closed';
        prStates.get(req.pr).headSha = req.headSha;
        mergeEvents.push({ pr: req.pr, rebased: req.rebased });
      }
      return landed;
    },
    runConflictAgent: async () => {
      aiCalls++;
      throw new Error('Zero AI calls expected when conflict is purely PDD Generated-from header line!');
    },
  });

  assert.equal(aiCalls, 0, 'PDD Generated-from header conflicts resolved with 0 AI calls');
  assert.deepEqual(out.merged, [101, 102, 103], 'all 3 PRs landed serially in strict FIFO order');
  assert.deepEqual(mergeEvents, [
    { pr: 101, rebased: false },
    { pr: 102, rebased: true },
    { pr: 103, rebased: true },
  ]);

  assert.equal(pushCommands.length, 2, 'PR #102 and PR #103 pushed rebased heads');
  for (const args of pushCommands) {
    assert.equal(args.includes('--force'), false, 'never uses plain --force');
    assert.ok(args.some(a => a.startsWith('--force-with-lease=refs/heads/pdd/core-')), 'uses explicit --force-with-lease');
    assert.equal(args.some(a => a.endsWith(':refs/heads/main')), false, 'never pushes to main');
  }

  gitSync(fx.repo, 'fetch', '-q', 'origin', 'main');
  gitSync(fx.repo, 'checkout', '-q', 'origin/main');
  const ownerCheck = findOwners({ root: fx.repo, paths: ['src/calc.mjs'] });
  assert.equal(ownerCheck.files[0].headers[0].state, 'current', 'final merged src/calc.mjs header hash is current');
  const { NODE_TEST_CONTEXT: _dropNtc, ...cleanTestEnv } = process.env;
  const calcOut = execFileSync(process.execPath, ['--test', 'test/calc.test.mjs'], { cwd: fx.repo, env: cleanTestEnv, encoding: 'utf8' });
  assert.match(calcOut, /# pass 4/);
  assert.equal(mergeQueueStatusLine(fx.stateDir), '', 'status line is empty once all queued PRs merged');
});

test('MQ2: post-rebase PDD header-hash drift sweep refreshes owned headers with 0 AI calls even when git rebase had zero conflict markers', async t => {
  const fx = createCalcRepoFixture(t);

  const sha201 = fx.makeBranch('pdd/core-201-slot-a', fx.initialMainSha, wt => {
    const p = readFileSync(join(wt, 'prompts/cli/calc.prompt.md'), 'utf8')
      .replace('- Reserved for addition.', '- `add(a, b)` returns `a + b`.');
    writeFileSync(join(wt, 'prompts/cli/calc.prompt.md'), p);
    const h = promptHeaderHash(Buffer.from(p));
    const c = readFileSync(join(wt, 'src/calc.mjs'), 'utf8')
      .replace(HEADER_RE, `// Generated from prompts/cli/calc.prompt.md (sha256: ${h}).`);
    writeFileSync(join(wt, 'src/calc.mjs'), c);
  });
  fx.landOnRemoteMain({ branch: 'pdd/core-201-slot-a', headSha: sha201 });

  const sha202 = fx.makeBranch('pdd/core-202-prompt-only', fx.initialMainSha, wt => {
    const p = readFileSync(join(wt, 'prompts/cli/calc.prompt.md'), 'utf8')
      .replace('- Reserved for multiplication.', '- Clarified multiplication wording.');
    writeFileSync(join(wt, 'prompts/cli/calc.prompt.md'), p);
  });

  await enqueueMergeQueueItem({ stateDir: fx.stateDir, pr: 202, issue: 202, branch: 'pdd/core-202-prompt-only', baseBranch: 'main', headSha: sha202, readyAt: 100 });
  let aiCalls = 0;
  const out = await processMergeQueue({
    stateDir: fx.stateDir,
    repoRoot: fx.repo,
    baseBranch: 'main',
    mode: 'auto',
  }, {
    getPullRequest: async () => ({ number: 202, state: 'open', merged: false, branch: 'pdd/core-202-prompt-only', headSha: sha202 }),
    mergePullRequest: async req => fx.landOnRemoteMain(req),
    runConflictAgent: async () => { aiCalls++; return { resolved: false }; },
  });

  assert.equal(aiCalls, 0);
  assert.deepEqual(out.merged, [202]);
  gitSync(fx.repo, 'fetch', '-q', 'origin', 'main');
  gitSync(fx.repo, 'checkout', '-q', 'origin/main');
  assert.equal(findOwners({ root: fx.repo, paths: ['src/calc.mjs'] }).files[0].headers[0].state, 'current');
});

test('MQ3: observe mode keeps waiting would-merge PRs conflict-free as humans merge earlier PRs, and integrates with tickCore & coreStatus', async t => {
  assert.equal(coreSettings({ autopilot: { engine: 'core', mergeQueue: true } }).mergeQueue, true);

  const fx = createCalcRepoFixture(t);

  const sha301 = fx.makeBranch('pdd/core-301-add', fx.initialMainSha, wt => {
    const p = readFileSync(join(wt, 'prompts/cli/calc.prompt.md'), 'utf8').replace('- Reserved for addition.', '- `add(a, b)` returns `a + b`.');
    writeFileSync(join(wt, 'prompts/cli/calc.prompt.md'), p);
    const h = promptHeaderHash(Buffer.from(p));
    writeFileSync(join(wt, 'src/calc.mjs'), readFileSync(join(wt, 'src/calc.mjs'), 'utf8')
      .replace(HEADER_RE, `// Generated from prompts/cli/calc.prompt.md (sha256: ${h}).`)
      .replace('export const slotA = null;', 'export function add(a, b) { return a + b; }'));
  });
  const sha302 = fx.makeBranch('pdd/core-302-mul', fx.initialMainSha, wt => {
    const p = readFileSync(join(wt, 'prompts/cli/calc.prompt.md'), 'utf8').replace('- Reserved for multiplication.', '- `mul(a, b)` returns `a * b`.');
    writeFileSync(join(wt, 'prompts/cli/calc.prompt.md'), p);
    const h = promptHeaderHash(Buffer.from(p));
    writeFileSync(join(wt, 'src/calc.mjs'), readFileSync(join(wt, 'src/calc.mjs'), 'utf8')
      .replace(HEADER_RE, `// Generated from prompts/cli/calc.prompt.md (sha256: ${h}).`)
      .replace('export const slotB = null;', 'export function mul(a, b) { return a * b; }'));
  });

  await enqueueMergeQueueItem({ stateDir: fx.stateDir, pr: 301, issue: 301, branch: 'pdd/core-301-add', baseBranch: 'main', headSha: sha301, readyAt: 100 });
  await enqueueMergeQueueItem({ stateDir: fx.stateDir, pr: 302, issue: 302, branch: 'pdd/core-302-mul', baseBranch: 'main', headSha: sha302, readyAt: 200 });

  const prMap = new Map([
    [301, { number: 301, state: 'open', merged: false, branch: 'pdd/core-301-add', headSha: sha301 }],
    [302, { number: 302, state: 'open', merged: false, branch: 'pdd/core-302-mul', headSha: sha302 }],
  ]);
  let ghReads = 0;

  const first = await processMergeQueue({
    stateDir: fx.stateDir, repoRoot: fx.repo, baseBranch: 'main', mode: 'observe',
  }, {
    getPullRequest: async pr => { ghReads++; return prMap.get(pr); },
    mergePullRequest: async () => { throw new Error('observe mode must never merge'); },
  });
  assert.deepEqual(first.synced, [301, 302]);
  assert.deepEqual(first.merged, []);

  ghReads = 0;
  const idle = await processMergeQueue({
    stateDir: fx.stateDir, repoRoot: fx.repo, baseBranch: 'main', mode: 'observe',
  }, {
    getPullRequest: async pr => { ghReads++; return prMap.get(pr); },
  });
  assert.equal(ghReads, 0, 'synced observe queue makes 0 GitHub reads when origin/main has not moved');
  assert.equal(idle.processed, 0);

  const humanLand = fx.landOnRemoteMain({ branch: 'pdd/core-301-add', headSha: sha301 });
  assert.equal(humanLand.merged, true);
  prMap.get(301).merged = true;
  prMap.get(301).state = 'closed';

  const afterHumanMerge = await processMergeQueue({
    stateDir: fx.stateDir, repoRoot: fx.repo, baseBranch: 'main', mode: 'observe',
  }, {
    getPullRequest: async pr => prMap.get(pr),
    mergePullRequest: async () => { throw new Error('observe mode must never merge'); },
  });
  assert.deepEqual(afterHumanMerge.merged, [301]);
  assert.deepEqual(afterHumanMerge.synced, [302]);
  const item302 = afterHumanMerge.queue.items.find(i => i.pr === 302);
  assert.notEqual(item302.headSha, sha302, 'PR #302 rebased onto new origin/main tip');
  assert.equal(item302.syncedBaseSha, humanLand.baseTipSha);

  // End-to-end observe enqueue + status line through coreWorld (tickCore)
  const w = await coreWorld(t, { settings: { mode: 'observe', runs: 1 } });
  w.issue(71, { title: 'Observe queue integration', body: 'Small fix.' });
  await w.tick();
  w.build(71, { body: 'Fixes #71\n\nRuntime: PASS\nEvidence: runtime=pass (1/1); tests=pass (1/1)' });
  await w.tick();
  w.review(71, 'PASS');
  w.suite(71, 0);
  await w.tick();
  const q = readMergeQueue(w.root);
  assert.equal(q.schema, MERGE_QUEUE_SCHEMA);
  assert.equal(q.items.length, 1);
  assert.equal(q.items[0].issue, 71);
  assert.match(coreStatus({ state: w.state, settings: w.settings }, { root: w.root, now: w.now }), /Merge queue: 1 synced\./);

  // End-to-end auto mode with mergeQueue: true through coreWorld (tickCore)
  const wAuto = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  wAuto.settings.mergeQueue = true;
  wAuto.issue(72, { title: 'Auto mergeQueue integration', body: 'Small fix.' });
  await wAuto.tick();
  const { pr: pr72 } = wAuto.build(72, { body: 'Fixes #72\n\nRuntime: PASS' });
  await wAuto.tick();
  wAuto.review(72, 'PASS');
  wAuto.suite(72, 0);
  const landedTick = await wAuto.tick();
  assert.match(landedTick.message, /1 merged/);
  assert.equal(pr72.merged, true);
  assert.equal(readMergeQueue(wAuto.root).items[0].state, 'merged');
});

test('MQ4: runs 1 bounded conflict-resolution agent pass (Codex / Claude / Gemini / AGY) on real conflict markers and aborts cleanly if markers remain', async t => {
  assert.equal(buildConflictAgentInvocation({ kind: 'codex', model: 'gpt-5' }).command, 'codex');
  assert.ok(buildConflictAgentInvocation({ kind: 'codex', model: 'gpt-5' }).args.includes('exec'));
  assert.equal(buildConflictAgentInvocation({ kind: 'claude', command: '/usr/local/bin/claude' }).command, '/usr/local/bin/claude');
  assert.equal(buildConflictAgentInvocation({ kind: 'gemini' }).kind, 'gemini');
  assert.equal(buildConflictAgentInvocation({ kind: 'agy' }).kind, 'agy');
  assert.throws(() => buildConflictAgentInvocation({ kind: 'unknown-bot' }), /Unsupported conflict-resolution agent kind/);

  const fx = createCalcRepoFixture(t);

  const shaUp = fx.makeBranch('pdd/core-400-up', fx.initialMainSha, wt => {
    writeFileSync(join(wt, 'src/calc.mjs'), readFileSync(join(wt, 'src/calc.mjs'), 'utf8')
      .replace('export const slotA = null;', 'export const slotA = "upstream";'));
  });
  fx.landOnRemoteMain({ branch: 'pdd/core-400-up', headSha: shaUp });

  const sha401 = fx.makeBranch('pdd/core-401-real-conflict', fx.initialMainSha, wt => {
    writeFileSync(join(wt, 'src/calc.mjs'), readFileSync(join(wt, 'src/calc.mjs'), 'utf8')
      .replace('export const slotA = null;', 'export const slotA = "pr-401";'));
  });

  const sha402 = fx.makeBranch('pdd/core-402-leaves-markers', fx.initialMainSha, wt => {
    writeFileSync(join(wt, 'src/calc.mjs'), readFileSync(join(wt, 'src/calc.mjs'), 'utf8')
      .replace('export const slotA = null;', 'export const slotA = "pr-402";'));
  });

  await enqueueMergeQueueItem({ stateDir: fx.stateDir, pr: 401, issue: 401, branch: 'pdd/core-401-real-conflict', baseBranch: 'main', headSha: sha401, readyAt: 100 });
  let seenPrompt = '';
  const res401 = await processMergeQueue({
    stateDir: fx.stateDir, repoRoot: fx.repo, baseBranch: 'main', mode: 'auto', agent: { kind: 'codex', command: 'codex' },
  }, {
    getPullRequest: async () => ({ number: 401, state: 'open', merged: false, branch: 'pdd/core-401-real-conflict', headSha: sha401 }),
    mergePullRequest: async req => fx.landOnRemoteMain(req),
    runConflictAgent: async ({ cwd, conflictFiles, prompt, invocation }) => {
      seenPrompt = prompt;
      assert.deepEqual(conflictFiles, ['src/calc.mjs']);
      assert.equal(invocation.kind, 'codex');
      const conflicted = readFileSync(join(cwd, 'src/calc.mjs'), 'utf8');
      assert.equal(hasGitConflictMarkers(conflicted), true);
      const cleaned = conflicted.replace(/<<<<<<<[\s\S]*?>>>>>>>[^\n]*/, 'export const slotA = "combined-upstream-and-401";');
      writeFileSync(join(cwd, 'src/calc.mjs'), cleaned);
      return { resolved: true };
    },
  });

  assert.deepEqual(res401.merged, [401]);
  assert.match(seenPrompt, /Upstream diff/);
  assert.match(seenPrompt, /PR diff/);

  await enqueueMergeQueueItem({ stateDir: fx.stateDir, pr: 402, issue: 402, branch: 'pdd/core-402-leaves-markers', baseBranch: 'main', headSha: sha402, readyAt: 200 });
  const res402 = await processMergeQueue({
    stateDir: fx.stateDir, repoRoot: fx.repo, baseBranch: 'main', mode: 'auto', agent: { kind: 'claude', command: 'claude' },
  }, {
    getPullRequest: async () => ({ number: 402, state: 'open', merged: false, branch: 'pdd/core-402-leaves-markers', headSha: sha402 }),
    mergePullRequest: async req => fx.landOnRemoteMain(req),
    runConflictAgent: async () => ({ resolved: true }),
  });

  assert.deepEqual(res402.merged, []);
  assert.deepEqual(res402.retried, [402]);
  assert.equal(existsSync(join(fx.stateDir, 'merge-queue-worktrees/pr-402')), false, 'temp rebase worktree cleaned up after abort');
  assert.equal(gitSync(fx.remote, 'rev-parse', 'refs/heads/pdd/core-402-leaves-markers'), sha402, 'remote PR branch never pushed when conflict markers remain');
});

test('MQ5: post-rebase focused test failure blocks push, and branch guard refuses main or non-Autopilot branches', async t => {
  assert.equal(isAllowedMergeQueueBranch('pdd/core-3455-abc123', 'main'), true);
  assert.equal(isAllowedMergeQueueBranch('main', 'main'), false);
  assert.equal(isAllowedMergeQueueBranch('master', 'main'), false);
  assert.equal(isAllowedMergeQueueBranch('develop', 'develop'), false);
  assert.equal(isAllowedMergeQueueBranch('feat/human-branch', 'main'), false);
  assert.equal(isAllowedMergeQueueBranch('--mirror', 'main'), false);
  assert.equal(isAllowedMergeQueueBranch('origin/pdd/core-1-a', 'main'), false);
  assert.equal(isAllowedMergeQueueBranch('pdd/core-1-a..b', 'main'), false);

  const fx = createCalcRepoFixture(t);
  await assert.rejects(
    () => enqueueMergeQueueItem({ stateDir: fx.stateDir, pr: 1, issue: 1, branch: 'main', headSha: fx.initialMainSha }),
    /Refusing to enqueue/,
  );

  const shaUp = fx.makeBranch('pdd/core-449-up', fx.initialMainSha, wt => {
    writeFileSync(join(wt, 'src/calc.mjs'), readFileSync(join(wt, 'src/calc.mjs'), 'utf8')
      .replace('export const slotA = null;', 'export const slotA = 99;'));
  });
  fx.landOnRemoteMain({ branch: 'pdd/core-449-up', headSha: shaUp });

  const sha450 = fx.makeBranch('pdd/core-450-semantic-break', fx.initialMainSha, wt => {
    writeFileSync(join(wt, 'test/calc.test.mjs'), readFileSync(join(wt, 'test/calc.test.mjs'), 'utf8')
      .replace('// --- test B ---', "test('expects old slotA', () => { assert.equal(calc.slotA, null); });"));
  });

  assert.deepEqual(discoverFocusedTestFiles(fx.repo, ['src/calc.mjs']), ['test/calc.test.mjs']);

  await enqueueMergeQueueItem({ stateDir: fx.stateDir, pr: 450, issue: 450, branch: 'pdd/core-450-semantic-break', baseBranch: 'main', headSha: sha450, readyAt: 100 });
  const out = await processMergeQueue({
    stateDir: fx.stateDir, repoRoot: fx.repo, baseBranch: 'main', mode: 'auto',
  }, {
    getPullRequest: async () => ({ number: 450, state: 'open', merged: false, branch: 'pdd/core-450-semantic-break', headSha: sha450 }),
    mergePullRequest: async req => fx.landOnRemoteMain(req),
  });

  assert.deepEqual(out.merged, []);
  assert.equal(gitSync(fx.remote, 'rev-parse', 'refs/heads/pdd/core-450-semantic-break'), sha450, 'failing post-rebase test blocked force-with-lease push');
  assert.match(out.queue.items[0].lastError, /focused tests failed/);
});

test('MQ6: tracks attempts per origin/<baseBranch> tip (never penalizing queue movement), ejects after 2 failures on the same base tip with a hash-free note, and immediately lands the next PR', async t => {
  assert.equal(MAX_ATTEMPTS_PER_BASE, 2);

  const sanitized = sanitizePublicQueueNote(
    'Failed at commit 02db5b950abcdef1234567890abcdef12345678 (sha256: 8de6006cebcdef1234567890abcdef1234567890abcdef1234567890abcdef12) job 8a60d5a3-99d9-4952-9e80-fcd14247a582 batch 20261116-223106-k9ti on pdd/core-502-fix',
  );
  assert.doesNotMatch(sanitized, /[0-9a-f]{7,64}/i);
  assert.doesNotMatch(sanitized, /[0-9a-f]{8}-[0-9a-f]{4}/i);
  assert.doesNotMatch(sanitized, /20261116-223106/);
  assert.match(sanitized, /pdd\/core-502-fix/);

  const fx = createCalcRepoFixture(t);

  const shaBaseA = fx.makeBranch('pdd/core-500-base-a', fx.initialMainSha, wt => {
    writeFileSync(join(wt, 'src/calc.mjs'), readFileSync(join(wt, 'src/calc.mjs'), 'utf8')
      .replace('export const slotA = null;', 'export const slotA = "A";'));
  });
  const landA = fx.landOnRemoteMain({ branch: 'pdd/core-500-base-a', headSha: shaBaseA });

  const sha501 = fx.makeBranch('pdd/core-501-resets-on-move', fx.initialMainSha, wt => {
    writeFileSync(join(wt, 'src/calc.mjs'), readFileSync(join(wt, 'src/calc.mjs'), 'utf8')
      .replace('export const slotB = null;', 'export const slotB = "501";'));
  });
  await enqueueMergeQueueItem({ stateDir: fx.stateDir, pr: 501, issue: 501, branch: 'pdd/core-501-resets-on-move', baseBranch: 'main', headSha: sha501, readyAt: 100 });

  // 1st failure on baseTipA -> attemptsByBase[baseTipA] === 1 (NOT ejected!)
  await processMergeQueue({
    stateDir: fx.stateDir, repoRoot: fx.repo, baseBranch: 'main', mode: 'auto',
  }, {
    getPullRequest: async () => ({ number: 501, state: 'open', merged: false, branch: 'pdd/core-501-resets-on-move', headSha: sha501 }),
    runFocusedTests: async () => ({ ok: false, reason: 'transient failure on base A' }),
  });
  let item501 = readMergeQueue(fx.stateDir).items.find(i => i.pr === 501);
  assert.equal(item501.state, 'queued');
  assert.equal(item501.attemptsByBase[landA.baseTipSha], 1);

  // Earlier PR lands on main -> origin/main moves to baseTipB!
  const shaBaseB = fx.makeBranch('pdd/core-500-base-b', landA.baseTipSha, wt => {
    writeFileSync(join(wt, 'test/calc.test.mjs'), readFileSync(join(wt, 'test/calc.test.mjs'), 'utf8')
      .replace('// --- test A ---', "test('slotA is A', () => { assert.equal(calc.slotA, 'A'); });"));
  });
  const landB = fx.landOnRemoteMain({ branch: 'pdd/core-500-base-b', headSha: shaBaseB });

  // 1st failure on NEW baseTipB -> attemptsByBase[baseTipB] === 1, STILL NOT EJECTED because base moved!
  const latest501Sha = gitSync(fx.remote, 'rev-parse', 'refs/heads/pdd/core-501-resets-on-move');
  await processMergeQueue({
    stateDir: fx.stateDir, repoRoot: fx.repo, baseBranch: 'main', mode: 'auto',
  }, {
    getPullRequest: async () => ({ number: 501, state: 'open', merged: false, branch: 'pdd/core-501-resets-on-move', headSha: latest501Sha }),
    runFocusedTests: async () => ({ ok: false, reason: 'first failure on base B' }),
  });
  item501 = readMergeQueue(fx.stateDir).items.find(i => i.pr === 501);
  assert.equal(item501.state, 'queued', 'earlier PR landing on main never penalizes PR #501 toward ejection');
  assert.equal(item501.attemptsByBase[landB.baseTipSha], 1);

  const merged501 = await processMergeQueue({
    stateDir: fx.stateDir, repoRoot: fx.repo, baseBranch: 'main', mode: 'auto',
  }, {
    getPullRequest: async () => ({ number: 501, state: 'open', merged: false, branch: 'pdd/core-501-resets-on-move', headSha: latest501Sha }),
    mergePullRequest: async req => fx.landOnRemoteMain(req),
  });
  assert.deepEqual(merged501.merged, [501]);

  // Part B: Queue Eject Rule (Never Clog the Train!)
  const currentMainSha = gitSync(fx.remote, 'rev-parse', 'refs/heads/main');
  const sha502 = fx.makeBranch('pdd/core-502-clogger', fx.initialMainSha, wt => {
    writeFileSync(join(wt, 'src/calc.mjs'), readFileSync(join(wt, 'src/calc.mjs'), 'utf8')
      .replace('export const slotA = null;', 'export const slotA = "broken-502";'));
  });
  const sha503 = fx.makeBranch('pdd/core-503-clean-behind', fx.initialMainSha, wt => {
    writeFileSync(join(wt, 'src/calc.mjs'), readFileSync(join(wt, 'src/calc.mjs'), 'utf8')
      .replace('export const slotC = null;', 'export const slotC = "clean-503";'));
  });

  await enqueueMergeQueueItem({ stateDir: fx.stateDir, pr: 502, issue: 502, branch: 'pdd/core-502-clogger', baseBranch: 'main', headSha: sha502, readyAt: 200 });
  await enqueueMergeQueueItem({ stateDir: fx.stateDir, pr: 503, issue: 503, branch: 'pdd/core-503-clean-behind', baseBranch: 'main', headSha: sha503, readyAt: 300 });

  const prComments = [];
  const trainOut = await processMergeQueue({
    stateDir: fx.stateDir,
    repoRoot: fx.repo,
    baseBranch: 'main',
    mode: 'auto',
    maxAttemptsPerCall: 2,
  }, {
    getPullRequest: async pr => ({
      number: pr,
      state: 'open',
      merged: false,
      branch: pr === 502 ? 'pdd/core-502-clogger' : 'pdd/core-503-clean-behind',
      headSha: pr === 502 ? sha502 : sha503,
    }),
    mergePullRequest: async req => fx.landOnRemoteMain(req),
    commentOnPr: async (pr, body) => { prComments.push({ pr, body }); },
  });

  assert.deepEqual(trainOut.ejected, [502], 'PR #502 ejected after 2 failures on the same base tip');
  assert.deepEqual(trainOut.merged, [503], 'queue immediately advanced past ejected PR #502 and landed PR #503');

  const ejectedItem = trainOut.queue.items.find(i => i.pr === 502);
  assert.equal(ejectedItem.state, 'ejected');
  assert.equal(ejectedItem.attemptsByBase[currentMainSha], 2);
  assert.match(mergeQueueStatusLine(fx.stateDir), /1 ejected \(PR #502\)/);

  assert.equal(prComments.length, 1);
  assert.equal(prComments[0].pr, 502);
  assert.doesNotMatch(prComments[0].body, /\b[0-9a-f]{7,64}\b/i);
  assert.match(prComments[0].body, /PR #502/);

  const stillEjected = await enqueueMergeQueueItem({ stateDir: fx.stateDir, pr: 502, issue: 502, branch: 'pdd/core-502-clogger', baseBranch: 'main', headSha: sha502 });
  assert.equal(stillEjected.entry.state, 'ejected');
  const requeued = await enqueueMergeQueueItem({ stateDir: fx.stateDir, pr: 502, issue: 502, branch: 'pdd/core-502-clogger', baseBranch: 'main', headSha: 'new-commit-after-fix' });
  assert.equal(requeued.entry.state, 'queued');
  assert.deepEqual(requeued.entry.attemptsByBase, {});
});

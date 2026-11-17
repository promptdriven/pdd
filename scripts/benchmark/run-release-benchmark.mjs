#!/usr/bin/env node
// Part A: PDD Release Authoring & Runtime Matrix Benchmark Runner & Comparator.

import * as nativeFs from 'node:fs';
import { join, resolve, dirname } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import {
  BENCHMARK_WORKLOADS,
  DEFAULT_PRICING_PER_MILLION,
  computeNorthStarScorecard,
  estimateTokenUsd,
  roundNum,
  sanitizePublicData,
  sanitizePublicText,
} from './scorecard.mjs';

const DEFAULT_ROOT = fileURLToPath(new URL('../../', import.meta.url));
const REFUSAL_PATTERNS = [
  'interface-unapproved',
  'invalid-simulation-override',
  'interface-missing',
  'native-only',
  'binding-missing',
  'real-binding-unavailable',
  'story-missing-test',
  'orphan-test',
];

export function measureSkillsFootprint(packageRoot = DEFAULT_ROOT, fs = nativeFs) {
  const skillsDir = join(resolve(packageRoot), 'skills');
  const bySkill = {};
  let totalFiles = 0;
  let totalLines = 0;
  let totalBytes = 0;

  if (!fs.existsSync(skillsDir)) {
    return { total_files: 0, total_lines: 0, total_bytes: 0, by_skill: {} };
  }

  function walkSkill(dir) {
    let files = 0;
    let lines = 0;
    let bytes = 0;
    for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
      if (entry.name.startsWith('.')) continue;
      const full = join(dir, entry.name);
      if (entry.isDirectory()) {
        const sub = walkSkill(full);
        files += sub.files;
        lines += sub.lines;
        bytes += sub.bytes;
      } else if (entry.isFile()) {
        const content = fs.readFileSync(full, 'utf8');
        files += 1;
        bytes += Buffer.byteLength(content, 'utf8');
        lines += content.length === 0 ? 0 : content.split('\n').length;
      }
    }
    return { files, lines, bytes };
  }

  for (const entry of fs.readdirSync(skillsDir, { withFileTypes: true })) {
    if (!entry.isDirectory() || entry.name.startsWith('.')) continue;
    const stats = walkSkill(join(skillsDir, entry.name));
    bySkill[entry.name] = stats;
    totalFiles += stats.files;
    totalLines += stats.lines;
    totalBytes += stats.bytes;
  }

  return {
    total_files: totalFiles,
    total_lines: totalLines,
    total_bytes: totalBytes,
    by_skill: bySkill,
  };
}

export function parseRuntimeCheckOutput(stdout = '', stderr = '', exitCode = 0) {
  const combined = `${stdout ?? ''}\n${stderr ?? ''}`;
  const refusalCodes = [];
  for (const code of REFUSAL_PATTERNS) {
    if (combined.includes(code)) refusalCodes.push(code);
  }
  const genericRefusals = [...combined.matchAll(/\brefused\s*\(([a-z0-9-]+)\)/gi)].map(m => m[1].toLowerCase());
  for (const code of genericRefusals) {
    if (!refusalCodes.includes(code)) refusalCodes.push(code);
  }

  let inputTokens = null;
  let outputTokens = null;
  let tokensUnreported = false;

  const inMatch = combined.match(/([\d,]+)\s*(?:input tokens|\bin\b)/i)
    || combined.match(/"input_tokens"\s*:\s*(\d+)/i);
  if (inMatch) inputTokens = Number(inMatch[1].replaceAll(',', ''));

  if (/output[_ ]tokens\s*:\s*"?unknown"?/i.test(combined) || /tokens:\s*unknown/i.test(combined)) {
    tokensUnreported = true;
  } else {
    const outMatch = combined.match(/([\d,]+)\s*(?:output tokens|\bout\b)/i)
      || combined.match(/"output_tokens"\s*:\s*(\d+)/i);
    if (outMatch) outputTokens = Number(outMatch[1].replaceAll(',', ''));
  }

  const aiCallMatch = combined.match(/(\d+)\s+AI\s+calls?/i);
  const aiCalls = aiCallMatch ? Number(aiCallMatch[1]) : null;
  if (aiCalls && aiCalls > 0 && outputTokens === null) {
    tokensUnreported = true;
  }

  let status = 'fail';
  if (exitCode === 0 && refusalCodes.length === 0 && !/\bno verdict\b/i.test(combined)) {
    status = 'pass';
  } else if (exitCode === 5 || (/\bno verdict\b/i.test(combined) && refusalCodes.includes('native-only'))) {
    status = 'not_run';
  }

  return {
    status,
    exit_code: exitCode,
    refusal_codes: refusalCodes,
    ai_calls: aiCalls,
    input_tokens: Number.isFinite(inputTokens) ? inputTokens : null,
    output_tokens: Number.isFinite(outputTokens) ? outputTokens : null,
    tokens_unreported: tokensUnreported,
  };
}

export function parseAgentSessionUsage(jsonlText = '', { fs = nativeFs, pricing = DEFAULT_PRICING_PER_MILLION } = {}) {
  let inputTokens = 0;
  let cachedTokens = 0;
  let outputTokens = 0;
  const skillPaths = new Set();

  for (const rawLine of String(jsonlText ?? '').split('\n')) {
    const line = rawLine.trim();
    if (!line) continue;
    let event;
    try {
      event = JSON.parse(line);
    } catch {
      continue;
    }

    const usage = event?.usage || event?.token_usage || event?.result?.usage || null;
    if (usage && typeof usage === 'object') {
      const inp = Number(usage.input_tokens ?? usage.prompt_tokens ?? 0) || 0;
      const cached = Number(
        usage.cached_input_tokens
        ?? usage.cache_read_input_tokens
        ?? usage.prompt_tokens_details?.cached_tokens
        ?? 0,
      ) || 0;
      const out = Number(usage.output_tokens ?? usage.completion_tokens ?? 0) || 0;
      inputTokens += inp;
      cachedTokens += cached;
      outputTokens += out;
    }

    const blob = JSON.stringify(event);
    for (const m of blob.matchAll(/([^\s"'`]+?\/skills\/pdd-[a-z-]+\/[^\s"'`]+\.md)/g)) {
      skillPaths.add(m[1]);
    }
  }

  const uncachedInputTokens = Math.max(0, inputTokens - cachedTokens);
  let skillBytes = 0;
  for (const p of skillPaths) {
    try {
      if (fs.existsSync(p) && fs.statSync(p).isFile()) {
        skillBytes += fs.statSync(p).size;
      }
    } catch {
      // Ignore unreadable transient paths.
    }
  }

  return {
    input_tokens: inputTokens,
    cached_tokens: cachedTokens,
    uncached_input_tokens: uncachedInputTokens,
    output_tokens: outputTokens,
    authoring_usd: estimateTokenUsd({
      uncachedInputTokens,
      cachedTokens,
      outputTokens,
      pricing,
    }),
    skill_files_read: skillPaths.size,
    skill_total_bytes: skillBytes,
  };
}

export function normalizeWorkloadRecord(raw = {}) {
  const id = String(raw.workload || raw.id || 'unknown');
  const spec = BENCHMARK_WORKLOADS[id] || {};
  const promptOnly = Number.isFinite(raw.prompt_only_seconds)
    ? raw.prompt_only_seconds
    : (Number.isFinite(raw.prompt_files_only_phase_s) ? raw.prompt_files_only_phase_s : null);
  const totalAuth = Number.isFinite(raw.total_authoring_seconds)
    ? raw.total_authoring_seconds
    : (Number.isFinite(raw.authoring_wall_s) ? raw.authoring_wall_s : null);
  const postPrompt = Number.isFinite(raw.post_prompt_pre_test_seconds)
    ? raw.post_prompt_pre_test_seconds
    : (Number.isFinite(raw.post_prompt_pre_test_s)
      ? raw.post_prompt_pre_test_s
      : (totalAuth !== null && promptOnly !== null ? Math.max(0, roundNum(totalAuth - promptOnly, 2)) : null));

  const lintRaw = raw.pdd_lint_status || {};
  const testRaw = raw.pdd_test_status || raw.first_hosted_test || {};
  const normalizeVerdict = v => {
    const s = String(v || '').toLowerCase();
    if (s === 'pass' || s === 'passed') return 'pass';
    if (s === 'not_run' || s === 'not-run' || s === 'not_invoked') return 'not_run';
    if (s === 'fail' || s === 'failed' || s === 'refused') return 'fail';
    return 'not_run';
  };

  const inputTokens = Number.isFinite(raw.input_tokens) ? raw.input_tokens : null;
  const cachedTokens = Number.isFinite(raw.cached_tokens) ? raw.cached_tokens : 0;
  const uncachedTokens = Number.isFinite(raw.uncached_input_tokens)
    ? raw.uncached_input_tokens
    : (inputTokens !== null ? Math.max(0, inputTokens - cachedTokens) : null);
  const outputTokens = Number.isFinite(raw.output_tokens) ? raw.output_tokens : null;
  const authoringUsd = Number.isFinite(raw.authoring_usd)
    ? raw.authoring_usd
    : (uncachedTokens !== null && outputTokens !== null
      ? estimateTokenUsd({ uncachedInputTokens: uncachedTokens, cachedTokens, outputTokens })
      : null);

  return {
    workload: id,
    label: raw.label || spec.label || id,
    tier: raw.tier || spec.tier || 'small',
    direct_baseline_seconds: Number(raw.direct_baseline_seconds ?? spec.direct_baseline_seconds) || null,
    direct_baseline_tokens: Number(raw.direct_baseline_tokens ?? spec.direct_baseline_tokens) || null,
    direct_baseline_usd: Number(raw.direct_baseline_usd ?? spec.direct_baseline_usd) || null,
    direct_rework_usd: Number(raw.direct_rework_usd ?? spec.direct_rework_usd) || null,
    prompt_only_seconds: roundNum(promptOnly, 2),
    post_prompt_pre_test_seconds: roundNum(postPrompt, 2),
    total_authoring_seconds: roundNum(totalAuth, 2),
    input_tokens: inputTokens,
    cached_tokens: cachedTokens,
    uncached_input_tokens: uncachedTokens,
    output_tokens: outputTokens,
    authoring_usd: roundNum(authoringUsd, 4),
    runtime_usd: Number.isFinite(raw.runtime_usd) ? roundNum(raw.runtime_usd, 4) : null,
    rework_usd: Number.isFinite(raw.rework_usd) ? roundNum(raw.rework_usd, 4) : null,
    existing_repo_sync_ready: Boolean(raw.existing_repo_sync_ready),
    skill_files_read: Number.isFinite(raw.skill_files_read) ? raw.skill_files_read : null,
    skill_total_bytes: Number.isFinite(raw.skill_total_bytes) ? raw.skill_total_bytes : null,
    pdd_lint_status: {
      status: normalizeVerdict(lintRaw.status || lintRaw.verdict),
      duration_seconds: roundNum(Number(lintRaw.duration_seconds ?? lintRaw.duration_s), 2),
      exit_code: Number.isFinite(lintRaw.exit_code) ? lintRaw.exit_code : null,
    },
    pdd_test_status: {
      status: normalizeVerdict(testRaw.status || testRaw.verdict),
      first_try_pass: typeof testRaw.first_try_pass === 'boolean'
        ? testRaw.first_try_pass
        : (normalizeVerdict(testRaw.status || testRaw.verdict) === 'pass'),
      duration_seconds: roundNum(Number(testRaw.duration_seconds ?? testRaw.duration_s), 2),
      exit_code: Number.isFinite(testRaw.exit_code) ? testRaw.exit_code : null,
      ai_calls: Number.isFinite(testRaw.ai_calls) ? testRaw.ai_calls : null,
      input_tokens: Number.isFinite(testRaw.input_tokens) ? testRaw.input_tokens : null,
      output_tokens: Number.isFinite(testRaw.output_tokens) ? testRaw.output_tokens : null,
      tokens_unreported: Boolean(testRaw.tokens_unreported),
      refusal_codes: Array.isArray(testRaw.refusal_codes) ? [...testRaw.refusal_codes] : [],
    },
  };
}

function pctDelta(curr, prev) {
  if (!Number.isFinite(curr) || !Number.isFinite(prev) || prev <= 0) return null;
  return roundNum(((curr - prev) / prev) * 100, 1);
}

export function compareReleaseRuns(candidate = {}, baseline = null, { regressionThresholdPct = 25 } = {}) {
  const warnings = [];
  const workloadComparisons = [];
  const candWorkloads = (candidate.workloads || []).map(normalizeWorkloadRecord);
  const baseMap = new Map(
    ((baseline?.workloads) || []).map(w => {
      const nw = normalizeWorkloadRecord(w);
      return [nw.workload, nw];
    }),
  );

  const candSkillBytes = Number(candidate.skills?.total_bytes ?? 0);
  const baseSkillBytes = Number(baseline?.skills?.total_bytes ?? 0);
  const skillBytesDeltaPct = baseSkillBytes > 0 ? pctDelta(candSkillBytes, baseSkillBytes) : null;
  if (skillBytesDeltaPct !== null && skillBytesDeltaPct > regressionThresholdPct) {
    warnings.push({
      severity: 'advisory',
      kind: 'skill_size_bloat',
      workload: 'all',
      delta_pct: skillBytesDeltaPct,
      message: sanitizePublicText(
        `Bundled skill text grew +${skillBytesDeltaPct}% (${baseSkillBytes.toLocaleString()} B -> ${candSkillBytes.toLocaleString()} B), exceeding +${regressionThresholdPct}% advisory threshold.`,
      ),
    });
  }

  for (const cw of candWorkloads) {
    const bw = baseMap.get(cw.workload) || null;
    const authTimeDelta = bw ? pctDelta(cw.total_authoring_seconds, bw.total_authoring_seconds) : null;
    const postPromptDelta = bw ? pctDelta(cw.post_prompt_pre_test_seconds, bw.post_prompt_pre_test_seconds) : null;
    const inputTokDelta = bw ? pctDelta(cw.input_tokens, bw.input_tokens) : null;
    const outputTokDelta = bw ? pctDelta(cw.output_tokens, bw.output_tokens) : null;
    const usdDelta = bw ? pctDelta(cw.authoring_usd, bw.authoring_usd) : null;

    if (authTimeDelta !== null && authTimeDelta > regressionThresholdPct) {
      warnings.push({
        severity: 'advisory',
        kind: 'authoring_time_regression',
        workload: cw.workload,
        delta_pct: authTimeDelta,
        message: sanitizePublicText(
          `${cw.label}: authoring time rose +${authTimeDelta}% (${bw.total_authoring_seconds}s -> ${cw.total_authoring_seconds}s).`,
        ),
      });
    }

    if (
      postPromptDelta !== null
      && postPromptDelta > regressionThresholdPct
      && (cw.post_prompt_pre_test_seconds ?? 0) >= 15
    ) {
      warnings.push({
        severity: 'advisory',
        kind: 'post_prompt_overhead_regression',
        workload: cw.workload,
        delta_pct: postPromptDelta,
        message: sanitizePublicText(
          `${cw.label}: post-prompt pre-test overhead rose +${postPromptDelta}% (${bw.post_prompt_pre_test_seconds}s -> ${cw.post_prompt_pre_test_seconds}s).`,
        ),
      });
    }

    if (inputTokDelta !== null && inputTokDelta > regressionThresholdPct) {
      warnings.push({
        severity: 'advisory',
        kind: 'input_token_regression',
        workload: cw.workload,
        delta_pct: inputTokDelta,
        message: sanitizePublicText(
          `${cw.label}: authoring input tokens rose +${inputTokDelta}% (${bw.input_tokens?.toLocaleString()} -> ${cw.input_tokens?.toLocaleString()}).`,
        ),
      });
    }

    if (outputTokDelta !== null && outputTokDelta > regressionThresholdPct) {
      warnings.push({
        severity: 'advisory',
        kind: 'output_token_regression',
        workload: cw.workload,
        delta_pct: outputTokDelta,
        message: sanitizePublicText(
          `${cw.label}: authoring output tokens rose +${outputTokDelta}% (${bw.output_tokens?.toLocaleString()} -> ${cw.output_tokens?.toLocaleString()}).`,
        ),
      });
    }

    if (cw.pdd_lint_status.status === 'pass' && cw.pdd_test_status.status === 'fail') {
      const codes = cw.pdd_test_status.refusal_codes.length
        ? ` (${cw.pdd_test_status.refusal_codes.join(', ')})`
        : '';
      warnings.push({
        severity: 'advisory',
        kind: 'lint_test_parity_mismatch',
        workload: cw.workload,
        delta_pct: null,
        message: sanitizePublicText(
          `${cw.label}: pdd lint passed while hosted pdd test failed${codes}.`,
        ),
      });
    }

    if (bw && bw.pdd_test_status.status === 'pass' && cw.pdd_test_status.status !== 'pass') {
      warnings.push({
        severity: 'advisory',
        kind: 'runtime_verdict_regression',
        workload: cw.workload,
        delta_pct: null,
        message: sanitizePublicText(
          `${cw.label}: hosted pdd test regressed from pass in ${baseline.version || 'baseline'} to ${cw.pdd_test_status.status}.`,
        ),
      });
    }

    if (cw.pdd_test_status.tokens_unreported) {
      warnings.push({
        severity: 'advisory',
        kind: 'runtime_tokens_unreported',
        workload: cw.workload,
        delta_pct: null,
        message: sanitizePublicText(
          `${cw.label}: hosted pdd test omitted runtime output token telemetry.`,
        ),
      });
    }

    workloadComparisons.push({
      workload: cw.workload,
      label: cw.label,
      tier: cw.tier,
      authoring_seconds_delta_pct: authTimeDelta,
      post_prompt_seconds_delta_pct: postPromptDelta,
      input_tokens_delta_pct: inputTokDelta,
      output_tokens_delta_pct: outputTokDelta,
      usd_delta_pct: usdDelta,
      lint_status: cw.pdd_lint_status.status,
      test_status: cw.pdd_test_status.status,
      refusal_codes: cw.pdd_test_status.refusal_codes,
    });
  }

  return {
    candidate_version: candidate.version || 'candidate',
    baseline_version: baseline?.version || null,
    threshold_pct: regressionThresholdPct,
    advisory_warning_count: warnings.length,
    warnings,
    workloads: workloadComparisons,
  };
}

function nativeRun(cmd, args, options = {}) {
  const res = spawnSync(cmd, args, {
    encoding: 'utf8',
    timeout: options.timeoutMs ?? 900_000,
    maxBuffer: 32 * 1024 * 1024,
    cwd: options.cwd,
    env: options.env ?? process.env,
  });
  return {
    code: res.status ?? 1,
    stdout: res.stdout ?? '',
    stderr: res.stderr ?? '',
  };
}

export function seedBrownfieldTemplate(armDir, { seedDir = null, fs = nativeFs, run = nativeRun } = {}) {
  if (seedDir && fs.existsSync(resolve(seedDir))) {
    fs.cpSync(resolve(seedDir), armDir, { recursive: true });
    return;
  }
  fs.mkdirSync(join(armDir, 'src'), { recursive: true });
  fs.mkdirSync(join(armDir, 'test'), { recursive: true });
  fs.writeFileSync(join(armDir, 'package.json'), JSON.stringify({
    name: 'brownfield-sync-bench',
    version: '1.0.0',
    type: 'module',
    scripts: { test: 'node --test test/*.test.mjs' },
  }, null, 2) + '\n');
  fs.writeFileSync(join(armDir, 'src/catalog.mjs'), [
    'export function listActiveItems(items = []) {',
    '  return items.filter(item => item && item.active !== false);',
    '}',
    '',
  ].join('\n'));
  fs.writeFileSync(join(armDir, 'src/orders.mjs'), [
    "import { listActiveItems } from './catalog.mjs';",
    'export function computeOrderSubtotal(order, catalog = []) {',
    '  const active = new Map(listActiveItems(catalog).map(i => [i.id, i.priceCents]));',
    '  return (order?.lines || []).reduce((sum, line) => sum + (active.get(line.id) || 0) * (line.qty || 0), 0);',
    '}',
    '',
  ].join('\n'));
  fs.writeFileSync(join(armDir, 'src/summary.mjs'), [
    "import { computeOrderSubtotal } from './orders.mjs';",
    'export function summarizeAccountOrders(orders = [], catalog = []) {',
    '  const totals = orders.map(o => computeOrderSubtotal(o, catalog));',
    '  return { count: orders.length, totalCents: totals.reduce((a, b) => a + b, 0) };',
    '}',
    '',
  ].join('\n'));
  fs.writeFileSync(join(armDir, 'test/existing.test.mjs'), [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { summarizeAccountOrders } from '../src/summary.mjs';",
    "test('preserves existing brownfield order totals', () => {",
    "  const summary = summarizeAccountOrders([{ lines: [{ id: 'a', qty: 2 }] }], [{ id: 'a', priceCents: 250, active: true }]);",
    '  assert.deepEqual(summary, { count: 1, totalCents: 500 });',
    '});',
    '',
  ].join('\n'));
  run('git', ['add', '.'], { cwd: armDir });
  run('git', ['-c', 'user.name=bench', '-c', 'user.email=bench@example.invalid', 'commit', '-qm', 'seed brownfield modules'], { cwd: armDir });
}

function executeFixtureChecks({ workloadId, fixtureDir, pddBin, run = nativeRun, now = Date.now }) {
  const lintStart = now();
  const lintRes = run(process.execPath, [pddBin, 'lint'], { cwd: fixtureDir });
  const lintDuration = (now() - lintStart) / 1000;
  const parsedLint = parseRuntimeCheckOutput(lintRes.stdout, lintRes.stderr, lintRes.code);

  const testStart = now();
  const testRes = run(process.execPath, [pddBin, 'test'], { cwd: fixtureDir });
  const testDuration = (now() - testStart) / 1000;
  const parsedTest = parseRuntimeCheckOutput(testRes.stdout, testRes.stderr, testRes.code);

  return normalizeWorkloadRecord({
    workload: workloadId,
    pdd_lint_status: {
      status: parsedLint.status,
      duration_seconds: lintDuration,
      exit_code: lintRes.code,
    },
    pdd_test_status: {
      ...parsedTest,
      duration_seconds: testDuration,
    },
  });
}

export function executeLiveAgentWorkload({
  workload,
  pddBin,
  packageRoot,
  agentCommand,
  workDirRoot,
  brownfieldSeedDir = null,
  fs = nativeFs,
  run = nativeRun,
  now = Date.now,
}) {
  const armDir = fs.mkdtempSync(join(workDirRoot || tmpdir(), `pdd-bench-${workload.id}-`));
  run('git', ['init', '-q'], { cwd: armDir });
  if (workload.tier === 'brownfield') {
    seedBrownfieldTemplate(armDir, { seedDir: brownfieldSeedDir, fs, run });
  }
  const shimDir = join(armDir, '.bench-shim');
  const shimLog = join(shimDir, 'pdd-calls.jsonl');
  const shimPath = join(shimDir, 'pdd');
  fs.mkdirSync(shimDir, { recursive: true });

  const shimSource = `#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { appendFileSync } from 'node:fs';
const start = Date.now();
const res = spawnSync(${JSON.stringify(process.execPath)}, [${JSON.stringify(pddBin)}, ...process.argv.slice(2)], {
  encoding: 'utf8',
  maxBuffer: 32 * 1024 * 1024,
});
const end = Date.now();
if (res.stdout) process.stdout.write(res.stdout);
if (res.stderr) process.stderr.write(res.stderr);
appendFileSync(${JSON.stringify(shimLog)}, JSON.stringify({
  argv: process.argv.slice(2),
  start_ms: start,
  end_ms: end,
  duration_s: (end - start) / 1000,
  exit_code: res.status ?? 1,
  stdout: res.stdout ?? '',
  stderr: res.stderr ?? '',
}) + '\\n');
process.exit(res.status ?? 1);
`;
  fs.writeFileSync(shimPath, shimSource, { mode: 0o755 });

  const env = { ...process.env, PATH: `${shimDir}:${process.env.PATH || ''}` };
  const cmd = Array.isArray(agentCommand) && agentCommand.length
    ? agentCommand
    : ['codex', 'exec', '--json', '--dangerously-bypass-approvals-and-sandbox', workload.prompt];

  const startMs = now();
  const agentRes = run(cmd[0], cmd.slice(1), { cwd: armDir, env, timeoutMs: 1_200_000 });
  const endMs = now();

  const usage = parseAgentSessionUsage(agentRes.stdout, { fs });
  const skillFootprint = measureSkillsFootprint(packageRoot, fs);

  const calls = fs.existsSync(shimLog)
    ? fs.readFileSync(shimLog, 'utf8').split('\n').filter(Boolean).map(line => JSON.parse(line))
    : [];

  const lintCalls = calls.filter(c => c.argv?.[0] === 'lint' && !c.argv.includes('--help'));
  const testCalls = calls.filter(c => c.argv?.[0] === 'test' && !c.argv.includes('--help') && !c.argv.includes('--files'));
  const firstTestCall = testCalls[0] || null;
  const lintCall = lintCalls.at(-1) || null;
  const testCall = testCalls.at(-1) || null;
  const allCheckCalls = [...lintCalls, ...testCalls].sort((a, b) => a.start_ms - b.start_ms);
  const firstCheckCall = allCheckCalls[0] || null;

  let latestPromptMtimeMs = startMs;
  for (const sub of ['prompts', 'user_stories']) {
    const dir = join(armDir, sub);
    if (!fs.existsSync(dir)) continue;
    for (const name of fs.readdirSync(dir)) {
      const st = fs.statSync(join(dir, name));
      if (st.mtimeMs > latestPromptMtimeMs) latestPromptMtimeMs = st.mtimeMs;
    }
  }

  const authoringEndMs = firstTestCall ? firstTestCall.start_ms : endMs;
  const totalAuthoringSec = Math.max(0, (authoringEndMs - startMs) / 1000);
  const promptOnlySec = Math.min(totalAuthoringSec, Math.max(0, (latestPromptMtimeMs - startMs) / 1000));
  const postPromptSec = Math.max(0, totalAuthoringSec - promptOnlySec);

  const parsedLint = lintCall
    ? parseRuntimeCheckOutput(lintCall.stdout, lintCall.stderr, lintCall.exit_code)
    : { status: 'not_run', exit_code: null };
  const parsedTest = testCall
    ? parseRuntimeCheckOutput(testCall.stdout, testCall.stderr, testCall.exit_code)
    : { status: 'not_run', exit_code: null, refusal_codes: [], input_tokens: null, output_tokens: null, tokens_unreported: false };

  // Measure live rework_usd: 0 when first-try lint & test pass with no retries, else post-first-check repair share + retry test tokens.
  let measuredReworkUsd = null;
  if (Number.isFinite(usage.authoring_usd) && firstCheckCall) {
    const hadCheckFailureOrRetry = lintCalls.length > 1
      || testCalls.length > 1
      || allCheckCalls.some(c => c.exit_code !== 0);
    if (!hadCheckFailureOrRetry) {
      measuredReworkUsd = 0;
    } else {
      const totalSessionMs = Math.max(1, endMs - startMs);
      const reworkWindowMs = Math.max(0, endMs - firstCheckCall.end_ms);
      const authoringReworkShare = usage.authoring_usd * Math.min(1, reworkWindowMs / totalSessionMs);
      let retryRuntimeUsd = 0;
      for (const retryCall of testCalls.slice(1)) {
        const parsedRetry = parseRuntimeCheckOutput(retryCall.stdout, retryCall.stderr, retryCall.exit_code);
        if (Number.isFinite(parsedRetry.input_tokens) && Number.isFinite(parsedRetry.output_tokens)) {
          retryRuntimeUsd += estimateTokenUsd({
            uncachedInputTokens: parsedRetry.input_tokens,
            cachedTokens: 0,
            outputTokens: parsedRetry.output_tokens,
          }) || 0;
        }
      }
      measuredReworkUsd = roundNum(authoringReworkShare + retryRuntimeUsd, 4);
    }
  }

  let existingTestsPass = false;
  if (workload.tier === 'brownfield') {
    const unitRes = run(process.execPath, ['--test', 'test/existing.test.mjs'], { cwd: armDir });
    const promptsDir = join(armDir, 'prompts');
    const storiesDir = join(armDir, 'user_stories');
    let syncedExistingModule = false;
    if (fs.existsSync(promptsDir)) {
      const collectMd = dir => {
        const files = [];
        for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
          const full = join(dir, entry.name);
          if (entry.isDirectory()) files.push(...collectMd(full));
          else if (entry.isFile() && entry.name.endsWith('.prompt.md')) files.push(full);
        }
        return files;
      };
      const promptFiles = collectMd(promptsDir);
      syncedExistingModule = promptFiles.some(pf => {
        const body = fs.readFileSync(pf, 'utf8');
        return /\bsrc\/(?:catalog|orders|summary)\.mjs\b/.test(body) || /\b(?:catalog|orders|summary)\.prompt\.md\b/.test(pf);
      });
    }
    const hasStory = fs.existsSync(storiesDir)
      && fs.readdirSync(storiesDir).some(name => name.endsWith('.md'));
    existingTestsPass = unitRes.code === 0
      && syncedExistingModule
      && hasStory
      && parsedLint.status === 'pass'
      && parsedTest.status === 'pass';
  }

  return normalizeWorkloadRecord({
    workload: workload.id,
    prompt_only_seconds: promptOnlySec,
    post_prompt_pre_test_seconds: postPromptSec,
    total_authoring_seconds: totalAuthoringSec,
    existing_repo_sync_ready: existingTestsPass,
    rework_usd: measuredReworkUsd,
    ...usage,
    skill_total_bytes: usage.skill_total_bytes || skillFootprint.total_bytes,
    pdd_lint_status: {
      status: parsedLint.status,
      duration_seconds: lintCall ? lintCall.duration_s : null,
      exit_code: parsedLint.exit_code,
    },
    pdd_test_status: {
      ...parsedTest,
      first_try_pass: firstTestCall
        ? parseRuntimeCheckOutput(firstTestCall.stdout, firstTestCall.stderr, firstTestCall.exit_code).status === 'pass'
        : false,
      duration_seconds: testCall
        ? roundNum(testCalls.reduce((sum, c) => sum + (Number(c.duration_s) || 0), 0), 2)
        : null,
    },
  });
}

function readJsonFile(path, fs) {
  return JSON.parse(fs.readFileSync(resolve(path), 'utf8'));
}

function readPackageVersion(packageRoot, fs) {
  try {
    return JSON.parse(fs.readFileSync(join(resolve(packageRoot), 'package.json'), 'utf8')).version || 'unknown';
  } catch {
    return 'unknown';
  }
}

export function runReleaseBenchmark(options = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const run = ports.run ?? nativeRun;
  const now = ports.now ?? Date.now;
  const packageRoot = resolve(options.packageRoot || DEFAULT_ROOT);
  const pddBin = resolve(options.pddBin || join(packageRoot, 'bin/pdd.mjs'));

  let candidate;
  if (options.candidateJson) {
    const raw = typeof options.candidateJson === 'string'
      ? readJsonFile(options.candidateJson, fs)
      : options.candidateJson;
    candidate = {
      version: raw.version || readPackageVersion(packageRoot, fs),
      date: raw.date || new Date(now()).toISOString().slice(0, 10),
      skills: raw.skills || measureSkillsFootprint(packageRoot, fs),
      large_codebase_summary: raw.large_codebase_summary || null,
      existing_repo_sync_ready: Boolean(raw.existing_repo_sync_ready),
      workloads: (raw.workloads || []).map(normalizeWorkloadRecord),
    };
  } else {
    const selectedIds = Array.isArray(options.workloads) && options.workloads.length
      ? options.workloads
      : ['snake', '2048', 'task-manager'];
    const workloads = [];
    for (const id of selectedIds) {
      const spec = BENCHMARK_WORKLOADS[id];
      if (!spec) throw new Error(`Unknown benchmark workload: ${id}`);
      if (options.fixtureDirs?.[id]) {
        workloads.push(executeFixtureChecks({
          workloadId: id,
          fixtureDir: resolve(options.fixtureDirs[id]),
          pddBin,
          run,
          now,
        }));
      } else if (options.execute) {
        workloads.push(executeLiveAgentWorkload({
          workload: spec,
          pddBin,
          packageRoot,
          agentCommand: options.agentCommand,
          workDirRoot: options.workDirRoot,
          brownfieldSeedDir: options.brownfieldSeedDir,
          fs,
          run,
          now,
        }));
      } else {
        workloads.push(normalizeWorkloadRecord({ workload: id }));
      }
    }
    candidate = {
      version: options.version || readPackageVersion(packageRoot, fs),
      date: new Date(now()).toISOString().slice(0, 10),
      skills: measureSkillsFootprint(packageRoot, fs),
      existing_repo_sync_ready: Boolean(options.existingRepoSyncReady),
      workloads,
    };
  }

  let baseline = null;
  if (options.baselineJson) {
    const rawBase = typeof options.baselineJson === 'string'
      ? readJsonFile(options.baselineJson, fs)
      : options.baselineJson;
    baseline = {
      version: rawBase.version || 'baseline',
      date: rawBase.date || null,
      skills: rawBase.skills || null,
      workloads: (rawBase.workloads || []).map(normalizeWorkloadRecord),
    };
  }

  const history = Array.isArray(options.history)
    ? options.history
    : (options.historyJson ? readJsonFile(options.historyJson, fs) : []);

  const comparison = compareReleaseRuns(candidate, baseline, {
    regressionThresholdPct: options.regressionThresholdPct ?? 25,
  });
  const northStar = computeNorthStarScorecard({
    releaseRun: candidate,
    observeRuns: options.observeRuns || [],
  });

  const report = sanitizePublicData({
    schema_version: 'pdd.release-benchmark.v1',
    generated_at: new Date(now()).toISOString(),
    candidate,
    baseline,
    history: Array.isArray(history) ? history : [],
    comparison,
    north_star_scorecard: northStar,
  });

  if (options.outFile) {
    const target = resolve(options.outFile);
    fs.mkdirSync(dirname(target), { recursive: true });
    fs.writeFileSync(target, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
  }

  return report;
}

export function formatReleaseBenchmarkSummary(report) {
  const c = report.candidate;
  const ns = report.north_star_scorecard.pdd_vs_direct_coding;
  const speedStr = ns.small_builds.speed_ratio_vs_direct !== null ? `${ns.small_builds.speed_ratio_vs_direct}x` : 'n/a';
  const costStr = ns.small_builds.cost_ratio_vs_direct !== null ? `${ns.small_builds.cost_ratio_vs_direct}x` : 'n/a';
  const passStr = ns.small_builds.first_try_runtime_pass_pct !== null ? `${ns.small_builds.first_try_runtime_pass_pct}%` : 'n/a';
  const speedupStr = ns.large_codebases.feature_iteration_speedup_x !== null ? `${ns.large_codebases.feature_iteration_speedup_x}x` : 'pending';
  const reworkStr = ns.large_codebases.rework_cost_reduction_pct !== null ? `${ns.large_codebases.rework_cost_reduction_pct}%` : 'pending';
  const lines = [
    `PDD Release Benchmark (${c.version} · ${c.date})`,
    `Skills footprint: ${c.skills.total_files} files, ${(c.skills.total_bytes / 1024).toFixed(1)} KB`,
    `Bar 1a (Small builds <=1.0x direct): speed=${speedStr}, cost=${costStr}, first-try pass=${passStr}`,
    `Bar 1b (Large brownfield 2-3x speedup, >50% rework cut): speedup=${speedupStr}, rework cut=${reworkStr}, sync ready=${ns.large_codebases.existing_repo_sync_ready ? 'yes' : 'no'}`,
    `Advisory regression warnings: ${report.comparison.advisory_warning_count}`,
  ];
  for (const w of report.comparison.warnings) {
    lines.push(`  [WARN] ${w.message}`);
  }
  return sanitizePublicText(lines.join('\n'));
}

function parseCliArgs(argv) {
  const opts = { workloads: [], fixtureDirs: {} };
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === '--candidate') opts.candidateJson = argv[++i];
    else if (arg === '--baseline') opts.baselineJson = argv[++i];
    else if (arg === '--history') opts.historyJson = argv[++i];
    else if (arg === '--package-root') opts.packageRoot = argv[++i];
    else if (arg === '--pdd-bin') opts.pddBin = argv[++i];
    else if (arg === '--brownfield-seed-dir') opts.brownfieldSeedDir = argv[++i];
    else if (arg === '--workload') opts.workloads.push(argv[++i]);
    else if (arg === '--fixture') {
      const pair = String(argv[++i] || '');
      const eq = pair.indexOf('=');
      if (eq > 0) opts.fixtureDirs[pair.slice(0, eq)] = pair.slice(eq + 1);
    } else if (arg === '--regression-pct') opts.regressionThresholdPct = Number(argv[++i]);
    else if (arg === '--out') opts.outFile = argv[++i];
    else if (arg === '--execute') opts.execute = true;
    else if (arg === '--json') opts.json = true;
    else if (arg === '--fail-on-regression') opts.failOnRegression = true;
    else if (arg === '--help' || arg === '-h') opts.help = true;
    else throw new Error(`Unknown argument: ${arg}`);
  }
  return opts;
}

const USAGE = `Usage: node scripts/benchmark/run-release-benchmark.mjs [options]
  --candidate FILE          Candidate release benchmark JSON
  --baseline FILE           Previous release baseline JSON for regression comparison
  --history FILE            Multi-version trend array JSON
  --package-root DIR        PDD package root to inspect skills/version
  --brownfield-seed-dir DIR Existing brownfield repo template for --execute brownfield runs
  --workload ID             Workload id (snake, 2048, task-manager, brownfield-repo-sync)
  --fixture ID=DIR          Run pdd lint and pdd test against an authored workspace
  --execute                 Launch live isolated agent authoring runs per workload
  --regression-pct N        Advisory warning threshold percent (default: 25)
  --out FILE                Write structured report JSON to FILE
  --json                    Print JSON report to stdout
`;

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const opts = parseCliArgs(process.argv.slice(2));
    if (opts.help) {
      process.stdout.write(USAGE);
      process.exit(0);
    }
    const report = runReleaseBenchmark(opts);
    if (opts.json) {
      process.stdout.write(`${JSON.stringify(report, null, 2)}\n`);
    } else {
      process.stdout.write(`${formatReleaseBenchmarkSummary(report)}\n`);
    }
    if (opts.failOnRegression && report.comparison.advisory_warning_count > 0) {
      process.exit(1);
    }
  } catch (err) {
    process.stderr.write(`Benchmark error: ${err.message}\n`);
    process.exit(2);
  }
}

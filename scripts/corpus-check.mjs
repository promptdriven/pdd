#!/usr/bin/env node
// G6 Offline 8-Repo Corpus Calibration Runner (`runLocalLint`, 0 AI / 0 network / 0 batch-state writes)
// + Seeded #3574, .only, conflict-marker, and broken-prompt-header recall/precision controls.
import { execFileSync } from 'node:child_process';
import { copyFileSync, existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { performance } from 'node:perf_hooks';
import { fileURLToPath } from 'node:url';
import { runLocalLint } from '../src/core/lint/run-local-lint.mjs';

const SCRIPT_DIR = dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = resolve(SCRIPT_DIR, '..');

const CORPUS_NAMES = [
  'carta_clone',
  'agent-link',
  'pocket',
  'polyglot-js',
  'polyglot-py',
  'polyglot-go',
  'polyglot-rs',
];

const CODE_TEST_NOISE_RE = /\[(test-private-(?:import|access)|fake-test-(?:prompt-read|exists-check|source-match)|test-fixed-sleep|test-unexcused-skip|boundary-mock-only-test)\]/;
const TEACHING_4PART_RE = /^Error:\s+[^:]+:\s+\S+:\d+\s+\[[^\]]+\]\s+.*\bFix:\s+.*\bRerun:\s+/;

export function parseOfflineLintPayload(stdout, status, procError = null, signal = null) {
  if (procError) return { parsedOk: false, parseError: String(procError.message || procError), problems: [], warnings: [] };
  if (signal) return { parsedOk: false, parseError: `process terminated by signal ${signal}`, problems: [], warnings: [] };
  if (typeof status !== 'number') return { parsedOk: false, parseError: `process exited with non-numeric status (${status})`, problems: [], warnings: [] };
  const raw = String(stdout ?? '').trim();
  if (!raw) return { parsedOk: false, parseError: 'empty stdout from pdd lint --local --json', problems: [], warnings: [] };
  let parsed;
  try {
    parsed = JSON.parse(raw);
  } catch (err) {
    return { parsedOk: false, parseError: `invalid JSON: ${err.message}`, problems: [], warnings: [] };
  }
  if (!parsed || typeof parsed !== 'object' || Array.isArray(parsed)) {
    return { parsedOk: false, parseError: 'JSON payload must be an object', problems: [], warnings: [] };
  }
  if (!Array.isArray(parsed.problems) || !Array.isArray(parsed.warnings)) {
    return { parsedOk: false, parseError: 'JSON payload missing required problems[] or warnings[] arrays', problems: [], warnings: [] };
  }
  if (typeof parsed.exit_code !== 'number' || parsed.exit_code !== status) {
    return { parsedOk: false, parseError: `exit_code mismatch (payload=${parsed.exit_code}, process=${status})`, problems: parsed.problems, warnings: parsed.warnings };
  }
  return { parsedOk: true, parseError: null, problems: parsed.problems, warnings: parsed.warnings };
}

export function replaceRequired(text, pattern, replacement, label) {
  let count = 0;
  const re = pattern instanceof RegExp
    ? new RegExp(pattern.source, pattern.flags.includes('g') ? pattern.flags : `${pattern.flags}g`)
    : null;
  let next;
  if (re) {
    next = text.replace(re, () => { count += 1; return replacement; });
  } else {
    const idx = text.indexOf(pattern);
    if (idx >= 0) {
      count = 1;
      next = `${text.slice(0, idx)}${replacement}${text.slice(idx + pattern.length)}`;
    } else {
      next = text;
    }
  }
  if (count <= 0) throw new Error(`Seed replacement "${label}" matched 0 times in fixture`);
  return { text: next, count };
}

function runOfflineLint(repoDir, env, { diff = false, baseRef } = {}) {
  let out = '', err = '';
  const t0 = performance.now();
  const status = runLocalLint(
    { cwd: repoDir, json: true, diff, baseRef },
    {
      env,
      stdout: { write(s) { out += String(s); } },
      stderr: { write(s) { err += String(s); } },
    },
  );
  const ms = Math.round(performance.now() - t0);
  const { parsedOk, parseError, problems, warnings } = parseOfflineLintPayload(out, status, null, null);
  return {
    exitCode: typeof status === 'number' ? status : null,
    signal: null,
    ms,
    parsedOk,
    parseError,
    errors: parsedOk ? problems.length : Math.max(1, problems.length),
    warnings: warnings.length,
    codeTestNoise: warnings.filter(w => CODE_TEST_NOISE_RE.test(String(w))).length,
    portErrors: problems.filter(p => String(p).includes('[native-only-unknown-port]')).length,
    problems,
    stderr: err.trim(),
  };
}

function runSeededControls(cartaCloneDir, scratchRoot, env) {
  const controls = [];

  // 1. Seeded carta_clone #3574 precision + fake-port recall controls.
  const tempCarta = join(scratchRoot, 'carta-seeded-copy');
  const required = [
    'prompts/connector/mcp-server.prompt.md',
    'prompts/connector/access.prompt.md',
    'prompts/connector/governance.prompt.md',
    'contracts/holder.md',
  ];
  const missing = required.find(rel => !existsSync(join(cartaCloneDir, rel)));
  if (missing) {
    controls.push({ name: 'carta_clone setup', ok: false, detail: `Missing ${join(cartaCloneDir, missing)}` });
  } else {
    for (const rel of required) {
      const dst = join(tempCarta, rel);
      mkdirSync(dirname(dst), { recursive: true });
      copyFileSync(join(cartaCloneDir, rel), dst);
    }
    execFileSync('git', ['init', '-q', tempCarta]);
    execFileSync('git', ['-C', tempCarta, 'config', 'user.name', 'Corpus Check']);
    execFileSync('git', ['-C', tempCarta, 'config', 'user.email', 'corpus@example.com']);

    const mcpPath = join(tempCarta, 'prompts/connector/mcp-server.prompt.md');
    let stemOpMcp = readFileSync(mcpPath, 'utf8');
    let posReplacements = 0;
    const posSeeds = [
      [/`invoke_tool`/g, '`access.invoke_tool`', 'invoke_tool -> access.invoke_tool'],
      [/`redeem_view`/g, '`access.redeem_view`', 'redeem_view -> access.redeem_view'],
      [/`register_client`/g, '`governance.register_client`', 'register_client -> governance.register_client'],
      [/`set_field_policy`/g, '`governance.set_field_policy`', 'set_field_policy -> governance.set_field_policy'],
      [/`manage_rollout`/g, '`governance.manage_rollout`', 'manage_rollout -> governance.manage_rollout'],
      [/`manage_grant`/g, '`governance.manage_grant`', 'manage_grant -> governance.manage_grant'],
      [/`rotate_token`/g, '`governance.rotate_token`', 'rotate_token -> governance.rotate_token'],
    ];
    for (const [pat, rep, label] of posSeeds) {
      const r = replaceRequired(stemOpMcp, pat, rep, label);
      stemOpMcp = r.text;
      posReplacements += r.count;
    }
    writeFileSync(mcpPath, stemOpMcp, 'utf8');
    execFileSync('git', ['-C', tempCarta, 'add', '.']);
    execFileSync('git', ['-C', tempCarta, 'commit', '-qm', 'seeded stem.op']);

    const posRes = runOfflineLint(tempCarta, env);
    const posOk = posRes.parsedOk && posRes.exitCode === 0 && posRes.errors === 0 && posRes.portErrors === 0;
    controls.push({
      name: 'carta_clone <stem>.<op> precision',
      ok: posOk,
      ms: posRes.ms,
      detail: posOk
        ? `0 false errors across ${posReplacements} seeded <stem>.<op> refs (access.*, governance.*)`
        : `Expected exit 0 & 0 errors, got exit ${posRes.exitCode} (${posRes.parseError ?? posRes.problems.join(' | ')})`,
    });

    let fakePortMcp = stemOpMcp;
    const r1 = replaceRequired(fakePortMcp, '`access.invoke_tool`', '`access.invoke_tools`', 'typo access.invoke_tools');
    fakePortMcp = r1.text;
    const r2 = replaceRequired(fakePortMcp, '`tokens.verify`', '`phantom_store.read`', 'fake phantom_store.read');
    fakePortMcp = r2.text;
    writeFileSync(mcpPath, fakePortMcp, 'utf8');

    const negRes = runOfflineLint(tempCarta, env);
    const caughtTypo = negRes.problems.find(p => p.includes('[native-only-unknown-port]') && p.includes('"access.invoke_tools"'));
    const caughtFake = negRes.problems.find(p => p.includes('[native-only-unknown-port]') && p.includes('"phantom_store.read"'));
    const teachingOk = Boolean(caughtTypo && caughtFake && TEACHING_4PART_RE.test(caughtTypo) && TEACHING_4PART_RE.test(caughtFake));
    const negOk = negRes.parsedOk && negRes.exitCode === 1 && teachingOk;
    controls.push({
      name: 'carta_clone fake-port recall + 4-part fix',
      ok: negOk,
      ms: negRes.ms,
      detail: negOk
        ? 'exit 1 caught both seeded ports ("access.invoke_tools", "phantom_store.read") with 4-part teaching fixes'
        : `Expected exit 1 + 4-part fixes, got exit ${negRes.exitCode} (${negRes.problems.join(' | ')})`,
    });
  }

  // 2. Seeded hard-error recall controls: .only, conflict markers, and broken-prompt-header (all with 4-part fixes).
  const hardRepo = join(scratchRoot, 'hard-error-seeded');
  mkdirSync(join(hardRepo, 'prompts'), { recursive: true });
  mkdirSync(join(hardRepo, 'src'), { recursive: true });
  mkdirSync(join(hardRepo, 'test'), { recursive: true });
  execFileSync('git', ['init', '-q', '-b', 'main', hardRepo]);
  execFileSync('git', ['-C', hardRepo, 'config', 'user.name', 'Corpus Check']);
  execFileSync('git', ['-C', hardRepo, 'config', 'user.email', 'corpus@example.com']);
  writeFileSync(join(hardRepo, 'prompts/app.prompt.md'), '# App\n\nOwn `src/app.mjs`.\n\n## Dependencies\nNone.\n');
  writeFileSync(join(hardRepo, 'src/app.mjs'), '// Generated from prompts/app.prompt.md.\nexport const ok = true;\n');
  writeFileSync(join(hardRepo, 'test/app.test.mjs'), "test('ok', () => {});\n");
  execFileSync('git', ['-C', hardRepo, 'add', '.']);
  execFileSync('git', ['-C', hardRepo, 'commit', '-qm', 'clean base']);

  // Seed broken-prompt-header + executable .only + conflict markers in working tree.
  writeFileSync(join(hardRepo, 'src/orphan.mjs'), '// Generated from prompts/missing.prompt.md.\nexport const x = 1;\n');
  writeFileSync(join(hardRepo, 'test/app.test.mjs'), "test.only('focused', () => {});\n");
  writeFileSync(join(hardRepo, 'src/conflict.mjs'), '<<<<<<< HEAD\nconst a = 1;\n=======\nconst a = 2;\n>>>>>>> main\n');
  execFileSync('git', ['-C', hardRepo, 'add', 'src/orphan.mjs', 'src/conflict.mjs']);

  const hardRes = runOfflineLint(hardRepo, env, { diff: true, baseRef: 'main' });
  for (const [code, label] of [
    ['broken-prompt-header', 'seeded broken-prompt-header recall + 4-part fix'],
    ['diff-focus-only', 'seeded executable .only recall + 4-part fix'],
    ['diff-conflict-marker', 'seeded conflict-marker recall + 4-part fix'],
  ]) {
    const hit = hardRes.problems.find(p => p.includes(`[${code}]`));
    const ok = Boolean(hardRes.parsedOk && hardRes.exitCode === 1 && hit && TEACHING_4PART_RE.test(hit));
    controls.push({
      name: label,
      ok,
      ms: hardRes.ms,
      detail: ok ? `exit 1 caught [${code}] with 4-part agent-teaching fix` : `Missing or malformed [${code}] in: ${hardRes.problems.join(' | ')}`,
    });
  }

  return { ok: controls.every(c => c.ok), controls };
}

function main(argv) {
  let corpusDir = process.env.PDD_CORPUS_DIR
    ? resolve(process.env.PDD_CORPUS_DIR)
    : resolve(REPO_ROOT, '../corpus');
  let jsonMode = false;

  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--json') jsonMode = true;
    else if (a === '--corpus-dir' && argv[i + 1]) corpusDir = resolve(argv[++i]);
    else {
      process.stderr.write(`Unknown argument: ${a}\nUsage: node scripts/corpus-check.mjs [--corpus-dir DIR] [--json]\n`);
      return 2;
    }
  }

  const scratchRoot = mkdtempSync(join(tmpdir(), 'pdd-corpus-check-'));
  const homeDir = join(scratchRoot, 'home');
  const stateDir = join(scratchRoot, 'state');
  mkdirSync(homeDir, { recursive: true });
  mkdirSync(stateDir, { recursive: true });
  const offlineEnv = { ...process.env, HOME: homeDir, PDD_STATE_DIR: stateDir, PDD_RUNTIME_URL: 'invalid' };

  try {
    const targets = [
      { name: 'wt-lint', dir: REPO_ROOT },
      ...CORPUS_NAMES.map(name => ({ name, dir: join(corpusDir, name) })),
    ];

    const rows = [];
    for (const target of targets) {
      if (!existsSync(target.dir)) {
        rows.push({ name: target.name, dir: target.dir, ok: false, missing: true, exitCode: 1, errors: 1, warnings: 0, codeTestNoise: 0, ms: 0 });
        continue;
      }
      const res = runOfflineLint(target.dir, offlineEnv);
      const speedOk = target.name !== 'agent-link' || res.ms < 3000;
      const ok = res.parsedOk && res.exitCode === 0 && res.errors === 0 && res.codeTestNoise === 0 && speedOk;
      rows.push({ name: target.name, dir: target.dir, ok, missing: false, ...res });
    }

    const stateFilesWritten = readdirSync(stateDir).length;
    const seeded = runSeededControls(join(corpusDir, 'carta_clone'), scratchRoot, offlineEnv);
    const allReposOk = rows.every(r => r.ok) && stateFilesWritten === 0;
    const overallOk = allReposOk && seeded.ok;

    if (jsonMode) {
      process.stdout.write(`${JSON.stringify({
        ok: overallOk,
        stateFilesWritten,
        repos: rows.map(({ problems, stderr, ...rest }) => rest),
        seededControls: seeded.controls,
      }, null, 2)}\n`);
      return overallOk ? 0 : 1;
    }

    const totalErrors = rows.reduce((s, r) => s + r.errors, 0);
    const totalWarnings = rows.reduce((s, r) => s + r.warnings, 0);
    const totalNoise = rows.reduce((s, r) => s + r.codeTestNoise, 0);
    const totalMs = rows.reduce((s, r) => s + r.ms, 0);

    const lines = [
      'G6 8-Repo Offline Corpus Calibration (`runLocalLint`, 0 AI / 0 network / 0 batch-state writes)',
      '',
      'Repo             Exit  Errors  Warnings  CodeNoise  Time(ms)  Status',
      '--------------------------------------------------------------------',
    ];
    for (const r of rows) {
      const status = r.missing ? 'MISSING' : (r.ok ? 'PASS' : 'FAIL');
      const exitLabel = r.exitCode === null ? 'NULL' : String(r.exitCode);
      lines.push(
        `${r.name.padEnd(16)} ${exitLabel.padStart(4)}  ${String(r.errors).padStart(6)}  ${String(r.warnings).padStart(8)}  ${String(r.codeTestNoise).padStart(9)}  ${String(r.ms).padStart(8)}  ${status}`,
      );
    }
    lines.push(
      '--------------------------------------------------------------------',
      `${'TOTAL (8 repos)'.padEnd(16)} ${' '.repeat(4)}  ${String(totalErrors).padStart(6)}  ${String(totalWarnings).padStart(8)}  ${String(totalNoise).padStart(9)}  ${String(totalMs).padStart(8)}  ${allReposOk ? 'PASS' : 'FAIL'}`,
      `Batch-state files written: ${stateFilesWritten}`,
      '',
      'Seeded Recall, Precision & 4-Part Agent-Teaching Controls:',
    );
    for (const c of seeded.controls) {
      lines.push(`  [${c.ok ? 'PASS' : 'FAIL'}] ${c.name} (${c.ms ?? 0}ms): ${c.detail}`);
    }
    lines.push('', `Overall corpus check: ${overallOk ? 'PASS' : 'FAIL'}`);
    process.stdout.write(`${lines.join('\n')}\n`);
    return overallOk ? 0 : 1;
  } finally {
    rmSync(scratchRoot, { recursive: true, force: true });
  }
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  process.exitCode = main(process.argv.slice(2));
}

#!/usr/bin/env node
// Offline 8-Repo Corpus Runner + Seeded carta_clone #3574 Recall & Precision Controls.
import { execFileSync, spawnSync } from 'node:child_process';
import { copyFileSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { performance } from 'node:perf_hooks';
import { fileURLToPath } from 'node:url';

const SCRIPT_DIR = dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = resolve(SCRIPT_DIR, '..');
const PDD_BIN = join(REPO_ROOT, 'bin/pdd.mjs');

const CORPUS_NAMES = [
  'carta_clone',
  'agent-link',
  'pocket',
  'polyglot-js',
  'polyglot-py',
  'polyglot-go',
  'polyglot-rs',
];

function runOfflineLint(repoDir, env) {
  const t0 = performance.now();
  const proc = spawnSync(process.execPath, [PDD_BIN, 'lint', '--local', '--json'], {
    cwd: repoDir,
    env,
    encoding: 'utf8',
    maxBuffer: 32 * 1024 * 1024,
  });
  const ms = Math.round(performance.now() - t0);
  let parsed = null;
  try {
    parsed = JSON.parse(proc.stdout || '{}');
  } catch {
    parsed = null;
  }
  const problems = Array.isArray(parsed?.problems) ? parsed.problems : [];
  const warnings = Array.isArray(parsed?.warnings) ? parsed.warnings : [];
  return {
    exitCode: proc.status ?? 1,
    ms,
    parsedOk: parsed !== null,
    errors: problems.length,
    warnings: warnings.length,
    portErrors: problems.filter(p => String(p).includes('[native-only-unknown-port]')).length,
    sleepWarnings: warnings.filter(w => String(w).includes('[test-fixed-sleep]')).length,
    problems,
    stderr: (proc.stderr || '').trim(),
  };
}

function runCartaCloneSeededControls(cartaCloneDir, scratchRoot, env) {
  const tempRepo = join(scratchRoot, 'carta-seeded-copy');
  const required = [
    'prompts/connector/mcp-server.prompt.md',
    'prompts/connector/access.prompt.md',
    'prompts/connector/governance.prompt.md',
    'contracts/holder.md',
  ];
  for (const rel of required) {
    const src = join(cartaCloneDir, rel);
    if (!existsSync(src)) {
      return {
        ok: false,
        controls: [{ name: 'carta_clone setup', ok: false, detail: `Missing ${src}` }],
      };
    }
    const dst = join(tempRepo, rel);
    mkdirSync(dirname(dst), { recursive: true });
    copyFileSync(src, dst);
  }

  execFileSync('git', ['init', '-q', tempRepo]);
  execFileSync('git', ['-C', tempRepo, 'config', 'user.name', 'Corpus Check']);
  execFileSync('git', ['-C', tempRepo, 'config', 'user.email', 'corpus@example.com']);

  const mcpPath = join(tempRepo, 'prompts/connector/mcp-server.prompt.md');
  const origMcp = readFileSync(mcpPath, 'utf8');

  // Control A: Positive <stem>.<op> exported operation references must pass with 0 errors.
  const stemOpMcp = origMcp
    .replace(/`invoke_tool`/g, '`access.invoke_tool`')
    .replace(/`redeem_view`/g, '`access.redeem_view`')
    .replace(/`register_client`/g, '`governance.register_client`')
    .replace(/`set_field_policy`/g, '`governance.set_field_policy`')
    .replace(/`manage_rollout`/g, '`governance.manage_rollout`')
    .replace(/`manage_grant`/g, '`governance.manage_grant`')
    .replace(/`rotate_token`/g, '`governance.rotate_token`');
  writeFileSync(mcpPath, stemOpMcp, 'utf8');
  execFileSync('git', ['-C', tempRepo, 'add', '.']);
  execFileSync('git', ['-C', tempRepo, 'commit', '-qm', 'seeded stem.op']);

  const posRes = runOfflineLint(tempRepo, env);
  const posOk = posRes.parsedOk && posRes.exitCode === 0 && posRes.portErrors === 0;

  // Control B: Negative seeded fake/typo ports must fail exit 1 and catch both undeclared ports.
  const fakePortMcp = stemOpMcp
    .replace('`access.invoke_tool`', '`access.invoke_tools`')
    .replace('`tokens.verify`', '`phantom_store.read`');
  writeFileSync(mcpPath, fakePortMcp, 'utf8');

  const negRes = runOfflineLint(tempRepo, env);
  const caughtTypo = negRes.problems.some(p => p.includes('[native-only-unknown-port]') && p.includes('"access.invoke_tools"'));
  const caughtFake = negRes.problems.some(p => p.includes('[native-only-unknown-port]') && p.includes('"phantom_store.read"'));
  const negOk = negRes.parsedOk && negRes.exitCode === 1 && caughtTypo && caughtFake;

  const controls = [
    {
      name: 'carta_clone <stem>.<op> precision',
      ok: posOk,
      exitCode: posRes.exitCode,
      errors: posRes.errors,
      portErrors: posRes.portErrors,
      ms: posRes.ms,
      detail: posOk
        ? '0 false native-only-unknown-port errors on access.invoke_tool / access.redeem_view / governance.*'
        : `Expected exit 0 & 0 port errors, got exit ${posRes.exitCode} (${posRes.problems.join(' | ')})`,
    },
    {
      name: 'carta_clone fake-port recall',
      ok: negOk,
      exitCode: negRes.exitCode,
      errors: negRes.errors,
      portErrors: negRes.portErrors,
      ms: negRes.ms,
      detail: negOk
        ? 'exit 1 caught both seeded "access.invoke_tools" typo and "phantom_store.read" fake port'
        : `Expected exit 1 catching both seeded ports, got exit ${negRes.exitCode} (caughtTypo=${caughtTypo}, caughtFake=${caughtFake})`,
    },
  ];
  return { ok: posOk && negOk, controls };
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
  const offlineEnv = {
    ...process.env,
    HOME: homeDir,
    PDD_STATE_DIR: stateDir,
    PDD_RUNTIME_URL: 'invalid',
  };

  try {
    const targets = [
      { name: 'wt-lint', dir: REPO_ROOT },
      ...CORPUS_NAMES.map(name => ({ name, dir: join(corpusDir, name) })),
    ];

    const rows = [];
    for (const target of targets) {
      if (!existsSync(target.dir)) {
        rows.push({
          name: target.name,
          dir: target.dir,
          ok: false,
          missing: true,
          exitCode: 1,
          errors: 1,
          portErrors: 0,
          warnings: 0,
          sleepWarnings: 0,
          ms: 0,
          detail: `Directory not found: ${target.dir}`,
        });
        continue;
      }
      const res = runOfflineLint(target.dir, offlineEnv);
      const ok = res.parsedOk && res.exitCode === 0 && res.errors === 0;
      rows.push({
        name: target.name,
        dir: target.dir,
        ok,
        missing: false,
        ...res,
      });
    }

    const seeded = runCartaCloneSeededControls(join(corpusDir, 'carta_clone'), scratchRoot, offlineEnv);
    const allReposOk = rows.every(r => r.ok);
    const overallOk = allReposOk && seeded.ok;

    if (jsonMode) {
      process.stdout.write(`${JSON.stringify({
        ok: overallOk,
        repos: rows.map(({ problems, stderr, ...rest }) => rest),
        seededControls: seeded.controls,
      }, null, 2)}\n`);
      return overallOk ? 0 : 1;
    }

    const totalErrors = rows.reduce((s, r) => s + r.errors, 0);
    const totalWarnings = rows.reduce((s, r) => s + r.warnings, 0);
    const totalSleep = rows.reduce((s, r) => s + r.sleepWarnings, 0);
    const totalMs = rows.reduce((s, r) => s + r.ms, 0);

    const lines = [
      '8-Repo Offline Corpus Check (`pdd lint --local --json`, 0 network / 0 AI calls)',
      '',
      'Repo             Exit  Errors  Warnings  SleepWarn  Time(ms)  Status',
      '--------------------------------------------------------------------',
    ];
    for (const r of rows) {
      const status = r.missing ? 'MISSING' : (r.ok ? 'PASS' : 'FAIL');
      lines.push(
        `${r.name.padEnd(16)} ${String(r.exitCode).padStart(4)}  ${String(r.errors).padStart(6)}  ${String(r.warnings).padStart(8)}  ${String(r.sleepWarnings).padStart(9)}  ${String(r.ms).padStart(8)}  ${status}`,
      );
    }
    lines.push(
      '--------------------------------------------------------------------',
      `${'TOTAL (8 repos)'.padEnd(16)} ${' '.repeat(4)}  ${String(totalErrors).padStart(6)}  ${String(totalWarnings).padStart(8)}  ${String(totalSleep).padStart(9)}  ${String(totalMs).padStart(8)}  ${allReposOk ? 'PASS' : 'FAIL'}`,
      '',
      'Seeded Recall & Precision Controls (disposable temp copy of carta_clone):',
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

process.exitCode = main(process.argv.slice(2));

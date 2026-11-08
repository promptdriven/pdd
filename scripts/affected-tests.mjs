#!/usr/bin/env node
// Owned by prompts/cli/affected-tests.prompt.md. No network or approval effects.
import { readFileSync, lstatSync, writeFileSync, realpathSync } from 'node:fs';
import { resolve, relative, isAbsolute, join, dirname } from 'node:path';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { constants } from 'node:os';
import { fileURLToPath } from 'node:url';
import { selectAffectedTests } from '../src/affected-tests.mjs';

export function affectedPlan({ root = process.cwd(), base }, ports = {}) {
  const command = ports.command ?? ((args) => {
    const result = spawnSync('git', args, { cwd: root, encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 });
    if (result.error || result.status !== 0) throw Error(`git ${args[0]} failed`);
    return result.stdout;
  });
  const read = ports.read ?? (path => {
    if (!lstatSync(join(root, path)).isFile()) throw Error('nonregular-input');
    return readFileSync(join(root, path));
  });
  const list = args => command(args).split('\0').filter(Boolean);
  let files = {}, current = {}, bytes = {}, changed = [], baseSha = null, head = null, cause, inventoryComplete = true;
  try {
    head = command(['rev-parse', '--verify', 'HEAD^{commit}']).trim();
    const ref = command(['rev-parse', '--verify', '--end-of-options', `${base}^{commit}`]).trim();
    baseSha = command(['merge-base', head, ref]).trim();
    const oldEntries = list(['ls-tree', '-r', '-z', baseSha]).map(row => ({mode:row.slice(0,6),path:row.slice(row.indexOf('\t')+1)}));
    const oldPaths = oldEntries.map(row => row.path);
    changed = [...new Set([...list(['diff', '--name-only', '--no-renames', '-z', baseSha]), ...list(['ls-files', '--others', '--exclude-standard', '-z'])])];
    const paths = list(['ls-files', '-z', '--cached', '--others', '--exclude-standard']);
    const deleted = new Set(list(['ls-files', '--deleted', '-z']));
    for (const path of [...new Set(paths)].sort()) if (!deleted.has(path)) { bytes[path] = read(path); current[path] = bytes[path].toString(); }
    files = { ...current };
    for (const path of oldPaths.filter(path => changed.includes(path))) {
      if (!['100644','100755'].includes(oldEntries.find(row => row.path === path).mode)) throw Error('nonregular-base-input');
      const old = command(['show', `${baseSha}:${path}`]);
      // Retain both edge sets, including removed imports and renamed sources.
      files[path] = Object.hasOwn(files, path) ? `${old}\n${files[path]}` : old;
    }
  } catch (error) { cause = error.message; }
  // A failed base read still inventories all current entries; it cannot yield a
  // successful empty run. Missing/unreadable test inventory is a hard error.
  if (cause) {
    current = {}; bytes = {};
    for (const path of list(['ls-files', '-z', '--cached', '--others', '--exclude-standard'])) {
      try { bytes[path] = read(path); current[path] = bytes[path].toString(); } catch { inventoryComplete = false; if (/^test\/[^/]+\.test\.mjs$/.test(path)) current[path] = ''; }
      if (/^test\/[^/]+\.test\.mjs$/.test(path)) files[path] = current[path] ?? '';
    }
  }
  const plan = selectAffectedTests({ files, changed });
  // Deleted tests remain dependency vertices but are not executable entries.
  plan.tests = plan.tests.filter(path => Object.hasOwn(current, path));
  plan.total = Object.keys(current).filter(path => /^test\/[^/]+\.test\.mjs$/.test(path)).length;
  if (cause) { plan.mode = 'full'; plan.reasons = [cause]; plan.tests = Object.keys(files).filter(path => /^test\/[^/]+\.test\.mjs$/.test(path) && Object.hasOwn(current, path)).sort(); }
  if (!plan.tests.length) throw Error('No runnable native tests; inventory unavailable.');
  const hash = createHash('sha256');
  for (const path of Object.keys(current).sort()) { const value = bytes[path] ?? current[path]; hash.update(JSON.stringify([path, Buffer.byteLength(value)])).update(value); }
  return { ...plan, base: baseSha, head, inventoryComplete, fingerprint: hash.digest('hex') };
}

export function runAffected({ root = process.cwd(), base, run = false, report }, ports = {}) {
  if (report) {
    const target = resolve(root, report);
    let physical;
    try { physical = realpathSync(target); } catch { physical = join(realpathSync(dirname(target)), target.split('/').at(-1)); }
    const rel = relative(realpathSync(root), physical);
    if (!rel.startsWith(`..${process.platform === 'win32' ? '\\' : '/'}`) && !isAbsolute(rel)) throw Error('Reports must be outside the repository.');
  }
  const plan = (ports.plan ?? affectedPlan)({ root, base });
  if (!run) return { plan, exitCode: 0 };
  const now = ports.now ?? Date.now, startedAt = now();
  const execute = ports.execute ?? ((command, args, options) => spawnSync(command, args, options));
  const full = plan.mode === 'full';
  const result = execute(full ? 'bash' : process.execPath,
    full ? [join(root, 'scripts/vm-suite-lock.sh')] : ['--test', ...plan.tests],
    { cwd: root, encoding: 'utf8', maxBuffer: 64 * 1024 * 1024, env: { ...process.env, ...(full ? { SUITE: 'npm test' } : {}) } });
  const finishedAt = now();
  let exitCode = result.signal ? 128 + (constants.signals[result.signal] ?? 0) : result.status ?? 1;
  const output = `${result.stdout ?? ''}\n${result.stderr ?? ''}`.replace(/\r/g, '');
  const footer = output.match(/^# tests (\d+)\n# suites \d+\n# pass (\d+)\n# fail (\d+)\n# cancelled (\d+)\n# skipped (\d+)\n# todo (\d+)\n# duration_ms [\d.]+(?:\n|$)/gm)?.at(-1);
  const values = footer?.match(/^# (?:tests|pass|fail|cancelled|skipped|todo) (\d+)$/gm)?.map(line => Number(line.split(' ').at(-1)));
  const counts = values?.length === 6 && values[0] > 0 && values[0] === values.slice(1).reduce((a,b) => a+b,0)
    ? Object.fromEntries(['tests','pass','fail','cancelled','skipped','todo'].map((key,i) => [key,values[i]])) : null;
  let stale = true;
  try { const after = (ports.plan ?? affectedPlan)({ root, base }); stale = !plan.inventoryComplete || !after.inventoryComplete || after.fingerprint !== plan.fingerprint || after.head !== plan.head || after.base !== plan.base; } catch {}
  if (stale || !counts || counts.fail || counts.cancelled) exitCode ||= 1;
  const evidence = { ...plan, startedAt, finishedAt, elapsedMinutes: (finishedAt - startedAt) / 60000, suiteMinutes: full ? null : (finishedAt - startedAt) / 60000, exitCode, counts, stale, signal: result.signal ?? null, error: result.error?.message ?? null };
  if (report) (ports.write ?? writeFileSync)(resolve(root, report), `${JSON.stringify(evidence, null, 2)}\n`);
  return { plan, evidence, exitCode, stdout: result.stdout, stderr: result.stderr };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const args = process.argv.slice(2), options = {};
    while (args.length) {
      const arg = args.shift();
      if (arg === '--run') options.run = true;
      else if (['--base', '--report'].includes(arg) && args[0]) options[arg.slice(2)] = args.shift();
      else throw Error('Usage: node scripts/affected-tests.mjs --base REF [--run] [--report PATH]');
    }
    if (!options.base) throw Error('--base is required');
    const result = runAffected(options);
    if (result.stdout) process.stdout.write(result.stdout);
    if (result.stderr) process.stderr.write(result.stderr);
    console.log(JSON.stringify(result.evidence ?? result.plan, null, 2));
    process.exitCode = result.exitCode;
    if (result.evidence?.signal) process.kill(process.pid, result.evidence.signal);
  } catch (error) { console.error(error.message); process.exitCode = 1; }
}

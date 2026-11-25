#!/usr/bin/env node
import { execFileSync, spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { cpSync, existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, realpathSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, relative, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const sha = s => createHash('sha256').update(s).digest('hex').slice(0, 16);
const sub = (s, v) => String(s).replace(/\{(\w+)\}/g, (m, k) => (k in v ? v[k] : m));
const isExec = p => existsSync(p) && statSync(p).isFile() && (statSync(p).mode & 0o111) !== 0 && !/\.(?:tgz|tar\.gz|whl|zip)$/i.test(p);
const sortKeys = x => Array.isArray(x) ? x.map(sortKeys) : (x && typeof x === 'object' ? Object.fromEntries(Object.keys(x).sort().map(k => [k, sortKeys(x[k])])) : x);
const pick = o => o ? { exit: o.exit, ms: o.ms, hash: o.hash, filesHash: o.filesHash } : null;
const mkDirs = (sbx, list) => list.forEach(d => mkdirSync(join(sbx, d), { recursive: true }));
const sameRes = (a, b) => a.exit === b.exit && a.hash === b.hash && a.filesHash === b.filesHash;
const parseArgs = argv => { const a = {}; for (let i = 0; i < argv.length; i++) if (argv[i].startsWith('--')) a[argv[i].slice(2)] = argv[i + 1] && !argv[i + 1].startsWith('--') ? argv[++i] : true; return a; };

function applyMasks(text, masks = [], sbx = '', forPath = false) {
  let out = String(text ?? '');
  if (sbx) { out = out.replaceAll(sbx, '<SANDBOX>'); try { const rp = realpathSync(sbx); if (rp !== sbx) out = out.replaceAll(rp, '<SANDBOX>'); } catch {} }
  for (const m of masks) {
    if (m.replace) out = out.replaceAll(sub(m.replace, { sandbox: sbx }), m.with ?? '');
    if (m.regex) out = out.replace(new RegExp(m.regex, 'g'), m.with ?? '');
    if (!forPath && m.sortJsonKeys && out.trim()) { try { out = JSON.stringify(sortKeys(JSON.parse(out))); } catch {} }
  }
  return out;
}

function makeEnv(sbx, suiteEnv, probeEnv) {
  const env = { PATH: process.env.PATH || '/usr/local/bin:/usr/bin:/bin', TZ: 'UTC', LANG: 'C.UTF-8', NO_COLOR: '1', COLUMNS: '120', HOME: join(sbx, 'home'), TMPDIR: join(sbx, 'tmp') };
  for (const src of [suiteEnv, probeEnv]) for (const [k, v] of Object.entries(src || {})) if (v === '' || v == null) delete env[k]; else env[k] = sub(v, { sandbox: sbx });
  return env;
}

function snapTree(root, skipGit) {
  const map = new Map();
  if (!existsSync(root)) return map;
  const walk = d => readdirSync(d, { withFileTypes: true }).forEach(e => {
    if (skipGit && e.name === '.git') return;
    const p = join(d, e.name);
    if (e.isDirectory()) walk(p); else if (e.isFile()) map.set(relative(root, p), sha(readFileSync(p)));
  });
  walk(root);
  return map;
}

function diffTrees(before, dirs, masks, sbx) {
  const ignore = (masks || []).filter(m => m.ignorePath).map(m => new RegExp(m.ignorePath)), out = {};
  for (const [tag, dir, skipGit] of dirs) {
    const pre = before[tag], post = snapTree(dir, skipGit);
    for (const [rel, h] of post) {
      if (pre.get(rel) === h || ignore.some(re => re.test(rel))) continue;
      let body; try { body = applyMasks(readFileSync(join(dir, rel), 'utf8'), masks, sbx); } catch { body = h; }
      out[`${tag}/${applyMasks(rel, masks, sbx, true)}`] = sha(body);
    }
    for (const rel of pre.keys()) if (!post.has(rel) && !ignore.some(re => re.test(rel))) out[`${tag}/${applyMasks(rel, masks, sbx, true)}`] = 'DELETED';
  }
  return Object.fromEntries(Object.keys(out).sort().map(k => [k, out[k]]));
}

function prepSandbox(runDir, label, target, suiteDir) {
  const sbx = join(runDir, label), dst = join(sbx, 'target');
  mkDirs(sbx, ['home', 'tmp', 'state', 'target', 'prefix']);
  if (target.home) cpSync(resolve(suiteDir, '..', target.home), join(sbx, 'home'), { recursive: true });
  cpSync(resolve(suiteDir, '..', target.from), dst, { recursive: true });
  if (target.ref) execFileSync('git', ['checkout', '-q', target.ref], { cwd: dst, stdio: 'pipe' });
  else if (target.gitInit && !existsSync(join(dst, '.git'))) { execFileSync('git', ['init', '-q'], { cwd: dst, stdio: 'pipe' }); execFileSync('git', ['add', '-A'], { cwd: dst, stdio: 'pipe' }); execFileSync('git', ['-c', 'user.name=ev', '-c', 'user.email=ev@local', 'commit', '-qm', 'init'], { cwd: dst, stdio: 'pipe' }); }
  return { sbx, cwd: dst };
}

function installInto(sbx, spec, suite) {
  mkDirs(sbx, ['home', 'tmp', 'state', 'prefix']);
  const resolved = existsSync(spec) ? resolve(spec) : spec;
  if (!suite.sides?.install || isExec(resolved)) return { spec: resolved, cmd: resolved, installed: false };
  const r = spawnSync('sh', ['-c', sub(suite.sides.install, { sandbox: sbx, artifact: resolved })], { env: makeEnv(sbx, suite.env), encoding: 'utf8', timeout: 180_000 });
  if (r.status !== 0) throw new Error(`Install failed (${r.status}): ${(r.stderr || r.stdout || '').trim().slice(0, 200)}`);
  return { spec: resolved, cmd: sub(suite.sides.cmd, { sandbox: sbx }), installed: true };
}

function observe(argv, { sbx, cwd, env, timeout, masks, vars }) {
  const trees = [['target', cwd, true], ['home', join(sbx, 'home'), false], ['state', join(sbx, 'state'), false]];
  const before = Object.fromEntries(trees.map(([t, d, g]) => [t, snapTree(d, g)]));
  const cmd = argv.map(x => sub(x, vars)), t0 = performance.now();
  const r = spawnSync(cmd[0], cmd.slice(1), { cwd, env, encoding: 'utf8', timeout: timeout ?? 60_000, maxBuffer: 32 * 1024 * 1024 });
  const ms = Math.round(performance.now() - t0), timedOut = r.error?.code === 'ETIMEDOUT';
  const exit = timedOut ? 124 : (r.status ?? 1), out = applyMasks(r.stdout, masks, sbx), err = applyMasks(r.stderr, masks, sbx);
  const files = diffTrees(before, trees, masks, sbx);
  return { exit, ms, timedOut, out, err, hash: sha(`${out}\n--ERR--\n${err}`), filesHash: sha(JSON.stringify(files)), files };
}

function shortDiff(a, b) {
  const parts = [];
  if (a.exit !== b.exit) parts.push(`exit ${a.exit}->${b.exit}`);
  if (a.hash !== b.hash) {
    const sa = `${a.out}\n${a.err}`, sb = `${b.out}\n${b.err}`;
    let i = 0; while (i < sa.length && i < sb.length && sa[i] === sb[i]) i++;
    const s = Math.max(0, i - 16), clip = x => x.slice(s, i + 44).replace(/\n/g, '\\n');
    parts.push(`out @${i}: "${clip(sa)}" vs "${clip(sb)}"`);
  }
  if (a.filesHash !== b.filesHash) parts.push(`files ${Object.keys(a.files).length}->${Object.keys(b.files).length}`);
  return parts.join('; ') || 'diff';
}

async function main() {
  const args = parseArgs(process.argv.slice(2));
  if (!args.suite || !args.cand) { console.error('Usage: evidence-run.mjs --suite <path> [--base <art|cmd>] --cand <art|cmd> [--repro <script>] [--out <rows.json>] [--must-red <N>]'); process.exit(2); }
  const suitePath = resolve(args.suite), suiteDir = dirname(suitePath), suite = (await import(pathToFileURL(suitePath).href)).default;
  const runDir = mkdtempSync(join(tmpdir(), 'evrun-')), rows = [], cleanCache = new Map();
  let seq = 0;
  try {
    const baseSide = args.base ? installInto(join(runDir, 'side-base'), args.base, suite) : null;
    const candSide = installInto(join(runDir, 'side-cand'), args.cand, suite);
    const targets = new Map((suite.targets || []).map(t => [t.id, t])), probes = [...(suite.probes || [])];
    if (args.repro) { const rp = resolve(args.repro); probes.push({ id: 'repro', run: /\.[cm]?js$/.test(rp) ? ['node', rp, '{cmd}'] : [rp, '{cmd}'], judge: 'flip', on: [suite.targets?.[0]?.id] }); }
    const runProbe = (probe, target, side, tag, patchPath) => {
      const { sbx, cwd } = prepSandbox(runDir, `r${++seq}-${tag}`, target, suiteDir);
      if (patchPath) { const pr = spawnSync('git', ['apply', '--whitespace=nowarn', patchPath], { cwd, encoding: 'utf8' }); if (pr.status !== 0) return { patchErr: (pr.stderr || pr.stdout || 'git apply failed').trim() }; }
      return observe(probe.run, { sbx, cwd, env: makeEnv(sbx, suite.env, probe.env), timeout: probe.timeout, masks: suite.masks, vars: { cmd: side.cmd, sandbox: sbx, cand: candSide.spec, target: cwd, suiteDir } });
    };

    for (const p of probes) for (const tid of (Array.isArray(p.on) ? p.on : (p.on ? [p.on] : [...targets.keys()]))) {
      const target = targets.get(tid), row = { id: `${p.id}@${tid}`, probe: p.id, target: tid, judge: p.judge, status: 'not-proved', reason: '', base: null, cand: null };
      if (!target) { row.reason = 'unknown target'; rows.push(row); continue; }
      if (p.judge === 'same') {
        if (!baseSide) row.reason = 'no base';
        else {
          const a1 = runProbe(p, target, baseSide, 'a1'), a2 = runProbe(p, target, baseSide, 'a2'); row.base = pick(a1);
          if (a1.timedOut || a2.timedOut) row.reason = 'timeout on base';
          else if (!sameRes(a1, a2)) row.reason = `unstable (A/A: ${shortDiff(a1, a2)})`;
          else {
            const c = runProbe(p, target, candSide, 'c'); row.cand = pick(c); cleanCache.set(row.id, c);
            if (c.timedOut) row.reason = 'timeout on cand';
            else { row.status = sameRes(a1, c) ? 'pass' : 'fail'; row.reason = row.status === 'pass' ? 'identical' : shortDiff(a1, c); }
          }
        }
      } else if (p.judge === 'flip') {
        if (!baseSide) row.reason = 'no base';
        else {
          const b = runProbe(p, target, baseSide, 'fb'); row.base = pick(b);
          if (b.exit === 0 || (p.symptom && !new RegExp(p.symptom).test(`${b.out}\n${b.err}`))) row.reason = 'repro did not fail on base';
          else { const c = runProbe(p, target, candSide, 'fc'); row.cand = pick(c); row.status = c.exit === 0 ? 'pass' : 'fail'; row.reason = c.exit === 0 ? 'flipped fail->pass' : `still fails (exit ${c.exit})`; }
        }
      } else if (p.judge === 'upgrade') {
        if (!baseSide) row.reason = 'no base';
        else {
          const { sbx, cwd } = prepSandbox(runDir, `u${++seq}`, target, suiteDir), uBase = installInto(sbx, args.base, suite);
          const env = makeEnv(sbx, suite.env, p.env), vars = { cmd: uBase.cmd, sandbox: sbx, cand: candSide.spec, target: cwd, suiteDir };
          const sRes = p.seed ? observe(p.seed, { sbx, cwd, env, timeout: p.timeout, masks: suite.masks, vars }) : { exit: 0, ms: 0 }; row.base = pick(sRes);
          if (sRes.exit !== 0) row.reason = `seed failed (exit ${sRes.exit})`;
          else {
            let hRes = { exit: 0, ms: 0, out: '', err: '' };
            if (p.handoff) hRes = observe(p.handoff, { sbx, cwd, env, timeout: 180_000, masks: suite.masks, vars });
            else { try { installInto(sbx, args.cand, suite); } catch (e) { hRes = { exit: 1, ms: 0, out: '', err: e.message }; } }
            const msg = (hRes.err || hRes.out).split('\n').find(Boolean)?.slice(0, 96) || '';
            if (hRes.exit === 3) { row.cand = pick(hRes); row.reason = msg || 'upgrade not proved'; }
            else if (hRes.exit !== 0) { row.status = 'fail'; row.cand = pick(hRes); row.reason = `upgrade handoff failed (exit ${hRes.exit}): ${msg}`; }
            else {
              const newCmd = suite.sides?.install && !isExec(candSide.spec) ? sub(suite.sides.cmd, { sandbox: sbx }) : candSide.cmd;
              const c = observe(p.run, { sbx, cwd, env, timeout: p.timeout, masks: suite.masks, vars: { ...vars, cmd: newCmd } });
              row.cand = pick(c); row.status = c.exit === 0 ? 'pass' : 'fail'; row.reason = c.exit === 0 ? 'upgraded cleanly' : `post-upgrade failed (exit ${c.exit})`;
            }
          }
        }
      } else if (p.judge === 'expect') {
        const c = runProbe(p, target, candSide, 'ex'); row.cand = pick(c); const ex = p.expect || {};
        if (ex.notProvedExit !== undefined && c.exit === ex.notProvedExit) row.reason = (c.err || c.out).split('\n').find(Boolean)?.slice(0, 100) || 'not proved';
        else { const ok = (Array.isArray(ex.exit) ? ex.exit : [ex.exit ?? 0]).includes(c.exit) && (!ex.contains || `${c.out}\n${c.err}`.includes(ex.contains)) && (!ex.notContains || !`${c.out}\n${c.err}`.includes(ex.notContains)); row.status = ok ? 'pass' : 'fail'; row.reason = ok ? 'matched expectation' : `exit ${c.exit} (expected ${ex.exit ?? 0})`; }
      } else row.reason = `unknown judge "${p.judge}"`;
      rows.push(row);
    }

    for (const ctrl of suite.controls || []) {
      const target = targets.get(ctrl.on || suite.targets?.[0]?.id), probe = probes.find(x => x.id === ctrl.probe);
      const row = { id: `ctrl:${ctrl.id}`, probe: ctrl.probe, target: target?.id || '?', judge: `control:${ctrl.must}`, status: 'not-proved', reason: '', base: null, cand: null };
      if (!target || !probe) { row.reason = 'invalid control target/probe'; rows.push(row); continue; }
      const clean = cleanCache.get(`${probe.id}@${target.id}`) ?? runProbe(probe, target, candSide, 'cc'); cleanCache.set(`${probe.id}@${target.id}`, clean);
      const mut = runProbe(probe, target, candSide, 'cm', resolve(suiteDir, '..', ctrl.patch)); row.base = pick(clean);
      if (mut.patchErr) { row.reason = `patch error: ${mut.patchErr.slice(0, 80)}`; rows.push(row); continue; }
      row.cand = pick(mut);
      if (ctrl.must === 'red') { const ok = mut.exit !== 0 && (mut.exit !== clean.exit || mut.hash !== clean.hash); row.status = ok ? 'pass' : 'fail'; row.reason = ok ? `caught (red, exit ${mut.exit})` : 'blind: fault stayed green'; }
      else if (ctrl.must === 'same') { const ok = mut.exit === clean.exit && mut.hash === clean.hash; row.status = ok ? 'pass' : 'fail'; row.reason = ok ? 'edit ignored (same)' : `changed: ${shortDiff(clean, mut)}`; }
      else row.reason = `unknown control must "${ctrl.must}"`;
      rows.push(row);
    }

    const counts = { pass: 0, fail: 0, 'not-proved': 0 }; rows.forEach(r => counts[r.status]++);
    const redOk = rows.some(r => r.judge === 'control:red' && r.status === 'pass'), need = args['must-red'] !== undefined ? Number(args['must-red']) : null;
    const gotRed = rows.filter(r => !r.judge.startsWith('control:') && r.status === 'fail').length;
    const [verdict, exitCode] = need !== null ? (gotRed >= need ? [`self-test pass (${gotRed} >= ${need} red)`, 0] : [`self-test fail (${gotRed} < ${need} red)`, 1])
      : (!rows.length || (!counts.fail && (counts['not-proved'] > 0 || !redOk))) ? [!rows.length ? 'not-proved (0 rows)' : !redOk ? 'not-proved (no red control)' : 'not-proved', 3] : counts.fail > 0 ? ['fail', 1] : ['pass', 0];
    const report = { schema: 'evidence-run.v1', network: 'open', suite: args.suite, base: args.base ?? null, cand: args.cand, verdict, exitCode, counts, rows };
    if (args.out) writeFileSync(resolve(args.out), JSON.stringify(report, null, 2) + '\n');
    console.log(`Evidence Run | network: open | base: ${args.base ?? '(none)'} | cand: ${args.cand}\n${'ROW'.padEnd(32)} ${'JUDGE'.padEnd(13)} ${'STATUS'.padEnd(11)} ${'EXIT'.padEnd(7)} ${'MS'.padStart(6)}  REASON\n${'-'.repeat(110)}`);
    for (const r of rows) console.log(`${r.id.slice(0, 32).padEnd(32)} ${r.judge.slice(0, 13).padEnd(13)} ${r.status.padEnd(11)} ${`${r.base?.exit ?? '-'}->${r.cand?.exit ?? '-'}`.padEnd(7)} ${String(r.cand?.ms ?? r.base?.ms ?? '-').padStart(6)}  ${r.reason}`);
    console.log(`\nVerdict: ${verdict} (pass=${counts.pass}, fail=${counts.fail}, not-proved=${counts['not-proved']})`);
    process.exitCode = exitCode;
  } finally { rmSync(runDir, { recursive: true, force: true }); }
}
main().catch(e => { console.error(e.stack || e.message); process.exit(1); });

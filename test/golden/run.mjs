import { spawnSync, execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, readFileSync, readdirSync, realpathSync, rmSync, statSync, symlinkSync, writeFileSync } from 'node:fs';
import { hostname, tmpdir, userInfo } from 'node:os';
import { dirname, join, relative, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { cases } from './cases.mjs';

const harnessDir = dirname(fileURLToPath(import.meta.url));
const harnessRoot = resolve(harnessDir, '../..');
const casesRoot = join(realpathSync(tmpdir()), 'pdd-golden-cases');
const realGit = execFileSync('/bin/sh', ['-c', 'command -v git'], { encoding: 'utf8' }).trim();
const fixedGitDate = '2026-11-13T12:00:00Z';
const nodeTools = ['gh', 'herdr', 'codex', 'claude', 'launchctl', 'systemctl', 'loginctl'];
const textLimit = 8192;
const detachedWaitMs = 15000;

const quote = value => `'${String(value).replaceAll("'", "'\\''")}'`;
const sha256 = data => createHash('sha256').update(data).digest('hex');

function writeShims(bin, control, remotes) {
  mkdirSync(bin, { recursive: true });
  symlinkSync(process.execPath, join(bin, 'node'));
  const shim = join(harnessDir, 'shim.mjs');
  for (const tool of nodeTools) writeFileSync(join(bin, tool), `#!/bin/sh\nexec ${quote(process.execPath)} ${quote(shim)} ${quote(control)} ${tool} "$@"\n`, { mode: 0o755 });
  writeFileSync(join(bin, 'git'), [
    '#!/bin/sh',
    'separator=$(printf \'\\037\')',
    'record="git$separator$PWD$separator"',
    'for word in "$@"; do record="$record$separator$word"; done',
    `printf '%s\\036' "$record" >> ${quote(join(control, 'calls.log'))}`,
    `case "$1 $2" in "remote get-url") exec ${quote(realGit)} "$@";; esac`,
    `exec ${quote(realGit)} -c ${quote(`url.file://${remotes}/.insteadOf=https://github.com/`)} "$@"`, ''].join('\n'), { mode: 0o755 });
}

function caseEnvironment(root, extra) {
  const home = join(root, 'home'), bin = join(root, 'bin');
  return {
    HOME: home, USERPROFILE: home, TMPDIR: join(root, 'tmp'), PATH: `${bin}:/usr/bin:/bin:/usr/sbin:/sbin`,
    TZ: 'UTC', LC_ALL: 'C', LANG: 'C', NO_COLOR: '1', TERM: 'dumb',
    GIT_CONFIG_NOSYSTEM: '1', GIT_TERMINAL_PROMPT: '0', GIT_CONFIG_GLOBAL: join(home, '.gitconfig'),
    GIT_AUTHOR_DATE: fixedGitDate, GIT_COMMITTER_DATE: fixedGitDate,
    PDD_RUNTIME_URL: 'http://127.0.0.1:1',
    ...extra,
  };
}

function prepare(testCase, checkout) {
  const root = join(casesRoot, testCase.id);
  rmSync(root, { recursive: true, force: true });
  const repo = join(root, 'project'), home = join(root, 'home'), control = join(root, '.golden');
  for (const folder of [repo, home, join(root, 'tmp'), control]) mkdirSync(folder, { recursive: true });
  writeFileSync(join(home, '.gitconfig'), '[user]\n\tname = Golden Fixture\n\temail = golden@example.invalid\n[init]\n\tdefaultBranch = main\n');
  writeShims(join(root, 'bin'), control, join(root, 'remotes'));
  const env = caseEnvironment(root, testCase.env);
  const git = (cwd, ...args) => execFileSync(realGit, args, { cwd, env, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }).trim();
  const pdd = (args, { cwd = repo } = {}) => spawnSync(process.execPath, [join(checkout, 'bin/pdd.mjs'), ...args], { cwd, env, input: '', encoding: 'utf8', timeout: 60000 });
  const context = { root, repo, home, control, env, git, pdd, checkout, harnessRoot, world: structuredClone(testCase.world ?? {}), now: Date.now() };
  testCase.build?.(context);
  writeFileSync(join(control, 'world.json'), JSON.stringify(context.world));
  for (const step of testCase.setup ?? []) step(context);
  waitForDetached(root);
  rmSync(join(control, 'calls.log'), { force: true });
  return context;
}

function listFiles(root) {
  const files = new Map();
  const visit = folder => {
    for (const entry of readdirSync(folder, { withFileTypes: true })) {
      const path = join(folder, entry.name), name = relative(root, path);
      if (name === 'bin' || name === '.golden' || name === 'remotes') continue;
      if (entry.isDirectory() && entry.name === '.git') { if (existsSync(join(path, 'pdd'))) visit(join(path, 'pdd')); continue; }
      if (entry.isDirectory()) { visit(path); continue; }
      if (entry.isSymbolicLink()) { files.set(name, { link: linkTarget(path) }); continue; }
      if (!entry.isFile()) continue;
      const data = readFileSync(path);
      files.set(name, { data, mode: (statSync(path).mode & 0o777).toString(8) });
    }
  };
  visit(root);
  return files;
}
const linkTarget = path => { try { return realpathSync(path); } catch { return '(broken link)'; } };

function changedFiles(before, after, normalize) {
  const rows = [];
  for (const [name, now] of after) {
    const old = before.get(name);
    const same = old && (now.link ? old.link === now.link : old.data && Buffer.compare(old.data, now.data) === 0 && old.mode === now.mode);
    if (same) continue;
    rows.push({ path: normalize(name), change: old ? 'changed' : 'added', ...describeFile(now, normalize) });
  }
  for (const name of before.keys()) if (!after.has(name)) rows.push({ path: normalize(name), change: 'removed' });
  for (const row of rows) row.path = row.path.replace(/(^|\/)[0-9a-f]{64}(?=\.[a-z]+$|$)/, '$1<CONTENT_HASH>');
  rows.sort((a, b) => a.path.localeCompare(b.path) || String(a.sha256).localeCompare(String(b.sha256)));
  const seen = new Map();
  for (const row of rows) { const count = seen.get(row.path) ?? 0; seen.set(row.path, count + 1); if (count) row.path = `${row.path}#${count + 1}`; }
  return rows;
}

function describeFile(file, normalize) {
  if (file.link) return { link: normalize(file.link) };
  const text = file.data.toString('utf8');
  if (text.includes('\u0000') || Buffer.compare(Buffer.from(text, 'utf8'), file.data) !== 0) return { mode: file.mode, sha256: sha256(file.data), bytes: file.data.length };
  const clean = normalizeFileText(text, normalize);
  return { mode: file.mode, sha256: sha256(clean), ...(clean.length <= textLimit ? { text: clean } : { bytes: clean.length }) };
}

function normalizeFileText(text, normalize) {
  try { return JSON.stringify(normalizeValue(JSON.parse(text), normalize), null, 1); } catch { return normalize(text); }
}
const normalizeValue = (value, normalize) => Array.isArray(value) ? value.map(item => normalizeValue(item, normalize))
  : value && typeof value === 'object' ? Object.fromEntries(Object.entries(value).map(([key, item]) => [normalize(key), pidKey(key) && Number.isInteger(item) ? '<PID>' : key === 'candidateVersion' && typeof item === 'string' ? '<CANDIDATE>' : (durationKey(key) || key === 'value' && durationKey(String(value.metric ?? ''))) && typeof item === 'number' && !Number.isInteger(item) ? '<DURATION>' : normalizeValue(item, normalize)]))
  : typeof value === 'string' ? normalize(value) : typeof value === 'number' ? normalizeNumber(value, normalize) : value;
const normalizeNumber = (value, normalize) => { const text = normalize(String(value)); return text === String(value) ? value : text; };
const pidKey = key => /(?:^pid$|Pid$|^pgid$)/.test(key);
const durationKey = key => /(?:Minutes|Seconds|Ms|Duration)$/.test(key);

const uuidPattern = /\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b/gi;
const monthDay = /\b(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec) \d{1,2}, \d{2}:\d{2}\b/g;

function makeNormalizer(context, extraPids, rawTexts) {
  const replacements = [
    [context.checkout, '<PKG>'], [harnessRoot, '<HARNESS>'], [context.root, '<ROOT>'], [casesRoot, '<CASES>'],
    [tmpdir(), '<TMPDIR>'], [realpathSync(tmpdir()), '<TMPDIR>'], [process.execPath, '<NODE>'], [realGit, '<GIT>'],
  ].filter(([from]) => from).sort((a, b) => b[0].length - a[0].length);
  const host = hostname(), user = safeUser();
  const pids = [...extraPids].filter(Boolean).map(String);
  const prefixes = [...new Set(rawTexts.flatMap(text => String(text).match(uuidPattern) ?? []).map(id => id.slice(0, 8).toLowerCase()))].filter(prefix => prefix !== '00000000');
  return text => {
    let out = String(text);
    for (const [from, to] of replacements) out = out.split(from).join(to);
    if (host.length >= 6) out = out.split(host).join('<HOST>');
    if (user.length >= 4) out = out.replace(new RegExp(`\\b${escapeRegExp(user)}\\b`, 'g'), '<USER>');
    out = out.replace(/\b\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?(?:Z|[+-]\d{2}:\d{2})/g, '<TIME>')
      .replace(uuidPattern, '<UUID>')
      .replace(monthDay, '<DATE>')
      .replace(/\b1[7-9]\d{11}\b/g, '<EPOCH_MS>')
      .replace(/\b\d+(?:\.\d+)? ?ms\b/g, '<MS>')
      .replace(/\bgui\/\d+/g, 'gui/<UID>')
      .replace(/\bpdd-[0-9a-f]{12}(?:-[0-9a-f]{6})?\b/g, match => match.length > 16 ? 'pdd-<RUN_HASH>-<AREA_HASH>' : 'pdd-<RUN_HASH>')
      .replace(/\bmemory [\d.]+ GiB free, pressure [a-z]+/g, 'memory <LIVE> GiB free, pressure <LIVE>')
      .replace(/\bdisk [\d.]+ GiB free/g, 'disk <LIVE> GiB free')
      .replace(/\bload [\d.]+/g, 'load <LIVE>')
      .replace(/\bpriority [a-z]+ · new work: [^\n]+/g, 'priority <LIVE> · new work: <LIVE>')
      .replace(/("(?:pid|[a-zA-Z]+Pid)":\s*)\d+/g, '$1"<PID>"');
    for (const prefix of prefixes) out = out.replace(new RegExp(`(?<![0-9a-f])${prefix}(?![0-9a-f])`, 'gi'), '<UUID8>');
    for (const pid of pids) out = out.replace(new RegExp(`\\b${pid}\\b`, 'g'), '<PID>');
    return out;
  };
}
const safeUser = () => { try { return userInfo().username; } catch { return ''; } };
const escapeRegExp = text => text.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

function readCalls(control, normalize) {
  const file = join(control, 'calls.log');
  if (!existsSync(file)) return [];
  return readFileSync(file, 'utf8').split('\x1e').filter(Boolean).map(record => {
    const [tool, cwd, meta, ...argv] = record.split('\x1f');
    const facts = Object.fromEntries(meta.split(';').filter(Boolean).map(pair => pair.split('=')));
    return { tool, cwd: normalize(cwd), argv: argv.map(normalize), ...facts };
  });
}

function gitState(context, normalize) {
  if (!existsSync(join(context.repo, '.git'))) return null;
  const read = (args, cwd = context.repo) => { try { return normalize(execFileSync(realGit, args, { cwd, env: context.env, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }).trim()); } catch { return '(unavailable)'; } };
  const remote = join(context.root, 'remotes/acme/widgets.git');
  return { refs: read(['for-each-ref', '--format=%(refname) %(objectname)']), status: read(['status', '--porcelain', '--untracked-files=all']), worktrees: read(['worktree', 'list', '--porcelain']),
    ...(existsSync(remote) ? { remote: read(['for-each-ref', '--format=%(refname) %(objectname)'], remote) } : {}) };
}

function liveProcesses(root) {
  try {
    return execFileSync('ps', ['-eo', 'pid=,args='], { encoding: 'utf8' }).split('\n')
      .map(line => line.trim()).filter(line => line.includes(root))
      .map(line => Number(line.split(/\s+/)[0])).filter(pid => pid !== process.pid);
  } catch { return []; }
}

function waitForDetached(root) {
  const until = Date.now() + detachedWaitMs, pause = new Int32Array(new SharedArrayBuffer(4));
  while (Date.now() < until) {
    if (!liveProcesses(root).length) return true;
    Atomics.wait(pause, 0, 0, 100);
  }
  for (const pid of liveProcesses(root)) try { process.kill(pid); } catch { }
  return false;
}

function holdCasesRoot() {
  const lock = join(casesRoot, '.capture.pid');
  mkdirSync(casesRoot, { recursive: true });
  const holder = existsSync(lock) ? Number(readFileSync(lock, 'utf8')) : 0;
  if (holder && holder !== process.pid && processAlive(holder)) throw Error(`Another golden capture (pid ${holder}) uses ${casesRoot}. Run one capture at a time.`);
  writeFileSync(lock, String(process.pid));
  process.once('exit', () => rmSync(lock, { force: true }));
}
const processAlive = pid => { try { process.kill(pid, 0); return true; } catch (error) { return error.code === 'EPERM'; } };

function runCase(testCase, checkout) {
  const context = prepare(testCase, checkout);
  const before = listFiles(context.root);
  const started = Date.now();
  const result = spawnSync(process.execPath, [join(checkout, 'bin/pdd.mjs'), ...testCase.argv], {
    cwd: testCase.cwd ? join(context.root, testCase.cwd) : context.repo, env: context.env, input: testCase.stdin ?? '', encoding: 'utf8', timeout: 60000,
  });
  const settled = waitForDetached(context.root);
  const after = listFiles(context.root), callsText = existsSync(join(context.control, 'calls.log')) ? readFileSync(join(context.control, 'calls.log'), 'utf8') : '';
  const rawTexts = [result.stdout, result.stderr, callsText, ...after.keys(), ...[...after.values()].filter(file => file.data && file.data.length < 1 << 20).map(file => file.data.toString('utf8'))];
  const normalize = makeNormalizer(context, [result.pid, process.pid], rawTexts);
  const record = {
    id: testCase.id, argv: testCase.argv, exit: result.error ? `error: ${result.error.code}` : result.status ?? `signal: ${result.signal}`,
    stdout: normalize(result.stdout ?? ''), stderr: normalize(result.stderr ?? ''),
    files: changedFiles(before, after, normalize),
    calls: readCalls(context.control, normalize),
    git: gitState(context, normalize),
    ...(settled ? {} : { detached: 'still running after wait' }),
  };
  return { record, ms: Date.now() - started };
}

function capture(checkout, out, only) {
  const target = resolve(checkout);
  if (!existsSync(join(target, 'bin/pdd.mjs'))) throw Error(`No bin/pdd.mjs in ${target}`);
  if (!only.length && existsSync(out) && readdirSync(out).length) throw Error(`${resolve(out)} is not empty. Capture all cases into a new or empty folder.`);
  mkdirSync(out, { recursive: true });
  holdCasesRoot();
  const selected = only.length ? cases.filter(testCase => only.includes(testCase.id)) : cases;
  const total = Date.now();
  for (const testCase of selected) {
    const { record, ms } = runCase(testCase, target);
    writeFileSync(join(out, `${testCase.id}.json`), JSON.stringify(record, null, 1) + '\n');
    process.stdout.write(`${testCase.id}: exit ${record.exit}, ${record.calls.length} calls, ${record.files.length} files, ${ms} ms\n`);
    if (!process.env.GOLDEN_KEEP) rmSync(join(casesRoot, testCase.id), { recursive: true, force: true });
  }
  process.stdout.write(`Captured ${selected.length} cases from ${target} into ${resolve(out)} in ${((Date.now() - total) / 1000).toFixed(1)} s.\n`);
}

const readRecords = folder => existsSync(folder) ? new Map(readdirSync(folder).filter(name => name.endsWith('.json')).sort()
  .map(name => [name.slice(0, -5), JSON.parse(readFileSync(join(folder, name), 'utf8'))])) : new Map();
const writeCall = call => /^(?:git\s(?:commit|push|branch|tag|worktree add|worktree remove|reset|checkout -b|switch -c|merge|rebase|update-ref)|gh\s(?:pr (?:create|merge|edit|close|comment)|issue (?:edit|close|comment|create)|label)|herdr\s(?:--session \S+ )?\S+ (?:create|open|run|close|prompt|rename|focus)\b)/.test(`${call.tool} ${call.argv.join(' ')}`)
  || (call.tool === 'gh' && /^(?:POST|PATCH|PUT|DELETE)$/i.test(call.argv[call.argv.indexOf('--method') + 1] ?? ''));
const callText = call => `${call.tool} ${call.argv.join(' ')}`.slice(0, 160);
const firstLineDifference = (a, b) => {
  const left = String(a).split('\n'), right = String(b).split('\n');
  const index = left.findIndex((line, at) => line !== right[at]);
  const at = index < 0 ? left.length : index;
  return `line ${at + 1}: ${JSON.stringify((left[at] ?? '(end)').slice(0, 120))} vs ${JSON.stringify((right[at] ?? '(end)').slice(0, 120))}`;
};

function compareCalls(a, b) {
  const notes = [];
  const writesA = a.filter(writeCall).map(callText), writesB = b.filter(writeCall).map(callText);
  const firstWrite = writesA.findIndex((text, index) => text !== writesB[index]);
  if (writesA.length !== writesB.length || firstWrite >= 0) {
    const at = firstWrite < 0 ? Math.min(writesA.length, writesB.length) : firstWrite;
    notes.push(`writes ${writesA.length} vs ${writesB.length}; first difference at write ${at + 1}: ${writesA[at] ?? '(none)'} | ${writesB[at] ?? '(none)'}`);
  }
  const readsA = a.filter(call => !writeCall(call)).map(callText).sort(), readsB = b.filter(call => !writeCall(call)).map(callText).sort();
  if (readsA.join('\n') !== readsB.join('\n')) {
    const onlyA = readsA.filter(text => !readsB.includes(text)), onlyB = readsB.filter(text => !readsA.includes(text));
    notes.push(`reads ${readsA.length} vs ${readsB.length}${onlyA.length ? `; only in A: ${onlyA.slice(0, 3).join(' | ')}` : ''}${onlyB.length ? `; only in B: ${onlyB.slice(0, 3).join(' | ')}` : ''}`);
  }
  if (!notes.length && a.map(callText).join('\n') !== b.map(callText).join('\n')) notes.push('same calls in another order');
  if (!notes.length && JSON.stringify(a) !== JSON.stringify(b)) notes.push('same commands with other folders, stdin or replies');
  return notes.map(note => `calls: ${note}`);
}

function compareFiles(a, b) {
  const byPath = rows => new Map(rows.map(row => [row.path, row]));
  const left = byPath(a), right = byPath(b), notes = [];
  for (const [path, row] of left) {
    const other = right.get(path);
    if (!other) notes.push(`files: only A wrote ${path}`);
    else if (JSON.stringify(row) !== JSON.stringify(other)) notes.push(`files: ${path} differs${row.text !== undefined && other.text !== undefined ? ` (${firstLineDifference(row.text, other.text)})` : row.change !== other.change ? ` (${row.change} vs ${other.change})` : ''}`);
  }
  for (const path of right.keys()) if (!left.has(path)) notes.push(`files: only B wrote ${path}`);
  return notes;
}

function compare(a, b) {
  const notes = [];
  if (a.exit !== b.exit) notes.push(`exit: ${a.exit} vs ${b.exit}`);
  for (const stream of ['stdout', 'stderr']) if (a[stream] !== b[stream]) notes.push(`${stream}: ${firstLineDifference(a[stream], b[stream])}`);
  notes.push(...compareFiles(a.files, b.files), ...compareCalls(a.calls, b.calls));
  for (const key of ['refs', 'status', 'worktrees', 'remote']) if (a.git?.[key] !== b.git?.[key]) notes.push(`git ${key}: ${firstLineDifference(a.git?.[key] ?? '', b.git?.[key] ?? '')}`);
  if (a.detached !== b.detached) notes.push(`detached: ${a.detached ?? 'settled'} vs ${b.detached ?? 'settled'}`);
  return notes;
}

function diff(outA, outB) {
  const left = readRecords(outA), right = readRecords(outB);
  const ids = [...new Set([...left.keys(), ...right.keys()])].sort();
  const lines = [], counts = { identical: 0, differ: 0, onlyA: 0, onlyB: 0 };
  for (const id of ids) {
    if (!right.has(id)) { counts.onlyA++; lines.push(`${id}: only in A`); continue; }
    if (!left.has(id)) { counts.onlyB++; lines.push(`${id}: only in B`); continue; }
    const notes = compare(left.get(id), right.get(id));
    if (!notes.length) { counts.identical++; continue; }
    counts.differ++;
    lines.push(`${id}:`, ...notes.map(note => `  ${note}`));
  }
  process.stdout.write([`Golden diff: A=${resolve(outA)} B=${resolve(outB)}`,
    `${ids.length} cases: ${counts.identical} identical, ${counts.differ} differ, ${counts.onlyA} only in A, ${counts.onlyB} only in B.`, ...lines, ''].join('\n'));
}

const usage = [
  'Usage: node test/golden/run.mjs capture <checkoutDir> <outDir> [caseId...]',
  '       node test/golden/run.mjs diff <outA> <outB>',
  'capture runs every case (or the named ones) against <checkoutDir>/bin/pdd.mjs and writes one record per case into a new or empty <outDir>.',
  'diff compares two capture folders and always exits 0. Set GOLDEN_KEEP=1 to keep the case folders for a look.', ''].join('\n');
const [command, first, second, ...rest] = process.argv.slice(2);
if (command === 'capture' && first && second) capture(first, second, rest);
else if (command === 'diff' && first && second) diff(first, second);
else { process.stderr.write(usage); process.exitCode = 2; }

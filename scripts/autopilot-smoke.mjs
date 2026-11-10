// Source contract: prompts/scripts/autopilot-smoke.prompt.md.
import * as nativeFs from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { tmpdir } from 'node:os';
import { randomUUID } from 'node:crypto';
import { spawnSync } from 'node:child_process';

const fixtureRoot = fileURLToPath(new URL('../fixtures/autopilot-smoke/', import.meta.url));
const label = 'pdd:autopilot';
const ownerPattern = /^[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,37}[a-zA-Z0-9])?$/;
const issueIdPattern = /^\d{2}-[a-z0-9]+(?:-[a-z0-9]+)*$/;
const marker = id => `<!-- pdd:autopilot-smoke:${id} -->`;
const usage = 'Usage: scripts/autopilot-smoke.sh --owner OWNER [--apply]\n' +
  '       scripts/autopilot-smoke.sh --check OWNER/REPO\n' +
  'Default: dry run. --apply creates a fresh private repo. Never deletes repos.';

function nativeRun(program, args, options = {}) {
  const env = Object.fromEntries(Object.entries(process.env).filter(([key]) => !key.startsWith('GIT_')));
  const result = spawnSync(program, args, {encoding: 'utf8', timeout: 120_000,
    maxBuffer: 32 * 1024 * 1024, ...options, env});
  return {code: result.status ?? 1, stdout: result.stdout ?? '', stderr: result.stderr ?? ''};
}
function bind(ports) {
  return {fs: nativeFs, run: nativeRun, now: Date.now,
    id: () => randomUUID().replaceAll('-', ''), log: line => process.stdout.write(`${line}\n`), ...ports};
}
function validRepo(repo) {
  const parts = typeof repo === 'string' ? repo.split('/') : [];
  return parts.length === 2 && ownerPattern.test(parts[0]) && /^[a-zA-Z0-9._-]{1,100}$/.test(parts[1]) &&
    !['.', '..'].includes(parts[1]);
}
function command(p, program, args, options = {}) {
  const result = p.run(program, args, options);
  if (result?.code !== 0) throw Error(`${program} ${args[0]} failed; check authentication, permissions and connectivity. Remote effects may remain.`);
  return result.stdout;
}
function jsonCommand(p, args) {
  const text = command(p, 'gh', args);
  try { return JSON.parse(text); } catch { throw Error('gh returned invalid JSON.'); }
}
function pages(p, path) {
  const rows = jsonCommand(p, ['api', '--method', 'GET', path, '--paginate', '--slurp']);
  if (!Array.isArray(rows) || !rows.every(Array.isArray)) throw Error('gh returned malformed paginated rows.');
  return rows.flat();
}
function time(value) {
  if (typeof value !== 'string' || !Number.isFinite(Date.parse(value))) throw Error('Invalid GitHub timestamp.');
  return new Date(value).toISOString();
}

export function loadSmokeFixture({root = fixtureRoot} = {}, ports = {}) {
  const {fs} = bind(ports), baseDir = resolve(root, 'base'), files = [];
  function walk(directory, prefix = '') {
    if (!fs.lstatSync(directory).isDirectory()) throw Error('Fixture directories must be regular directories, not symlinks.');
    for (const name of fs.readdirSync(directory).sort()) {
      const path = prefix ? `${prefix}/${name}` : name;
      const full = join(directory, name), stat = fs.lstatSync(full);
      if (stat.isDirectory()) walk(full, path);
      else if (stat.isFile()) files.push({path, content: fs.readFileSync(full, 'utf8')});
      else throw Error('Fixture base accepts only regular files and directories, no symlinks.');
    }
  }
  walk(baseDir);
  let pkg;
  try { pkg = JSON.parse(files.find(file => file.path === 'package.json')?.content); }
  catch { throw Error('Fixture base needs a package.json with a native test command.'); }
  if (!files.length || typeof pkg?.scripts?.test !== 'string' || !pkg.scripts.test.trim()) {
    throw Error('Fixture base needs a native test command.');
  }
  const issueDir = resolve(root, 'issues');
  if (!fs.lstatSync(issueDir).isDirectory()) throw Error('Fixture issue directory must not be a symlink.');
  const names = fs.readdirSync(issueDir).filter(name => name.endsWith('.md')).sort();
  if (names.length < 3 || names.length > 5) throw Error('Smoke fixture needs 3 to 5 issues.');
  const issues = names.map(name => {
    const id = name.slice(0, -3), path = join(issueDir, name);
    if (!issueIdPattern.test(id)) throw Error('Invalid issue fixture filename.');
    if (!fs.lstatSync(path).isFile()) throw Error('Issue fixtures must be regular files, not symlinks.');
    const text = fs.readFileSync(path, 'utf8');
    const match = /^# ([^\r\n]+)\r?\n([\s\S]*)$/.exec(text);
    if (!match?.[1].trim() || !match[2].trim()) throw Error(`Issue fixture ${name} needs a title and body.`);
    if (text.includes('pdd:autopilot-smoke:')) throw Error('Issue fixture contains a reserved identity marker.');
    return {id, title: match[1].trim(), body: `${match[2].trim()}\n\n${marker(id)}`};
  });
  return {baseDir, files, issues};
}

// Optional read-only hook for callers; intentionally independent of core/state.
export function readSmokeResults({repo, fixture} = {}, ports = {}) {
  if (!validRepo(repo)) throw Error('Expected a GitHub OWNER/REPO.');
  const p = bind(ports);
  fixture ??= loadSmokeFixture({}, p);
  const checkedAt = new Date(p.now()).toISOString();
  const inventory = pages(p, `repos/${repo}/issues?state=all&per_page=100`);
  const selected = fixture.issues.map(seed => {
    const matches = inventory.filter(row => !row?.pull_request && typeof row?.body === 'string' && row.body.includes(marker(seed.id)));
    if (matches.length !== 1) throw Error(`Expected exactly one smoke issue for ${seed.id}; found ${matches.length} (missing or duplicate).`);
    const issue = matches[0];
    if (!Number.isSafeInteger(issue.number) || issue.number < 1 || typeof issue.title !== 'string' ||
      typeof issue.html_url !== 'string' || issue.html_url.toLowerCase() !== `https://github.com/${repo}/issues/${issue.number}`.toLowerCase() ||
      !['open', 'closed'].includes(issue.state)) {
      throw Error('Malformed GitHub issue row.');
    }
    return {seed, issue};
  });
  const prs = jsonCommand(p, ['pr', 'list', '--repo', repo, '--state', 'merged', '--limit', '1000',
    '--json', 'number,url,mergedAt,closingIssuesReferences']);
  if (!Array.isArray(prs)) throw Error('Malformed merged PR inventory.');
  if (prs.length >= 1000) throw Error('Merged PR inventory saturated the 1000-row limit; results may be truncated.');
  for (const pr of prs) {
    if (!Number.isSafeInteger(pr?.number) || !Array.isArray(pr.closingIssuesReferences)) throw Error('Malformed merged PR row.');
    time(pr.mergedAt);
  }
  const issues = selected.map(({seed, issue}) => {
    const createdAt = time(issue.created_at);
    const comments = pages(p, `repos/${repo}/issues/${issue.number}/comments?per_page=100`);
    const endPattern = new RegExp(`<!-- pdd:autopilot-core:end:${issue.number}:[^\\s<>]+ -->`);
    const ended = comments.flatMap(comment => {
      if (typeof comment?.body !== 'string') throw Error('Malformed GitHub comment row.');
      return endPattern.test(comment.body) ? [time(comment.created_at)] : [];
    }).sort();
    const merged = prs.filter(pr => pr.closingIssuesReferences.some(ref =>
      typeof ref?.url === 'string' && ref.url.toLowerCase() === issue.html_url.toLowerCase()))
      .map(pr => time(pr.mergedAt)).sort();
    let state = 'open', finishedAt = null;
    if (issue.state === 'closed' && merged.length) { state = 'merged'; finishedAt = merged.at(-1); }
    else if (ended.length || issue.state === 'closed') {
      state = 'ended'; finishedAt = ended.at(-1) ?? time(issue.closed_at);
    }
    return {id: seed.id, number: issue.number, title: issue.title, url: issue.html_url, state, createdAt, finishedAt,
      elapsedSeconds: Math.max(0, Math.floor((Date.parse(finishedAt ?? checkedAt) - Date.parse(createdAt)) / 1000))};
  });
  return {repo, checkedAt, issues};
}

function parse(argv) {
  if (argv.length === 1 && argv[0] === '--help') return {help: true};
  const values = {};
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (!['--owner', '--check', '--apply'].includes(arg) || Object.hasOwn(values, arg)) throw Error(usage);
    if (arg === '--apply') values[arg] = true;
    else {
      const value = argv[++i];
      if (!value || value.startsWith('--')) throw Error(usage);
      values[arg] = value;
    }
  }
  if (values['--check']) {
    if (Object.keys(values).length !== 1 || !validRepo(values['--check'])) throw Error(usage);
    return {repo: values['--check']};
  }
  if (!ownerPattern.test(values['--owner'] ?? '')) throw Error(usage);
  return {owner: values['--owner'], apply: Boolean(values['--apply'])};
}
function cleanupLine(repo) { return `Delete manually: gh repo delete ${repo} --yes`; }

export function runSmoke(argv, ports = {}) {
  const p = bind(ports);
  try {
    const options = parse(argv);
    if (options.help) return {exitCode: 0, message: usage};
    const fixture = p.fixture ?? loadSmokeFixture({}, p);
    if (options.repo) {
      const result = readSmokeResults({repo: options.repo, fixture}, p);
      p.log(`Repo: ${result.repo}; checked=${result.checkedAt}`);
      for (const issue of result.issues) {
        p.log(`#${issue.number} ${issue.state} ${issue.title}; created=${issue.createdAt} finished=${issue.finishedAt ?? '-'} elapsed=${issue.elapsedSeconds}s ${issue.url}`);
      }
      p.log(cleanupLine(result.repo));
      return {exitCode: 0, message: ''};
    }
    const stamp = new Date(p.now()).toISOString().replaceAll(/[-:]/g, '').replace(/\.\d{3}Z$/, 'Z');
    const id = p.id();
    if (!/^[a-f0-9]+$/.test(id)) throw Error('Invalid fresh repository id.');
    const repo = `${options.owner}/autopilot-smoke-${stamp}-${id}`;
    p.log(`${options.apply ? 'Apply' : 'Dry run'}: ${repo} (private)`);
    p.log(cleanupLine(repo));
    p.log(`Check: scripts/autopilot-smoke.sh --check ${repo}`);
    fixture.issues.forEach((issue, index) => p.log(`${index + 1}. ${issue.title} [${label}]`));
    if (!options.apply) return {exitCode: 0, message: ''};
    const staging = p.fs.mkdtempSync(join(tmpdir(), 'pdd-autopilot-smoke-'));
    try {
      for (const file of fixture.files) {
        const destination = join(staging, file.path);
        p.fs.mkdirSync(dirname(destination), {recursive: true});
        p.fs.writeFileSync(destination, file.content, 'utf8');
      }
      const git = args => command(p, 'git', args, {cwd: staging});
      git(['-c', 'init.templateDir=', 'init', '--initial-branch=main']);
      git(['config', 'core.hooksPath', '/dev/null']);
      git(['add', '--', '.']);
      git(['-c', 'core.hooksPath=/dev/null', '-c', 'commit.gpgSign=false',
        '-c', 'user.name=Smoke sandbox', '-c', 'user.email=smoke@example.invalid', 'commit', '-m', 'Seed smoke helpers']);
      command(p, 'gh', ['repo', 'create', repo, '--private', '--source', staging, '--push']);
      command(p, 'gh', ['label', 'create', label, '--repo', repo, '--color', '5319e7', '--force']);
      for (const issue of fixture.issues) {
        const url = command(p, 'gh', ['issue', 'create', '--repo', repo, '--title', issue.title,
          '--label', label, '--body-file', '-'], {input: `${issue.body}\n`}).trim();
        if (!/^https:\/\/github\.com\/[a-zA-Z0-9._/-]+\/issues\/\d+$/.test(url)) {
          throw Error('gh issue create returned no valid issue URL; remote effects may remain.');
        }
        p.log(`${url} ${issue.title}`);
      }
    } finally { p.fs.rmSync(staging, {recursive: true, force: true}); }
    return {exitCode: 0, message: ''};
  } catch (error) { return {exitCode: 1, message: error.message}; }
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const result = runSmoke(process.argv.slice(2));
  if (result.message) (result.exitCode ? process.stderr : process.stdout).write(`${result.message}\n`);
  process.exitCode = result.exitCode;
}

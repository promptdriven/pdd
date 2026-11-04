// Generated from prompts/cli/autopilot-launcher.prompt.md (sha256: 12bd60a88c4862d038670ee6cbb7dd1c36ddd3ce602c605fcf70d7d275e3fc91).
import { spawn } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { existsSync, mkdirSync, readFileSync, writeFileSync, renameSync, unlinkSync, openSync, closeSync } from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { runAgentProcess, parseAgentAuthStatus } from './agent-adapters.mjs';
import { loadAgentDefinitions } from './agent-config.mjs';
import { pathDiagnostic } from './path-diagnostic.mjs';
import { runAutopilot } from './autopilot.mjs';
import { checkWorkflowAgents } from './workflow-agents.mjs';

const INTERVAL = 30 * 60 * 1000;
const SESSION = 'pdd-autopilot';
const ACK = '<!-- pdd:autopilot:thanks -->';
const ACK_TEXT = `thanks, a maintainer will look\n\n${ACK}`;
const self = fileURLToPath(import.meta.url);
const quote = value => `'${String(value).replaceAll("'", "'\\''")}'`;
const line = value => String(value).split(/[\r\n]/)[0].replace(/[\x00-\x1f\x7f]/g, ' ');
const read = (file, fallback = null) => { try { return JSON.parse(readFileSync(file, 'utf8')); } catch (e) { if (e.code === 'ENOENT') return fallback; throw e; } };
function save(file, value) {
  mkdirSync(dirname(file), { recursive: true, mode: 0o700 });
  const temp = `${file}.${randomUUID()}.tmp`;
  try { writeFileSync(temp, JSON.stringify(value), { mode: 0o600 }); renameSync(temp, file); }
  finally { try { unlinkSync(temp); } catch (e) { if (e.code !== 'ENOENT') throw e; } }
}
async function settings(state, p) {
  const result = await runAutopilot({ action: 'setup', interactive: false, inRepo: true }, {
    cwd: state.cwd,
    execFile: async (command, args) => ({ stdout: await p.checked(command, args) }),
  });
  if (result.exitCode !== 0) throw Error(result.message);
  return result;
}
const ok = message => ({ exitCode: 0, message });
const bad = message => ({ exitCode: 1, message: line(message) });
function portsFor(state, ports) {
  const env = { ...process.env, ...state?.environment, ...ports.env };
  const run = ports.run ?? runAgentProcess;
  const execute = async (command, args, options = {}) => run(command, args, { cwd: state.cwd, env, timeoutMs: 10000, maxBytes: 8 * 1024 * 1024, ...options });
  const checked = async (command, args) => { const result = await execute(command, args); if (result.code !== 0) throw Error(`${command} failed; check its sign-in and retry.`); return result.stdout; };
  return { ...ports, env, run, execute, checked, now: ports.now ?? Date.now };
}
const keepEnv = env => Object.fromEntries(['HOME', 'PATH', 'CODEX_HOME', 'CLAUDE_CONFIG_DIR', 'GEMINI_CLI_HOME', 'XDG_CONFIG_HOME', 'XDG_RUNTIME_DIR', 'DBUS_SESSION_BUS_ADDRESS'].filter(k => typeof env[k] === 'string').map(k => [k, env[k]]));
async function selectAgent(state, p) {
  let definitions = loadAgentDefinitions({ cwd: state.cwd, env: p.env });
  definitions.push({ id: 'agy', kind: 'agy', command: 'agy', env: {} });
  const current = p.env.CODEX_THREAD_ID ? 'codex' : p.env.CLAUDECODE ? 'claude' : null;
  const rank = def => def.kind === current ? -1 : ['codex', 'claude', 'agy', 'gemini'].indexOf(def.kind);
  definitions = definitions.map((def, index) => ({ def, index })).sort((a, b) => rank(a.def) - rank(b.def) || a.index - b.index).map(x => x.def);
  for (const def of definitions) {
    const agentEnv = { ...p.env, ...def.env };
    try {
      if (def.kind === 'gemini') {
        const help = await p.execute(def.command, ['--version'], { env: agentEnv });
        const credentials = read(join(agentEnv.GEMINI_CLI_HOME || agentEnv.HOME || homedir(), '.gemini', 'oauth_creds.json'), {});
        if (help.code === 0 && typeof credentials.refresh_token === 'string' && credentials.refresh_token) return def;
      } else if (def.kind === 'agy') {
        const result = await checkWorkflowAgents({ cwd: state.cwd, env: agentEnv, requested: 'agy' }, {
          run: (_command, args, options) => p.execute(def.command, args, options),
        });
        if (result.ok) return def;
      } else {
        const result = await p.execute(def.command, def.kind === 'codex' ? ['login', 'status'] : ['auth', 'status', '--json'], { env: agentEnv });
        if (parseAgentAuthStatus({ agent: def.kind, result }) === 'ready') return def;
      }
    } catch { /* Try another installed sign-in; never make a model call to test it. */ }
  }
  return null;
}
function xml(value) { return String(value).replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;').replaceAll('"', '&quot;').replaceAll("'", '&apos;'); }
// Timers execute this file directly. Neither platform needs a shell or a daemon owned by pdd.
async function userTimer(action, state, p) {
  const platform = p.platform ?? process.platform;
  const name = `pdd-autopilot-${state.id}`;
  const home = p.env.HOME || homedir();
  if (platform === 'darwin') {
    const folder = join(home, 'Library', 'LaunchAgents'), file = join(folder, `${name}.plist`);
    const domain = `gui/${p.uid ?? process.getuid()}`;
    if (action === 'status') return (await p.execute('launchctl', ['print', `${domain}/${name}`])).code === 0;
    if (action === 'stop') { if ((await p.execute('launchctl', ['print', `${domain}/${name}`])).code === 0) await p.checked('launchctl', ['bootout', `${domain}/${name}`]); try { unlinkSync(file); } catch (e) { if (e.code !== 'ENOENT') throw e; } return false; }
    mkdirSync(folder, { recursive: true });
    const args = [process.execPath, self, state.stateFile].map(x => `<string>${xml(x)}</string>`).join('');
    const vars = Object.entries(state.environment).map(([k, v]) => `<key>${xml(k)}</key><string>${xml(v)}</string>`).join('');
    writeFileSync(file, `<?xml version="1.0" encoding="UTF-8"?><!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd"><plist version="1.0"><dict><key>Label</key><string>${name}</string><key>ProgramArguments</key><array>${args}</array><key>EnvironmentVariables</key><dict>${vars}</dict><key>StartInterval</key><integer>1800</integer><key>StandardErrorPath</key><string>${xml(state.stateFile + '.log')}</string></dict></plist>`, { mode: 0o600 });
    await p.execute('launchctl', ['bootout', `${domain}/${name}`]);
    await p.checked('launchctl', ['bootstrap', domain, file]);
    return true;
  }
  if (platform !== 'linux') throw Error('Autopilot user timers need macOS or Linux.');
  const folder = join(p.env.XDG_CONFIG_HOME || join(home, '.config'), 'systemd', 'user');
  if (action === 'status') return (await p.execute('systemctl', ['--user', 'is-active', `${name}.timer`])).code === 0;
  if (action === 'stop') {
    if ((await p.execute('systemctl', ['--user', 'is-active', `${name}.timer`])).code === 0) await p.checked('systemctl', ['--user', 'stop', `${name}.timer`]);
    if (existsSync(join(folder, `${name}.timer`))) await p.checked('systemctl', ['--user', 'disable', `${name}.timer`]);
    for (const suffix of ['timer', 'service']) { try { unlinkSync(join(folder, `${name}.${suffix}`)); } catch (e) { if (e.code !== 'ENOENT') throw e; } }
    await p.checked('systemctl', ['--user', 'daemon-reload']); return false;
  }
  mkdirSync(folder, { recursive: true });
  const unit = value => JSON.stringify(String(value).replaceAll('%', '%%'));
  writeFileSync(join(folder, `${name}.service`), `[Unit]\nDescription=PDD Autopilot tick\n[Service]\nType=oneshot\nExecStart=${[process.execPath, self, state.stateFile].map(unit).join(' ')}\n${Object.entries(state.environment).map(([k, v]) => `Environment=${unit(k + '=' + v)}\n`).join('')}`, { mode: 0o600 });
  writeFileSync(join(folder, `${name}.timer`), `[Unit]\nDescription=PDD Autopilot every 30 minutes\n[Timer]\nOnActiveSec=30min\nOnUnitActiveSec=30min\nAccuracySec=1s\n[Install]\nWantedBy=timers.target\n`, { mode: 0o600 });
  await p.checked('systemctl', ['--user', 'daemon-reload']);
  await p.checked('systemctl', ['--user', 'enable', `${name}.timer`]);
  await p.checked('systemctl', ['--user', 'restart', `${name}.timer`]);
  return true;
}
async function timer(action, state, p) { return p.timer ? p.timer(action, state) : userTimer(action, state, p); }
async function herdr(args, p) {
  if (p.herdr) return p.herdr(args);
  const result = await p.execute('herdr', ['--session', SESSION, ...args]);
  let reply; try { reply = JSON.parse(result.code === 0 ? result.stdout : result.stderr || result.stdout); } catch { reply = {}; }
  if (result.code !== 0 || reply.error) throw Object.assign(Error(reply.error?.message || 'Herdr could not deliver; run herdr --help.'), { code: reply.error?.code });
  return reply;
}
async function openWorkspace(state, p) {
  if (!p.herdr) {
    const status = await herdr(['status', 'server', '--json'], p);
    if (!status.running) {
      const childEnv = Object.fromEntries(Object.entries(p.env).filter(([k]) => !/^(?:HERDR_|CLAUDECODE$|CLAUDE_CODE_|CODEX_THREAD_ID$|PDD_AGENT_SESSION$)/.test(k)));
      const child = spawn('herdr', ['--session', SESSION, 'server'], { env: childEnv, cwd: state.cwd, detached: true, stdio: 'ignore' });
      await new Promise((resolve, reject) => { child.once('error', reject); child.once('spawn', resolve); }); child.unref();
      for (let i = 0; i < 50; i++) {
        try { if ((await herdr(['status', 'server', '--json'], p)).running) break; } catch { /* startup */ }
        await new Promise(resolve => setTimeout(resolve, 100));
      }
    }
  }
  if (!state.paneId) {
    const reply = await herdr(['workspace', 'create', '--cwd', state.cwd, '--label', `${state.repo} Autopilot`, '--no-focus'], p);
    state.paneId = reply.result?.root_pane?.pane_id;
    state.workspaceId = reply.result?.workspace?.workspace_id;
    if (!state.paneId) throw Error('Herdr returned no pane; run herdr --help.');
  }
}
function response(text) {
  const boundary = text.search(/\r?\n\r?\n/);
  if (boundary < 0) throw Error('GitHub returned no HTTP headers.');
  const headers = text.slice(0, boundary), body = text.slice(boundary).trim();
  const header = name => headers.match(new RegExp(`^${name}:\\s*(.+)$`, 'im'))?.[1]?.trim();
  return { status: Number(headers.match(/^HTTP\/\S+\s+(\d+)/)?.[1]), etag: header('etag'), link: header('link'), resetAt: Number(header('x-ratelimit-reset')) * 1000, body };
}
async function queryIssues(state, p) {
  let endpoint = `repos/${state.repo}/issues?state=open&sort=updated&direction=desc&per_page=100`;
  const issues = [], pages = {}; let first = true, etag;
  while (endpoint) {
    const old = state.pages?.[endpoint];
    const args = ['api', '--include', '--method', 'GET', endpoint];
    if (old?.etag) args.push('-H', `If-None-Match: ${old.etag}`);
    const r = response((await p.execute('gh', args)).stdout);
    if ([403, 429].includes(r.status) && r.resetAt) return { status: r.status, resetAt: r.resetAt };
    let page;
    if (r.status === 304 && old) page = old;
    else {
      if (r.status !== 200) throw Error('GitHub issue check failed; check gh auth status.');
      const rows = JSON.parse(r.body); if (!Array.isArray(rows)) throw Error('GitHub returned no issue list.');
      page = { etag: r.etag, rows, next: r.link?.match(/<https:\/\/api\.github\.com\/([^>]+)>; rel="next"/)?.[1] };
    }
    if (first) { etag = page.etag; first = false; }
    pages[endpoint] = page; issues.push(...page.rows); endpoint = page.next;
  }
  return { status: 200, etag, issues, pages };
}
async function githubGet(endpoint, p) {
  const result = await p.execute('gh', ['api', '--include', '--method', 'GET', endpoint]);
  const r = response(result.stdout);
  if ([403, 429].includes(r.status) && r.resetAt) throw Object.assign(Error('GitHub rate limited; waiting until reset.'), { resetAt: r.resetAt });
  if (r.status === 404) return { ...r, value: null };
  if (r.status !== 200) throw Error('GitHub lookup unavailable; eligible work will be retried next tick.');
  return { ...r, value: JSON.parse(r.body) };
}
async function comments(number, state, p) {
  if (p.comments) return p.comments(number);
  let endpoint = `repos/${state.repo}/issues/${number}/comments?per_page=100`; const rows = [];
  while (endpoint) {
    const r = await githubGet(endpoint, p);
    if (!Array.isArray(r.value)) throw Error('GitHub comments unavailable; retry next tick.');
    rows.push(...r.value); endpoint = r.link?.match(/<https:\/\/api\.github\.com\/([^>]+)>; rel="next"/)?.[1];
  }
  return rows;
}
async function trusted(row, state, config, p) {
  const login = row.user?.login;
  if (!login) return false;
  if ([state.repo.split('/')[0], ...config.trust].some(name => name.toLowerCase() === login.toLowerCase())) return true;
  p.permissions ??= new Map();
  if (!p.permissions.has(login)) {
    const result = await githubGet(`repos/${state.repo}/collaborators/${encodeURIComponent(login)}/permission`, p);
    p.permissions.set(login, ['admin', 'maintain', 'write'].includes(result.value?.permission));
  }
  return p.permissions.get(login);
}
function message(state, issues) {
  const skill = state.agent.kind === 'codex' ? '$pdd-autopilot' : '/pdd-autopilot';
  const skillPath = join(state.packageRoot ?? dirname(dirname(self)), 'skills', 'pdd-autopilot', 'SKILL.md');
  return `${skill}\nLoad and follow the bundled skill at ${JSON.stringify(skillPath)}. Run its start-up recipe first when recipeFirst is true, then follow its room, pdd:working claim and stuck-run rules. Inspect claimed issues for progress and stale claims; do not treat them as unclaimed work. The packet contains only trusted text; further issue/comment reads must preserve that boundary. Use the skill's pdd-check and pdd-merge handoffs for review and merge work.\n${JSON.stringify({ repository: state.repo, activatedAt: state.activatedAt, recipeFirst: !state.recipeDelivered, ...(state.runs === undefined ? {} : { runs: state.runs }), issues })}\n`;
}
async function wake(state, text, p) {
  await openWorkspace(state, p);
  let running = false;
  try { running = Boolean((await herdr(['agent', 'get', state.paneId], p)).result?.agent); }
  catch (e) {
    if (!['agent_not_found', 'pane_not_found', 'server_not_running'].includes(e.code)) throw e;
    if (e.code !== 'agent_not_found') { delete state.paneId; delete state.workspaceId; await openWorkspace(state, p); }
  }
  if (running) { await herdr(['agent', 'prompt', state.paneId, text], p); return; }
  const file = state.stateFile.replace(/\.json$/, '.message.md');
  writeFileSync(file, text, { mode: 0o600 });
  let definition;
  try { definition = loadAgentDefinitions({ cwd: state.cwd, env: p.env }).find(x => x.id === state.agent.id); } catch { /* Report at launch if the selected command no longer works. */ }
  definition ??= state.agent;
  const input = `"$(cat ${quote(file)})"`;
  const args = definition.kind === 'codex' ? ['--no-daemon', '--dangerously-bypass-approvals-and-sandbox', input]
    : definition.kind === 'claude' ? ['--dangerously-skip-permissions', input]
    : ['--dangerously-skip-permissions', '--prompt-interactive', input];
  if (definition.kind === 'gemini') args.splice(0, 1, '--yolo');
  const env = Object.entries({ ...keepEnv(p.env), ...definition.env }).map(([k, v]) => `${k}=${quote(v)}`);
  await herdr(['pane', 'run', state.paneId, ['env', ...env, quote(definition.command), ...args].join(' ')], p);
}

export async function tickAutopilot(stateFile, ports = {}) {
  let state = read(stateFile); if (!state?.enabled) return ok('Autopilot stopped.');
  const p = portsFor(state, ports), config = await settings(state, p);
  if (config.mode === 'off') return ok(line(config.message));
  if (state.retryAt > p.now()) return ok(`GitHub rate limited; next attempt after ${new Date(state.retryAt).toISOString()}.`);
  const lock = stateFile + '.lock'; let fd;
  try { fd = openSync(lock, 'wx', 0o600); writeFileSync(fd, String(process.pid)); }
  catch (e) {
    if (e.code !== 'EEXIST') throw e;
    const pid = Number(readFileSync(lock, 'utf8'));
    try { process.kill(pid, 0); return ok('Autopilot tick already running.'); }
    catch (error) { if (error.code !== 'ESRCH') return ok('Autopilot tick already running.'); }
    unlinkSync(lock); return tickAutopilot(stateFile, ports);
  }
  try {
    const result = p.queryIssues ? await p.queryIssues(state) : await queryIssues(state, p);
    if ([403, 429].includes(result.status)) { state.retryAt = result.resetAt || p.now() + INTERVAL; return ok('GitHub rate limited; waiting until reset.'); }
    delete state.retryAt;
    if (result.status !== 304) { state.cachedIssues = result.issues; state.etag = result.etag; if (result.pages) state.pages = result.pages; }
    state.acknowledged ??= {}; state.commentCache ??= {};
    const work = [];
    for (const issue of state.cachedIssues ?? []) {
      const labels = issue.labels?.map(x => typeof x === 'string' ? x : x.name) ?? [];
      if (issue.pull_request || issue.state !== 'open' || (Date.parse(issue.created_at) < Date.parse(state.activatedAt) && !labels.includes('pdd:autopilot'))) continue;
      const version = `${issue.updated_at}:${issue.comments}`;
      let rows = [];
      if (issue.comments) {
        const cached = state.commentCache[issue.number];
        rows = cached?.version === version ? cached.rows : await comments(issue.number, state, p);
        state.commentCache[issue.number] = { version, rows };
      }
      const trustedComments = []; let acknowledged = false;
      for (const row of rows) {
        if (await trusted(row, state, config, p)) {
          if (row.body === ACK_TEXT) acknowledged = true;
          else trustedComments.push(row);
        }
      }
      const authorTrusted = await trusted(issue, state, config, p);
      if (!authorTrusted && !trustedComments.length) {
        if (!state.acknowledged[issue.number] && !acknowledged) {
          const reply = await p.execute('gh', ['api', '--include', '--method', 'POST', `repos/${state.repo}/issues/${issue.number}/comments`, '-f', `body=${ACK_TEXT}`]);
          if (reply.code !== 0) {
            const failure = response(reply.stdout);
            if ([403, 429].includes(failure.status) && failure.resetAt) throw Object.assign(Error('GitHub rate limited; waiting until reset.'), { resetAt: failure.resetAt });
            throw Error('GitHub reply could not be sent; retry next tick.');
          }
        }
        state.acknowledged[issue.number] = true;
        continue;
      }
      work.push({ number: issue.number, url: issue.html_url, ...(labels.includes('pdd:working') ? { claimed: true } : {}), ...(authorTrusted ? { title: issue.title, body: issue.body } : {}), comments: trustedComments.map(row => ({ author: row.user.login, body: row.body })) });
    }
    // stop may have been requested while GitHub was in flight.
    if (!read(stateFile)?.enabled) return ok('Autopilot stopped.');
    if (work.length || !state.recipeDelivered) {
      await wake(state, message(state, work), p);
      state.recipeDelivered = true;
    }
    return ok(work.length ? `Autopilot offered ${work.length} issue(s).` : 'Autopilot tick complete.');
  } catch (e) {
    if (e.resetAt) { state.retryAt = e.resetAt; return ok('GitHub rate limited; waiting until reset.'); }
    throw e;
  } finally {
    const latest = read(stateFile);
    state.enabled = latest?.enabled === true; state.timerInstalled = latest?.timerInstalled;
    state.nextTick = state.enabled ? p.now() + INTERVAL : null;
    save(stateFile, state); closeSync(fd); unlinkSync(lock);
  }
}

export async function runAutopilotLauncher(input, ports = {}) {
  const { command, packageRoot, runs, issues = [] } = input;
  let state = { cwd: input.cwd, environment: keepEnv(input.env ?? process.env) };
  let p = portsFor(state, { ...ports, env: input.env });
  try {
    state.cwd = (await p.checked('git', ['rev-parse', '--show-toplevel'])).trim();
    const id = createHash('sha256').update(state.cwd).digest('hex').slice(0, 20);
    const folder = ports.stateRoot ?? join(p.env.HOME || homedir(), '.local', 'state', 'pdd', 'autopilot');
    const stateFile = join(folder, `${id}.json`), previous = read(stateFile);
    state = { ...state, ...previous, cwd: state.cwd, id, stateFile };
    p = portsFor(state, { ...ports, env: input.env });
    if (command === 'status') {
      const active = Boolean(state.enabled && await timer('status', state, p));
      return ok(`Autopilot ${active ? 'running' : 'stopped'}: ${state.repo ?? state.cwd} · ${state.agent?.id ?? 'no agent'} · next tick: ${active && state.nextTick ? new Date(state.nextTick).toISOString() : 'none'}`);
    }
    if (command === 'stop') {
      if (previous) { state.enabled = false; state.nextTick = null; save(stateFile, state); if (state.timerInstalled !== false) { await timer('stop', state, p); state.timerInstalled = false; save(stateFile, state); } }
      return ok('Autopilot stopped on this machine; the current step can finish.');
    }
    if (command === 'start' && runs !== undefined && (!/^[1-9][0-9]*$/.test(runs) || !Number.isSafeInteger(Number(runs)))) return { exitCode: 2, message: 'Use --runs with a positive integer, or omit it for no fixed cap.' };
    if (command === 'start') {
      const config = await settings(state, p);
      if (config.mode === 'off') return ok(`${line(config.message)} Choose observe or auto with pdd autopilot observe or pdd autopilot auto.`);
      state.packageRoot = packageRoot;
    }
    if (!state.repo) state.repo = JSON.parse(await p.checked('gh', ['repo', 'view', '--json', 'nameWithOwner'])).nameWithOwner;
    if (command === 'add') {
      const label = await p.execute('gh', ['api', '--method', 'POST', `repos/${state.repo}/labels`, '-f', 'name=pdd:autopilot', '-f', 'color=5319e7', '-f', 'description=Autopilot may take this old issue']);
      if (label.code !== 0 && !/already_exists/.test(label.stdout + label.stderr)) throw Error('Could not create pdd:autopilot; check gh auth status.');
      for (const ref of issues) {
        const number = String(ref).match(/(?:^|#|\/)([1-9][0-9]*)\/?$/)?.[1];
        if (!number) return { exitCode: 2, message: 'Name an issue number for pdd autopilot add.' };
        await p.checked('gh', ['api', '--method', 'POST', `repos/${state.repo}/issues/${number}/labels`, '-f', 'labels[]=pdd:autopilot']);
      }
      return ok(`Marked ${issues.length} issue(s) with pdd:autopilot.`);
    }
    if (command !== 'start') return { exitCode: 2, message: 'Use pdd autopilot start, stop, status or add.' };
    if ((await p.execute('gh', ['auth', 'status'])).code !== 0) return bad('GitHub is not signed in; run gh auth login.');
    try { if ((await p.execute('herdr', ['--version'])).code !== 0) throw Error(); }
    catch { return bad('Herdr is missing or unavailable; install Herdr, then run herdr --help.'); }
    const agent = ports.selectAgent ? await ports.selectAgent(state, p) : await selectAgent(state, p);
    if (!agent) return bad('Sign in to Codex, Claude Code, agy or Gemini at your terminal, then run pdd autopilot start.');
    const version = read(join(packageRoot, 'package.json')).version;
    const warnings = (ports.pathDiagnostic ?? pathDiagnostic)({ cwd: state.cwd, packageRoot, env: p.env, mode: 'workflow' });
    state.agent = { id: agent.id, kind: agent.kind, command: agent.command };
    state.environment = keepEnv({ ...p.env, ...agent.env });
    state.activatedAt ??= new Date(p.now()).toISOString();
    state.enabled = true; state.timerInstalled = true; state.nextTick = p.now() + INTERVAL;
    if (runs === undefined) delete state.runs; else state.runs = Number(runs);
    await openWorkspace(state, p);
    save(stateFile, state);
    try { await timer('start', state, p); }
    catch { state.enabled = false; state.nextTick = null; save(stateFile, state); return bad('Autopilot timer could not start; enable your systemd user session on Linux or launchctl user session on macOS, then retry.'); }
    let warning = '';
    try { await tickAutopilot(stateFile, { ...ports, env: p.env }); }
    catch (e) { warning = ` Warning: ${line(e.message)}; next tick will retry.`; }
    return ok(`Autopilot running: ${state.repo} · ${agent.id} · pdd ${version} · next tick: ${new Date(state.nextTick).toISOString()}. See: herdr session attach ${SESSION}.${warning}${warnings.length ? ' ' + warnings.map(line).join(' ') : ''}`);
  } catch (e) { return bad(`Autopilot: ${e.code === 'ENOENT' ? 'install git, gh and Herdr, and sign in to your agent, then retry.' : line(e.message)}`); }
}

if (process.argv[1] && resolve(process.argv[1]) === self) {
  tickAutopilot(process.argv[2]).catch(error => { process.stderr.write(`Autopilot: ${line(error.message)}\n`); process.exitCode = 1; });
}

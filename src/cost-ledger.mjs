// Implements prompts/cli/cost-ledger.prompt.md.
import * as nativeFs from 'node:fs';
import { createHash } from 'node:crypto';
import { homedir } from 'node:os';
import { join } from 'node:path';

const DAY = 86_400_000, BYTES = 256 * 1024;
const uuid = value => typeof value === 'string' && /^[0-9a-f]{8}-(?:[0-9a-f]{4}-){3}[0-9a-f]{12}$/i.test(value);
const number = value => typeof value === 'number' && Number.isFinite(value) && value >= 0;
const hash = value => createHash('sha256').update(value).digest('hex').slice(0, 20);
const keys = ['input', 'cachedInput', 'output', 'reasoningOutput', 'total'];
const outcomes = ['merged', 'reverted', 'stuck', 'closed', 'parked'];
const emptyTokens = () => Object.fromEntries(keys.map(key => [key, 0]));
const readJson = (fs, file) => { try { return JSON.parse(fs.readFileSync(file, 'utf8')); } catch { return null; } };
const expand = (path, home) => typeof path === 'string' && path ? path.replace(/^~(?=\/|$)/, home) : null;
const event = (cost, at, metric, value, extra = {}) => { if (value > 0 || value === 0 && (['suiteMinutes', 'ciMinutes', 'activeMinutes'].includes(metric) || metric === 'total' && extra.account && !cost.tokens.some(row => row.account === extra.account))) cost.events.push({ at, metric, value, ...extra }); };

function initial(run, at) {
  return { schema: 'pdd.cost.v1', capturedAt: at, outcome: outcome(run), outcomeAt: run.cancelled?.at ?? run.updatedAt ?? at, tokens: [], sessions: {},
    person: { questions: 0, answers: 0, approvals: 0, waitingMinutes: 0, activeMinutes: null },
    suiteMinutes: null, ciMinutes: null, githubCalls: 0, events: [], measurements: {}, coverage: ['not-captured'], waits: {} };
}

// Positional reads have a fixed byte budget. Incomplete rows remain for a later capture.
function rows(fs, file, offset, tail = false) {
  let fd;
  try {
    fd = fs.openSync(file, 'r');
    const size = fs.fstatSync(fd).size, truncated = size < offset;
    let start = tail ? Math.max(0, size - BYTES) : truncated ? 0 : offset;
    const bytes = Buffer.alloc(Math.min(BYTES, size - start));
    let n = 0;
    while (n < bytes.length) { const count = fs.readSync(fd, bytes, n, bytes.length - n, start + n); if (!count) break; n += count; }
    const buffer = bytes.subarray(0, n), end = buffer.lastIndexOf(10);
    let text = end < 0 ? '' : buffer.subarray(0, end).toString('utf8');
    if (tail && start > 0) text = text.slice(text.indexOf('\n') + 1);
    // An overlong row cannot pin the cursor forever. It is skipped with incomplete coverage.
    const oversized = end < 0 && n === BYTES;
    const next = start + (end < 0 ? oversized ? n : 0 : end + 1);
    return { values: text.split('\n').flatMap(line => { try { return [JSON.parse(line)]; } catch { return []; } }),
      offset: next, backlog: next < size, truncated, oversized };
  } catch { return null; }
  finally { if (fd !== undefined) try { fs.closeSync(fd); } catch {} }
}

function sessionFile(fs, home, agent, id, chat, root, at) {
  if (agent === 'claude') return join(home, 'projects', root.replace(/[^a-zA-Z0-9]/g, '-'), `${id}.jsonl`);
  const v7 = /^[0-9a-f]{8}-[0-9a-f]{4}-7/i.test(id) ? parseInt(id.replaceAll('-', '').slice(0, 12), 16) : at;
  const first = Math.max(at - 31 * DAY, Math.min(at, chat.startedAt ?? at, v7) - DAY);
  const found = [];
  for (let day = new Date(first); day.getTime() <= at + DAY; day.setUTCDate(day.getUTCDate() + 1)) {
    const dir = join(home, 'sessions', String(day.getUTCFullYear()), String(day.getUTCMonth() + 1).padStart(2, '0'), String(day.getUTCDate()).padStart(2, '0'));
    let names; try { names = fs.readdirSync(dir); } catch { continue; }
    for (const name of names) if (name.startsWith('rollout-') && name.endsWith(`-${id}.jsonl`)) {
      try { found.push({ file: join(dir, name), at: fs.statSync(join(dir, name)).mtimeMs }); } catch {}
    }
  }
  return found.sort((a, b) => b.at - a.at)[0]?.file;
}
function tokenValues(usage, agent) {
  const fields = agent === 'codex'
    ? [usage.input_tokens, usage.cached_input_tokens ?? 0, usage.output_tokens, usage.reasoning_output_tokens ?? 0, usage.total_tokens]
    : [(usage.input_tokens ?? 0) + (usage.cache_creation_input_tokens ?? 0) + (usage.cache_read_input_tokens ?? 0), usage.cache_read_input_tokens ?? 0, usage.output_tokens, 0,
      (usage.input_tokens ?? 0) + (usage.cache_creation_input_tokens ?? 0) + (usage.cache_read_input_tokens ?? 0) + (usage.output_tokens ?? 0)];
  return fields.every(number) ? Object.fromEntries(keys.map((key, i) => [key, fields[i]])) : null;
}
function captureTokens(cost, run, ports, at) {
  const fs = ports.sessionFs ?? ports.fs ?? nativeFs, env = ports.env ?? process.env, home = env.HOME || homedir();
  const chats = [...(run.chats ?? []), ...[run.chatReplacement?.original, run.chatReplacement?.replacement].filter(Boolean)];
  const visited = new Set();
  for (const chat of chats) {
    const agent = chat.agent ?? run.agent, id = chat.session?.id;
    if (!['codex', 'claude'].includes(agent) || !uuid(id)) { cost.coverage.push('session-unavailable'); continue; }
    const config = expand(Object.hasOwn(chat, 'configDir') ? chat.configDir : run.configDir, home) ?? expand(env[agent === 'codex' ? 'CODEX_HOME' : 'CLAUDE_CONFIG_DIR'], home) ?? join(home, `.${agent}`);
    const account = `${agent}:${hash(config)}`, identity = hash(`${account}:${id}`);
    if (visited.has(identity)) continue; visited.add(identity);
    const saved = cost.sessions[identity] ?? { account, agent, offset: 0, usage: emptyTokens(), messages: {} };
    const file = sessionFile(fs, config, agent, id, chat, run.root, at);
    const batch = file ? rows(fs, file, saved.offset, agent === 'codex') : null;
    if (!batch) { cost.coverage.push('session-unavailable'); continue; }
    if (batch.backlog) cost.coverage.push('session-backlog');
    if (batch.truncated || batch.oversized) saved.incomplete = true;
    if (saved.incomplete) cost.coverage.push('session-truncated');
    for (const row of batch.values) {
      if (!row || typeof row !== 'object' || row.sessionId && row.sessionId !== id) continue;
      if (agent === 'codex') {
        if (row.type !== 'event_msg' || row.payload?.type !== 'token_count') continue;
        const usage = tokenValues(row.payload.info?.total_token_usage ?? {}, agent);
        if (usage) { saved.observed = true; for (const key of keys) saved.usage[key] = Math.max(saved.usage[key], usage[key]); }
      } else {
        if (row.type !== 'assistant' || row.isMeta || row.isApiErrorMessage || !row.message?.usage) continue;
        const messageId = row.message.id ?? row.uuid;
        if (typeof messageId !== 'string') { cost.coverage.push('usage-identity-missing'); continue; }
        const usage = tokenValues(row.message.usage, agent);
        if (!usage) continue;
        saved.observed = true;
        const key = hash(messageId), previous = saved.messages[key] ?? emptyTokens();
        for (const field of keys) { const delta = Math.max(0, usage[field] - previous[field]); saved.usage[field] += delta; previous[field] += delta; }
        saved.messages[key] = previous;
      }
    }
    saved.offset = batch.offset; cost.sessions[identity] = saved;
    if (!saved.observed) cost.coverage.push('usage-unavailable');
  }
  const accounts = new Map();
  for (const session of Object.values(cost.sessions)) {
    if (!session.observed) continue;
    if (!accounts.has(session.account)) accounts.set(session.account, { account: session.account, agent: session.agent, ...emptyTokens() });
    for (const key of keys) accounts.get(session.account)[key] += session.usage[key];
  }
  const tokens = [...accounts.values()].sort((a, b) => a.account.localeCompare(b.account));
  for (const row of tokens) for (const key of keys) event(cost, at, key, row[key] - (cost.tokens.find(old => old.account === row.account)?.[key] ?? 0), { account: row.account, agent: row.agent });
  cost.tokens = tokens;
}
function capturePerson(cost, before, run, at) {
  const requests = [before?.question, run.question].filter(Boolean);
  const gates = [before?.gate, run.gate, ...(run.decisions ?? []).filter(d => d.decision === 'approve' || d.decision === 'approved').map(d => ({ id: d.gateId, at: d.gateAt ?? d.at, area: d.stage, kind: 'approve' }))].filter(Boolean);
  for (const question of requests) {
    const id = `q:${question.at}:${question.area}`;
    if (!number(question.at) || cost.waits[id]) continue;
    cost.waits[id] = { kind: 'question', at: question.at, accountedAt: question.at, endedAt: null };
    cost.person.questions++; event(cost, at, 'questions', 1);
  }
  for (const gate of gates) {
    const id = `g:${gate.id ?? `${gate.at}:${gate.area}:${gate.kind}`}`;
    if (!number(gate.at) || cost.waits[id]) continue;
    cost.waits[id] = { kind: 'gate', gateId: gate.id ?? null, at: gate.at, accountedAt: gate.at, endedAt: null };
  }
  const answers = run.changes?.filter(change => change.answer) ?? [];
  const approvals = (run.decisions ?? []).filter(d => d.decision === 'approve' || d.decision === 'approved');
  for (const [id, wait] of Object.entries(cost.waits)) {
    if (wait.endedAt !== null) continue;
    const answer = wait.kind === 'question' ? answers.find(a => a.at >= wait.at && (!before?.question?.area || a.stage === before.question.area)) : null;
    const approval = wait.kind === 'gate' ? approvals.find(d => wait.gateId ? d.gateId === wait.gateId : (d.gateAt ?? d.at) === wait.at) : null;
    const current = wait.kind === 'question' ? run.question && id === `q:${run.question.at}:${run.question.area}`
      : run.gate && id === `g:${run.gate.id ?? `${run.gate.at}:${run.gate.area}:${run.gate.kind}`}`;
    if (answer || approval || !current || ['completed', 'cancelled'].includes(run.state)) {
      wait.endedAt = Math.min(at, answer?.at ?? approval?.at ?? at);
      if (answer) { cost.person.answers++; event(cost, at, 'answers', 1); }
      if (approval) {
        cost.person.approvals++; event(cost, at, 'approvals', 1);
      }
    }
    const end = wait.endedAt ?? at, minutes = Math.max(0, end - wait.accountedAt) / 60000;
    cost.person.waitingMinutes += minutes; event(cost, at, 'waitingMinutes', minutes); wait.accountedAt = Math.max(wait.accountedAt, end);
  }
}
function outcome(run) {
  if (run.cost?.explicitOutcome) return run.cost.explicitOutcome;
  if (run.state === 'paused') return 'parked';
  if (run.state === 'stuck') return 'stuck';
  if (run.state === 'cancelled') return 'closed';
  const last = run.pr?.at(-1);
  if (last?.state === 'merged' && last.stage === run.areas?.at(-1)?.name) return 'merged';
  if (last?.state === 'closed') return 'closed';
  return 'running';
}
export function captureCosts(before, run, ports = {}) {
  const at = (ports.now ?? Date.now)(), fs = ports.fs ?? nativeFs;
  const cost = structuredClone(run.cost?.schema === 'pdd.cost.v1' ? run.cost : before?.cost?.schema === 'pdd.cost.v1' ? before.cost : initial(run, at));
  cost.coverage = [];
  if (ports.skipCostSessions) cost.coverage.push('session-capture-deferred');
  else captureTokens(cost, { ...run, chats: [...(before?.chats ?? []), ...(run.chats ?? [])] }, ports, at); capturePerson(cost, before, run, at);
  const next = outcome({ ...run, cost });
  if (next !== cost.outcome) { cost.outcome = next; cost.outcomeAt = at; }
  const calls = (() => { try { return fs.readFileSync(join(run.runDir, 'github-cost.jsonl'), 'utf8').split('\n').filter(line => { try { return number(JSON.parse(line).at); } catch { return false; } }).length; } catch { return 0; } })();
  event(cost, at, 'githubCalls', Math.max(0, calls - cost.githubCalls)); cost.githubCalls = Math.max(cost.githubCalls, calls);
  let minutes = 0, known = false;
  for (const pr of run.pr ?? []) {
    const ci = readJson(fs, join(run.runDir, `cost-ci-${pr.number}.json`));
    if (!ci?.complete) cost.coverage.push('ci-unavailable');
    if (number(ci?.minutes)) { minutes += ci.minutes; known = true; }
  }
  if (known) { if (cost.ciMinutes === null || minutes > cost.ciMinutes) event(cost, at, 'ciMinutes', Math.max(0, minutes - (cost.ciMinutes ?? 0))); cost.ciMinutes = minutes; }
  if (cost.suiteMinutes === null) cost.coverage.push('suite-unavailable');
  if (cost.person.activeMinutes === null) cost.coverage.push('person-active-unavailable');
  if (!run.chats?.length) cost.coverage.push('session-unavailable');
  cost.coverage.push('github-unattributed-excluded');
  cost.coverage = [...new Set(cost.coverage)].sort(); cost.capturedAt = at;
  return cost;
}

export function applyCostMeasurement(run, input, at) {
  if (!input || Array.isArray(input) || typeof input !== 'object' || Object.keys(input).some(key => !['id', 'suiteMinutes', 'personMinutes', 'outcome'].includes(key)) ||
    typeof input.id !== 'string' || !/^[A-Za-z0-9_.-]{1,100}$/.test(input.id) ||
    !['suiteMinutes', 'personMinutes', 'outcome'].some(key => Object.hasOwn(input, key)) ||
    ['suiteMinutes', 'personMinutes'].some(key => Object.hasOwn(input, key) && !number(input[key])) ||
    Object.hasOwn(input, 'outcome') && !outcomes.includes(input.outcome)) throw Error('Invalid cost measurement');
  const value = Object.fromEntries(Object.entries(input).sort(([a], [b]) => a.localeCompare(b)));
  const cost = run.cost ??= initial(run, at), previous = cost.measurements[input.id];
  if (previous) { if (JSON.stringify(previous) !== JSON.stringify(value)) throw Error('Cost measurement id conflict'); return run; }
  cost.measurements[input.id] = value;
  if (Object.hasOwn(input, 'suiteMinutes')) { cost.suiteMinutes = (cost.suiteMinutes ?? 0) + input.suiteMinutes; event(cost, at, 'suiteMinutes', input.suiteMinutes); }
  if (Object.hasOwn(input, 'personMinutes')) { cost.person.activeMinutes = (cost.person.activeMinutes ?? 0) + input.personMinutes; event(cost, at, 'activeMinutes', input.personMinutes); }
  if (input.outcome) { cost.explicitOutcome = input.outcome; cost.outcome = input.outcome; cost.outcomeAt = at; }
  return run;
}
export function recordCostGithub(runDir, entry, { fs = nativeFs } = {}) {
  try { fs.mkdirSync(runDir, { recursive: true, mode: 0o700 }); fs.appendFileSync(join(runDir, 'github-cost.jsonl'), JSON.stringify({ at: entry.at }) + '\n', { mode: 0o600 }); } catch {}
}
export async function captureClosedCi(run, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  for (const pr of run.pr ?? []) {
    if (!['closed', 'merged'].includes(pr.state) || !Number.isSafeInteger(pr.number) || pr.number < 1) continue;
    const head = pr.head ?? pr.headSha, branch = typeof pr.branch === 'string' && pr.branch.length > 0 && !/[\x00-\x20\x7f]/.test(pr.branch) ? pr.branch : null;
    if ((!branch && (typeof head !== 'string' || !/^[0-9a-f]{40,64}$/i.test(head))) || !/^[\w.-]+\/[\w.-]+$/.test(run.repo)) continue;
    const file = join(run.runDir, `cost-ci-${pr.number}.json`);
    try { fs.writeFileSync(file, JSON.stringify({ attempted: true, minutes: null, complete: false }), { mode: 0o600, flag: 'wx' }); } catch { continue; }
    let minutes = null, complete = false;
    try {
      const result = await ports.execFile('gh', ['api', `repos/${run.repo}/actions/runs?${branch ? `branch=${encodeURIComponent(branch)}` : `head_sha=${head}`}&per_page=100`], { cwd: run.root });
      if (result.code && result.code !== 0) throw Error('CI read failed');
      const response = JSON.parse(result.stdout);
      if (!Array.isArray(response.workflow_runs) || !Number.isInteger(response.total_count)) throw Error('Invalid CI durations');
      const selected = response.workflow_runs.filter(row => row.pull_requests?.length ? row.pull_requests.some(pull => pull.number === pr.number) : branch ? row.head_branch === branch : row.head_sha === head);
      complete = Boolean(branch) && response.total_count <= response.workflow_runs.length;
      minutes = 0;
      for (const row of selected) {
        if (row.run_attempt > 1) complete = false;
        const duration = Date.parse(row.updated_at) - Date.parse(row.run_started_at);
        if (row.status !== 'completed' || !number(duration)) { complete = false; continue; }
        minutes += duration / 60000;
      }
    } catch {}
    try { fs.writeFileSync(file, JSON.stringify({ attempted: true, minutes, complete }), { mode: 0o600 }); } catch {}
  }
}

function total(costs) {
  const tokens = new Map(), person = { questions: 0, answers: 0, approvals: 0, waitingMinutes: 0, activeMinutes: null };
  let suiteMinutes = null, ciMinutes = null, githubCalls = 0;
  for (const cost of costs) {
    for (const row of cost.tokens) {
      if (!tokens.has(row.account)) tokens.set(row.account, { account: row.account, agent: row.agent, ...emptyTokens() });
      for (const key of keys) tokens.get(row.account)[key] += row[key];
    }
    for (const key of Object.keys(person)) if (cost.person[key] !== null) person[key] = (person[key] ?? 0) + cost.person[key];
    if (cost.suiteMinutes !== null) suiteMinutes = (suiteMinutes ?? 0) + cost.suiteMinutes;
    if (cost.ciMinutes !== null) ciMinutes = (ciMinutes ?? 0) + cost.ciMinutes;
    githubCalls += cost.githubCalls;
  }
  return { totalTokens: tokens.size ? [...tokens.values()].reduce((sum, row) => sum + row.total, 0) : null, tokens: [...tokens.values()].sort((a,b) => a.account.localeCompare(b.account)), person, suiteMinutes, ciMinutes, githubCalls };
}
function eventsTotal(events) {
  const result = { tokens: [], person: { questions: 0, answers: 0, approvals: 0, waitingMinutes: 0, activeMinutes: null }, suiteMinutes: null, ciMinutes: null, githubCalls: 0 };
  for (const e of events) {
    if (keys.includes(e.metric) && e.account) {
      let row = result.tokens.find(row => row.account === e.account);
      if (!row) { row = { account: e.account, agent: e.agent, ...emptyTokens() }; result.tokens.push(row); }
      row[e.metric] += e.value;
    } else if (Object.hasOwn(result.person, e.metric)) result.person[e.metric] = (result.person[e.metric] ?? 0) + e.value;
    else if (['suiteMinutes', 'ciMinutes', 'githubCalls'].includes(e.metric)) result[e.metric] = (result[e.metric] ?? 0) + e.value;
  }
  result.totalTokens = result.tokens.length ? result.tokens.reduce((sum, row) => sum + row.total, 0) : null;
  result.tokens.sort((a,b) => a.account.localeCompare(b.account)); return result;
}
function percentile(rows, q) {
  if (!rows.length) return null;
  const rank = values => values.length ? values.sort((a,b) => a-b)[Math.ceil(values.length*q)-1] : null;
  const result = total([]);
  for (const key of ['totalTokens','suiteMinutes','ciMinutes','githubCalls']) result[key] = rank(rows.map(row => row[key]).filter(number));
  for (const key of Object.keys(result.person)) result.person[key] = rank(rows.map(row => row.person[key]).filter(number));
  for (const account of new Set(rows.flatMap(row => row.tokens.map(token => token.account)))) {
    const token = rows.flatMap(row => row.tokens).find(row => row.account === account);
    result.tokens.push({ account, agent: token.agent, ...Object.fromEntries(keys.map(key => [key, rank(rows.map(row => row.tokens.find(token => token.account === account)?.[key] ?? 0))])) });
  }
  return result;
}
export function costReport(runs, now) {
  const costs = runs.map(run => ({ run, cost: run.cost ?? initial(run, now) }));
  const publicRows = costs.map(({ run, cost }) => ({ repo: run.repo, issue: run.number, runId: run.runId,
    ...Object.fromEntries(['outcome','outcomeAt','tokens','person','suiteMinutes','ciMinutes','githubCalls','coverage'].map(key => [key, cost[key]])) }));
  const window = days => {
    const since = now - days * DAY, groups = new Map();
    for (const row of costs) { const key = `${row.run.repo.toLowerCase()}#${row.run.number}`; if (!groups.has(key)) groups.set(key, []); groups.get(key).push(row); }
    const merged = [...groups.values()].filter(group => {
      const latest = [...group].sort((a,b) => (b.run.startedAt ?? 0) - (a.run.startedAt ?? 0))[0].cost;
      return latest.outcome === 'merged' && latest.outcomeAt > since && latest.outcomeAt <= now;
    }).map(group => total(group.map(row => row.cost)));
    return { since, totals: eventsTotal(costs.flatMap(row => row.cost.events).filter(e => e.at > since && e.at <= now)),
      coverage: [...new Set(costs.flatMap(row => row.cost.coverage))].sort(), mergedIssues: merged.length, p50: percentile(merged, 0.5), p90: percentile(merged, 0.9) };
  };
  return { schema: 'pdd.cost-report.v1', generatedAt: now, runs: publicRows, day: window(1), week: window(7) };
}
export function costStatusLines(report) {
  const num = value => value === null ? 'unknown' : Number(value.toFixed(2));
  const describe = row => row ? `${num(row.totalTokens)} tokens; CI ${num(row.ciMinutes)} min; suite ${num(row.suiteMinutes)} min; GitHub ${row.githubCalls}; person Q/A/approvals ${row.person.questions}/${row.person.answers}/${row.person.approvals}, active ${num(row.person.activeMinutes)} min, wait ${num(row.person.waitingMinutes)} min` : 'no merged issues';
  const lines = ['Issue costs (local measured usage):'];
  for (const key of ['day','week']) {
    const row = report[key]; lines.push(`Last ${key}: ${describe(row.totals)}`, `  Per merged issue (${row.mergedIssues}): P50 ${describe(row.p50)}; P90 ${describe(row.p90)}`);
    for (const token of row.totals.tokens) lines.push(`  ${token.account}: ${token.total} tokens (input ${token.input}, cached ${token.cachedInput}, output ${token.output}, reasoning ${token.reasoningOutput})`);
    if (row.coverage.length) lines.push(`  Coverage: ${row.coverage.join(', ')}`);
  }
  lines.push(`Outcomes: ${['running',...outcomes].map(outcome => `${outcome} ${report.runs.filter(row => row.outcome === outcome).length}`).join(', ')}`);
  return lines.join('\n');
}

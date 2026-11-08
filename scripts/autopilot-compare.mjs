// Implements prompts/cli/autopilot-compare.prompt.md. Development-only, offline.
import { readFileSync, realpathSync } from 'node:fs';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { createHash } from 'node:crypto';
import { isDeepStrictEqual } from 'node:util';
import { autopilotGithubWorld, analysisFor } from '../test/helpers/autopilot-github-world.mjs';

const schema = 'pdd.autopilot-compare.v1';
const fixture = new URL('../test/fixtures/autopilot-compare-backlog.json', import.meta.url);
const kinds = ['comments', 'blockedBy', 'blocking', 'timeline'];
const object = v => v !== null && typeof v === 'object' && !Array.isArray(v);
const finite = Number.isFinite;
const numberFrom = key => Number(String(key).split('/').at(-1));
const sortedNumbers = rows => [...new Set(rows.map(numberFrom))].sort((a, b) => a - b);
const sumKeys = ['restCalls', 'restWrites', 'graphqlCalls', 'graphqlWrites', 'writes', 'deliveries'];
const fail = () => { throw Error('Invalid replay data. Use the documented saved snapshot shape.'); };
const hash = text => createHash('sha256').update(text).digest('hex');
const canonical = value => JSON.stringify(value, (_key, item) => object(item)
  ? Object.fromEntries(Object.keys(item).sort().map(k => [k, item[k]])) : item);

export function validateReplay(replay) {
  if (!object(replay) || replay.schema_version !== schema || typeof replay.synthetic !== 'boolean'
    || !Array.isArray(replay.frames) || !replay.frames.length
    || (replay.completeIndependent !== undefined && typeof replay.completeIndependent !== 'boolean')
    || (replay.completeIndependent && !replay.synthetic)) fail();
  let last = -Infinity, repository;
  const names = new Set();
  for (const frame of replay.frames) {
    const s = frame?.snapshot;
    if (!object(frame) || typeof frame.name !== 'string' || !/^[a-z0-9-]+$/.test(frame.name) || names.has(frame.name)
      || !finite(frame.at) || !finite(Date.parse(new Date(frame.at).toISOString())) || frame.at <= last
      || !object(s) || s.v !== 1 || !/^[a-z0-9-]+\/[a-z0-9_.-]+$/.test(s.repository)
      || (repository && s.repository !== repository) || !finite(s.refreshedAt) || s.refreshedAt > frame.at
      || !object(s.list) || !object(s.list.rows) || !finite(s.list.readAt) || s.list.readAt > frame.at
      || !finite(Date.parse(s.list.since)) || !object(s.issues) || !object(s.invalid)) fail();
    repository = s.repository; last = frame.at; names.add(frame.name);
    const rows = { ...Object.fromEntries(Object.entries(s.issues).filter(([, e]) => e.raw).map(([n, e]) => [n, e.raw])), ...s.list.rows };
    for (const [n, row] of Object.entries(rows)) {
      if (!object(row) || !Number.isSafeInteger(row.number) || row.number < 1 || String(row.number) !== n
        || row.html_url !== `https://github.com/${repository}/issues/${n}` || !Number.isSafeInteger(row.id)
        || !['open', 'closed'].includes(row.state) || typeof row.title !== 'string'
        || !(row.body === null || typeof row.body === 'string') || !Array.isArray(row.labels)
        || row.labels.some(l => typeof l !== 'string' && typeof l?.name !== 'string')
        || typeof row.user?.login !== 'string' || !finite(Date.parse(row.created_at)) || !finite(Date.parse(row.updated_at))
        || !object(s.issues[n]?.kinds) || kinds.some(k => !Array.isArray(s.issues[n].kinds[k]))
        || row.comments !== s.issues[n].kinds.comments.length
        || !object(row.issue_dependencies_summary)
        || ['blocked_by', 'total_blocked_by'].some(k => row.issue_dependencies_summary[k] !== s.issues[n].kinds.blockedBy.length)
        || ['blocking', 'total_blocking'].some(k => row.issue_dependencies_summary[k] !== s.issues[n].kinds.blocking.length)
        || (replay.completeIndependent && Object.values(row.issue_dependencies_summary ?? {}).some(v => v !== 0))) fail();
    }
    for (const [n, entry] of Object.entries(s.issues)) {
      if (!rows[n] || !object(entry) || !(entry.version === null || typeof entry.version === 'string')
        || !finite(entry.observedAt) || !object(entry.kinds) || Object.keys(entry.kinds).some(k => !kinds.includes(k))) fail();
      for (const [kind, items] of Object.entries(entry.kinds)) {
        if (!Array.isArray(items)) fail();
        if (new Set(items.map(i => kind === 'comments' || kind === 'timeline' ? i?.id : i?.html_url)).size !== items.length) fail();
        for (const item of items) {
          if (!object(item)) fail();
          if (kind === 'comments' && (!Number.isSafeInteger(item.id) || typeof item.body !== 'string'
            || typeof item.user?.login !== 'string' || !finite(Date.parse(item.created_at)) || !finite(Date.parse(item.updated_at)))) fail();
          if (kind === 'timeline' && (!Number.isSafeInteger(item.id) || typeof item.event !== 'string'
            || typeof item.actor?.login !== 'string' || !finite(Date.parse(item.created_at)))) fail();
          if (['blockedBy', 'blocking'].includes(kind) && !Object.values(rows).some(r => r.html_url === item.html_url)) fail();
          if (kind === 'blocking' && !s.issues[numberFrom(item.html_url)]?.kinds?.blockedBy?.some(i => i.html_url === rows[n].html_url)) fail();
          if (kind === 'blockedBy' && !s.issues[numberFrom(item.html_url)]?.kinds?.blocking?.some(i => i.html_url === rows[n].html_url)) fail();
        }
        if (replay.completeIndependent && ['blockedBy', 'blocking'].includes(kind) && items.length) fail();
      }
    }
  }
  return replay;
}

// Update recorded observations only. Keep the selected version's fake writes.
function applySnapshot(w, snapshot, previous) {
  const rowsOf = s => ({ ...Object.fromEntries(Object.entries(s?.issues ?? {}).filter(([, e]) => e.raw).map(([n, e]) => [n, e.raw])), ...s?.list.rows });
  const rows = rowsOf(snapshot), before = rowsOf(previous);
  for (const n of Object.keys(before)) if (!rows[n]) w.github.remove(Number(n));
  for (const [n, row] of Object.entries(rows)) {
    const old = before[n], issue = w.github.issues.get(Number(n)) ?? w.github.add(Number(n));
    issue.deleted = false;
    const set = (field, value) => { if (!old || !isDeepStrictEqual(old[field], row[field])) value(); };
    set('id', () => { issue.id = String(row.id); });
    for (const field of ['title', 'body', 'state', 'state_reason']) set(field, () => { issue[field] = row[field]; });
    set('user', () => { issue.user = row.user.login; });
    set('labels', () => { issue.labels = row.labels.map(l => typeof l === 'string' ? l : l.name); });
    set('created_at', () => { issue.created = Date.parse(row.created_at); });
    set('updated_at', () => { issue.updated = Date.parse(row.updated_at); });
    const entry = snapshot.issues[n], oldEntry = previous?.issues[n];
    for (const kind of kinds) {
      const items = entry?.kinds[kind] ?? [], prior = oldEntry?.kinds[kind] ?? [];
      if (old && isDeepStrictEqual(items, prior)) continue;
      if (kind === 'comments') {
        const priorIds = new Set(prior.map(c => String(c.id)));
        issue.comments = [...issue.comments.filter(c => !priorIds.has(c.id)), ...items.map(c => ({ id: String(c.id), body: c.body, user: c.user.login,
          created: Date.parse(c.created_at), updated: Date.parse(c.updated_at) }))];
      } else if (kind === 'timeline') {
        const priorIds = new Set(prior.map(e => String(e.id)));
        issue.timeline = [...issue.timeline.filter(e => !priorIds.has(e.id)), ...items.map(e => ({ id: String(e.id), event: e.event, actor: e.actor.login,
          created: Date.parse(e.created_at), ...(e.label ? { label: e.label.name } : {}) }))];
      } else if (kind === 'blockedBy') issue.blockedBy = items.map(i => numberFrom(i.html_url));
      // blocking is derived by the repo fake from the inverse blockedBy links.
    }
  }
}

function packetDecision(text) {
  const artifact = /Artifact path: (.+)/.exec(text)?.[1];
  const content = artifact ? readFileSync(JSON.parse(artifact), 'utf8') : text;
  if (text.includes('Dependency analysis request artifact')) {
    const request = JSON.parse(content);
    return { kind: 'dependency-review', issues: sortedNumbers(request.issues) };
  }
  // The native work message ends in a JSON packet, as in the process replay.
  const packet = JSON.parse(content.trim().split('\n').at(-1));
  if (!Array.isArray(packet.issues) || (packet.timeRules !== undefined && !Array.isArray(packet.timeRules))) throw Error('Unsupported work packet.');
  return { kind: 'work', issues: packet.issues.map(i => ({ number: i.number, eligible: i.eligible === true, claimed: i.claimed === true,
      expiredClaim: !!i.expiredClaim })).sort((a, b) => a.number - b.number),
    timeRules: (packet.timeRules ?? []).map(r => ({ kind: r.kind, number: r.number })).sort((a, b) => a.number - b.number || a.kind.localeCompare(b.kind)) };
}

async function runSide(root, replay) {
  const source = realpathSync(root), version = JSON.parse(readFileSync(resolve(source, 'package.json'), 'utf8')).version;
  const w = await autopilotGithubWorld({ src: resolve(source, 'src'), issues: 0, repository: replay.frames[0].snapshot.repository,
    environment: Object.fromEntries(Object.keys(process.env).map(k => [k, undefined])),
    machine: 'compare-machine', start: replay.frames[0].at });
  try {
    const payloads = new Map(), generations = new Map(), blobs = new Map();
    const identity = (map, value, prefix) => {
      if (!map.has(value)) map.set(value, `<${prefix}:${map.size + 1}>`);
      return map.get(value);
    };
    const originalGithub = w.github.gh;
    w.github.gh = async (args, options = {}) => {
      const mark = w.github.calls.length;
      const reply = await originalGithub(args, options);
      const call = w.github.calls[mark];
      if (call && (call.api === 'graphql' ? /^\s*mutation\b/.test(call.query) : !['GET', 'HEAD'].includes(call.method))) {
        const body = options.input === undefined ? (args.includes('-f')
          ? { body: args[args.indexOf('-f') + 1].replace(/^body=/, '') } : null) : JSON.parse(options.input);
        if (call.endpoint.endsWith('/contents/.pdd-reviewer.json') && object(body)) {
          if (body.sha && blobs.has(body.sha)) body.sha = blobs.get(body.sha);
          if (body.content) {
            const lease = JSON.parse(Buffer.from(body.content, 'base64').toString('utf8'));
            if (lease.coordinatorId === w.state().coordinatorId) lease.coordinatorId = '<coordinator:self>';
            if (lease.generation) lease.generation = identity(generations, lease.generation, 'lease-generation');
            body.content = lease;
          }
          const saved = w.github.contents.get(body.branch);
          if (saved) identity(blobs, saved.sha, 'lease-blob');
        }
        payloads.set(call, hash(canonical(body)));
      }
      return reply;
    };
    const decisions = [], originalHerdr = w.ports.herdr;
    w.ports.herdr = async args => {
      if (args[0] === 'agent' && args[1] === 'prompt') decisions.push(packetDecision(args.at(-1)));
      return originalHerdr(args);
    };
    const frames = [];
    let previous, handled = 0;
    for (const frame of replay.frames) {
      w.time = frame.at; w.agent = 'idle';
      applySnapshot(w, frame.snapshot, previous);
      const mark = w.github.calls.length, decisionMark = decisions.length, promptMark = w.prompts.length;
      const result = previous ? await w.tick() : await w.invoke('start');
      if (result.exitCode !== 0) throw Error(`Replay did not complete at ${frame.name}.`);
      if (replay.completeIndependent) {
        let drained = 0;
        while (handled < w.requests.length) {
          if (++drained > 20) throw Error('Synthetic review drain limit reached.');
          const request = w.requests[handled++];
          const answer = await w.complete(request, analysisFor(request));
          if (answer.exitCode !== 0) throw Error(`Synthetic completion failed at ${frame.name}.`);
          await w.idle();
        }
      }
      const state = w.state();
      const rawCalls = w.github.calls.slice(mark);
      const calls = rawCalls.map(c => ({ api: c.api, method: c.method, endpoint: c.endpoint, status: c.status,
        conditional: c.conditional, ...(c.api === 'graphql' ? { mutation: /^\s*mutation\b/.test(c.query) } : {}) }));
      const writes = calls.flatMap((c, i) => (c.api === 'graphql' ? c.mutation : !['GET', 'HEAD'].includes(c.method))
        ? [{ ...c, payloadSha256: payloads.get(rawCalls[i]) }] : []);
      const restWrites = writes.filter(c => c.api === 'rest').length;
      frames.push({ name: frame.name, at: frame.at, outcome: previous ? 'tick-returned' : 'started',
        decisions: { delivered: decisions.slice(decisionMark), eligible: sortedNumbers(state.githubIntake?.eligible ?? []),
          pendingReview: w.requests.length > handled, retryAt: state.retryAt ?? null, reviewQueueUnknown: state.reviewQueueUnknown === true }, calls, writes,
        metrics: { restCalls: calls.filter(c => c.api === 'rest').length, restWrites, graphqlCalls: calls.filter(c => c.api === 'graphql').length,
          graphqlWrites: writes.length - restWrites, writes: writes.length, deliveries: w.prompts.length - promptMark } });
      previous = frame.snapshot;
    }
    return { root: source, version, frames, totals: Object.fromEntries(sumKeys.map(k => [k, frames.reduce((n, f) => n + f.metrics[k], 0)])) };
  } finally { w.cleanup(); }
}

export async function compareAutopilot({ oldRoot, newRoot, replay }) {
  // Serialize once so each side receives the very same observations and no mutation can cross sides.
  const input = JSON.stringify(validateReplay(replay));
  const old = await runSide(oldRoot, JSON.parse(input)), next = await runSide(newRoot, JSON.parse(input));
  return { schema_version: schema, synthetic: replay.synthetic, inputSha256: createHash('sha256').update(input).digest('hex'),
    selfComparison: old.root === next.root, old, new: next,
    comparison: old.frames.map((a, i) => {
      const b = next.frames[i];
      return { name: a.name, decisionsEqual: isDeepStrictEqual([a.outcome, a.decisions], [b.outcome, b.decisions]),
        callsEqual: isDeepStrictEqual(a.calls, b.calls), writesEqual: isDeepStrictEqual(a.writes, b.writes),
        restDelta: b.metrics.restCalls - a.metrics.restCalls, writeDelta: b.metrics.writes - a.metrics.writes,
        deliveryDelta: b.metrics.deliveries - a.metrics.deliveries };
    }) };
}

export function comparisonTable(report) {
  const lines = [
    `Offline replay (${report.synthetic ? 'synthetic' : 'sanitized external'} input${report.selfComparison ? '; SELF COMPARISON' : ''}).`,
    `Old: ${report.old.version} at ${report.old.root}`, `New: ${report.new.version} at ${report.new.root}`,
    `Shared input SHA-256: ${report.inputSha256}`, '',
    '| Metric (attempts, including setup) | Old | New | New - old |', '| --- | ---: | ---: | ---: |',
    ...sumKeys.map(k => `| ${k} | ${report.old.totals[k]} | ${report.new.totals[k]} | ${report.new.totals[k] - report.old.totals[k]} |`), '',
    '| Frame | Decisions | Call trace | Write trace | REST delta | Write delta | Delivery delta |',
    '| --- | --- | --- | --- | ---: | ---: | ---: |',
    ...report.comparison.map(r => `| ${r.name} | ${r.decisionsEqual ? 'equal' : 'different'} | ${r.callsEqual ? 'equal' : 'different'} | ${r.writesEqual ? 'equal' : 'different'} | ${r.restDelta} | ${r.writeDelta} | ${r.deliveryDelta} |`), '',
    'Unmeasured: issues/hour, AI tokens/cost (#3061), CI minutes, person interventions, stuck runs, duplicate claims, wrong merges, false-green evidence and reverts.',
    'Write traces include normalized payload hashes. Differences need review. This is not a merge gate result.',
  ];
  return `${lines.join('\n')}\n`;
}

const usage = 'Usage: node scripts/autopilot-compare.mjs --old ROOT --new ROOT [--replay FILE] [--json]\n';
export async function main(argv, io = process) {
  const options = {};
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === '--help' && argv.length === 1) { io.stdout.write(usage); return 0; }
    if (!['--old', '--new', '--replay', '--json'].includes(arg) || Object.hasOwn(options, arg)
      || (arg !== '--json' && (!argv[i + 1] || argv[i + 1].startsWith('--')))) { io.stderr.write(usage); return 2; }
    options[arg] = arg === '--json' ? true : argv[++i];
  }
  if (!options['--old'] || !options['--new']) { io.stderr.write(usage); return 2; }
  try {
    const replay = JSON.parse(readFileSync(options['--replay'] ?? fixture, 'utf8'));
    const report = await compareAutopilot({ oldRoot: options['--old'], newRoot: options['--new'], replay });
    io.stdout.write(options['--json'] ? `${JSON.stringify(report, null, 2)}\n` : comparisonTable(report));
    return 0;
  } catch {
    // Do not print snapshot bodies, source exception text or credentials.
    io.stderr.write('Offline replay failed. Check local source compatibility and replay data.\n'); return 1;
  }
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) process.exitCode = await main(process.argv.slice(2));

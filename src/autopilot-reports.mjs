// Generated from prompts/cli/autopilot-reports.prompt.md (sha256: 1ae5b3fbf1cf59b48c91ac97d87f9f996d3ebcbfaad27ad366a743755224ea17).
import * as nativeFs from 'node:fs';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { redactSecrets } from './secret-redaction.mjs';

export const REPORT_REPOSITORY = 'promptdriven/pdd';
const DAY = 24 * 60 * 60 * 1000, RECENT = 14 * DAY;
const LOGIN = /^[a-z\d](?:[a-z\d]|-(?=[a-z\d])){0,38}$/i;
const LABELS = { runtime: 'pdd:runtime', pdd: 'pdd:autopilot-report' };
const slug = value => String(value ?? '').toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, '').slice(0, 40);
const minor = version => /^(\d+)\.(\d+)/.exec(String(version ?? ''))?.slice(1, 3).join('.') ?? 'unknown';
const readJson = (fs, file, fallback) => { try { return JSON.parse(fs.readFileSync(file, 'utf8')); } catch { return fallback; } };
function save(fs, file, value) {
  fs.mkdirSync(join(file, '..'), { recursive: true, mode: 0o700 });
  const temp = `${file}.${process.pid}.tmp`;
  fs.writeFileSync(temp, JSON.stringify(value, null, 2) + '\n', { mode: 0o600 }); fs.renameSync(temp, file);
}

export function reportFingerprint({ kind, component, code, version }) {
  return [slug(kind), slug(component) || 'unknown', slug(code) || 'unknown', minor(version)].join('.');
}
export const reportMarker = fingerprint => `<!-- pdd:autopilot-report:${fingerprint} -->`;

// Safe text: versions, step, error code, counts and a short redacted tail. Paths, URLs and repository names go.
function safeTail(text, words = []) {
  let value = redactSecrets(String(text ?? ''));
  value = value.replace(/https?:\/\/\S+/g, '[url]').replace(/(?:~|\.{0,2})?(?:\/[\w.@+-]+){2,}\/?/g, '[path]');
  for (const word of words.filter(w => typeof w === 'string' && w.length > 2)) value = value.split(word).join('[repository]');
  return value.split(/\r?\n/).map(line => line.slice(0, 200)).filter(line => line.trim()).slice(-20).join('\n');
}

// The public text has fixed fields only (kind, component, code, step, versions, count, fingerprint), never free-form
// text. A draft written earlier may lack the fields: its fingerprint KIND.COMPONENT.CODE.MINOR gives the first three.
function publicReport(draft) {
  const [kind = 'unknown', component = 'unknown', code = 'unknown'] = String(draft.fingerprint ?? '').split('.');
  const f = { kind: draft.kind === 'runtime' ? 'runtime' : 'pdd', component: slug(draft.component ?? component) || 'unknown', code: slug(draft.code ?? code) || 'unknown',
    step: slug(draft.step) || 'unknown', versions: draft.versions && typeof draft.versions === 'object' ? draft.versions : {} };
  const known = value => /^[\w.+-]{1,40}$/.test(String(value ?? '')) ? value : 'unknown';
  const name = f.kind === 'runtime' ? 'Runtime' : 'PDD';
  const title = `Autopilot report: ${name} ${f.component} ${f.code} (PDD ${minor(f.versions.pdd)})`;
  const body = [f.code === 'adopt-pdd' ? 'Autopilot changed existing code that no prompt owns (path e, a direct change with a regression test). Please adopt PDD for those modules (the local draft on the Autopilot machine lists them): give each one a prompt and a binding or header.'
    : draft.shipped === true && f.code === 'vector-replay' && f.component === 'autopilot-core' ? 'Autopilot could not run the replay or formal tests of one PR. The PR went on, with that claim marked as not checked in its merge note.'
    : draft.shipped === true ? 'Autopilot shipped one PR with "Runtime: not run" because Runtime could not check it. The job did not wait for a fix.'
    : draft.stopped === true && f.code === 'stop-loop' ? 'Autopilot holds one issue: its own steps or a service stopped 3 jobs of it in 24 hours. The issue gets no strike; Autopilot takes it again after a new engine version or a person\'s comment on it.'
    : draft.stopped === true ? 'Autopilot stopped one of its own steps for one job: it made no progress. The issue gets no strike, and Autopilot tries again later.'
    : `Autopilot ended one job because of a ${name} problem. The job did not wait for a fix.`, '',
    `- Kind: ${f.kind}`, `- Component: ${f.component}`, `- Error code: ${f.code}`, `- Step: ${f.step}`,
    `- Versions: PDD ${known(f.versions.pdd)}, Node ${known(f.versions.node)}, ${known(f.versions.platform)}, agent ${known(f.versions.agent)}`,
    `- Seen on this machine: ${Number.isSafeInteger(draft.count) && draft.count > 0 ? draft.count : 1}`,
    '', 'The detail stays in the local draft on the Autopilot machine.', '', reportMarker(draft.fingerprint)].join('\n');
  return { title, body };
}

function draftFor({ cause, versions, step, words, runtimeRepo, runtimeOwner }) {
  const fingerprint = reportFingerprint({ ...cause, version: versions.pdd });
  const kind = cause.kind === 'runtime' ? 'runtime' : 'pdd';
  const draft = { fingerprint, kind, component: slug(cause.component) || 'unknown', code: slug(cause.code) || 'unknown', step: slug(step) || 'unknown',
    versions: { pdd: versions.pdd ?? null, node: versions.node ?? null, platform: versions.platform ?? null, agent: versions.agent ?? null },
    ...(cause.shipped === true ? { shipped: true } : {}), ...(cause.stopped === true ? { stopped: true } : {}), ...(runtimeRepo ? { runtimeRepo } : {}), ...(LOGIN.test(String(runtimeOwner ?? '')) ? { runtimeOwner } : {}),
    repository: REPORT_REPOSITORY, labels: [LABELS[kind]], detail: safeTail(cause.detail || cause.text, words) || '' };
  return { ...draft, ...publicReport(draft) };
}

function github(ports) {
  return async (method, endpoint, body) => {
    const args = ['api', '--include', '--method', method, endpoint, ...(body === undefined ? [] : ['--input', '-'])];
    const r = await ports.gh(args, body === undefined ? {} : { input: JSON.stringify(body) });
    const text = String(r.stdout ?? ''), cut = text.search(/\r?\n\r?\n/), status = Number(/^HTTP\/\S+\s+(\d+)/.exec(text)?.[1] ?? 0);
    if (status < 200 || status >= 300) throw Error(`GitHub ${method} returned ${status || 'no reply'}`);
    return { value: cut >= 0 && text.slice(cut).trim() ? JSON.parse(text.slice(cut).trim()) : null, next: /<https:\/\/api\.github\.com\/([^>]+)>;\s*rel="next"/.exec(text.slice(0, Math.max(cut, 0)))?.[1] };
  };
}

// Open reports with the marker, and reports closed in the last 14 days.
async function findReport(api, draft, now) {
  let endpoint = `repos/${draft.repository}/issues?state=all&labels=${encodeURIComponent(draft.labels[0])}&per_page=100`;
  for (let page = 0; endpoint && page < 5; page++) {
    const { value, next } = await api('GET', endpoint);
    const found = (value ?? []).find(row => !row.pull_request && String(row.body ?? '').includes(reportMarker(draft.fingerprint))
      && (row.state === 'open' || now - Date.parse(row.closed_at) < RECENT));
    if (found) return found;
    endpoint = next;
  }
  return null;
}

// The owner repository: a Runtime cause goes to the configured Runtime repository when this machine can read it,
// else to promptdriven/pdd with label pdd:runtime. A PDD cause always goes to promptdriven/pdd.
async function ownerRepository(api, draft, runtimeRepo) {
  if (draft.kind !== 'runtime' || !/^[\w.-]+\/[\w.-]+$/.test(String(runtimeRepo ?? ''))) return REPORT_REPOSITORY;
  try { await api('GET', `repos/${runtimeRepo}`); return runtimeRepo; } catch { return REPORT_REPOSITORY; }
}
// Send one report through the dedup rules: one issue per cause, and at most one "seen again" comment per cause per
// machine per day. There is no daily cap on new reports.
async function sendDraft(draft, { root, machine, runtimeRepo, limit = true }, ports) {
  const fs = ports.fs ?? nativeFs, now = (ports.now ?? Date.now)(), api = github(ports), file = join(root, 'ledger.json');
  const ledger = readJson(fs, file, { filed: [], seen: {} });
  const destination = runtimeRepo ?? draft.runtimeRepo, repository = await ownerRepository(api, draft, destination);
  // An assignee only when the operator configured one for the Runtime repository that receives the report.
  const assignees = draft.kind === 'runtime' && repository === destination && LOGIN.test(String(draft.runtimeOwner ?? '')) ? [draft.runtimeOwner] : [];
  draft = { ...draft, repository, labels: [LABELS[draft.kind === 'runtime' ? 'runtime' : 'pdd']], assignees };
  const ref = number => `${draft.repository}#${number}`;
  const found = await findReport(api, draft, now);
  if (found) {
    if (now - (ledger.seen[draft.fingerprint] ?? -Infinity) < DAY) return { state: 'counted', number: found.number, id: found.id, ref: ref(found.number) };
    await api('POST', `repos/${draft.repository}/issues/${found.number}/comments`, { body: `Seen again on one more Autopilot machine run at ${new Date(now).toISOString()}.\n\n${reportMarker(draft.fingerprint)}` });
    ledger.seen[draft.fingerprint] = now; save(fs, file, ledger);
    return { state: 'seen', number: found.number, id: found.id, ref: ref(found.number) };
  }
  // A cause with no known code ("other-…") files at most one new report per machine per hour; the rest stay drafts.
  if (limit && /\.other-[0-9a-f]{8}\./.test(draft.fingerprint) && ledger.filed.some(row => /\.other-/.test(row.fingerprint) && now - row.at < DAY)) return { state: 'limit' };
  const { title, body } = publicReport(draft);
  const { value } = await api('POST', `repos/${draft.repository}/issues`, { title, body, labels: draft.labels, assignees: draft.assignees });
  ledger.filed = [...ledger.filed.filter(row => now - row.at < DAY), { fingerprint: draft.fingerprint, number: value.number, at: now }];
  save(fs, file, ledger);
  return { state: 'filed', number: value.number, id: value.id, ref: ref(value.number) };
}

function keepDraft(fs, root, draft, now) {
  const file = join(root, 'drafts', `${draft.fingerprint}.json`), old = readJson(fs, file, null);
  const kept = { ...draft, count: (old?.count ?? 0) + 1, firstAt: old?.firstAt ?? now, lastAt: now };
  save(fs, file, { ...kept, ...publicReport(kept) });
}

// The owner of a cause (Serhan's boundary): everything that goes INTO Runtime is PDD's (prompts, interface blocks,
// bindings, Stories, test vectors, tests, up to the call), so a refusal of our input (interface, binding, lint), a
// scenario value limit, a vector replay or a Runtime case is kind pdd. Kind runtime is only what happens inside Runtime
// after the call: no verdict, an interpreter error, server incompatibility, a server-side internal error.
const PDD_OWNED = /scenario|vector|replay|safe-integer|integer-out-of-range|runtime-case|test-case/;
export function reportKind(cause) {
  if (cause?.kind !== 'runtime') return cause?.kind;
  return PDD_OWNED.test(`${slug(cause.component)} ${slug(cause.code)}`) || !RUNTIME_CODES.has(stableCode(cause.code)) ? 'pdd' : 'runtime';
}
// Stable fingerprints: an agent writes the code and the component as free text, so each is mapped to a fixed word.
const CODES = [['merge-check-tool', /^merge-check-tool$/], ['suite-broken', /^suite-broken$/], ['adopt-pdd', /^adopt-pdd$/], ['no-verdict', /verdict/], ['maintenance', /maintenance/],
  ['scenario-limit', /scenario|safe-integer|integer-out-of-range|out-of-range/], ['vector-replay', /vector|replay/], ['runtime-case', /runtime-case|test-case/],
  ['lint-refusal', /lint/], ['interface-refusal', /interface/], ['binding-refusal', /binding/], ['input-refusal', /refus|reject/], ['interpreter-error', /interpreter/],
  ['server-internal', /server-internal|internal-server|server-error|(?:^|-)5\d\d(?:-|$)|unavailable|bad-gateway/], ['server-incompatible', /server|compat/], ['crash', /crash|panic|segfault|exception/], ['claim-error', /claim/], ['not-run', /not-run/],
  ['base-check', /^base-check$/], ['step-quiet', /^step-quiet$/], ['stop-loop', /^stop-loop$/], ['timeout', /timeout|timed-out/], ['cli-error', /cli|command|usage|exit|failed|error/]];
// An unknown code is other-HASH of the step and the error class (the code slug with no digits) only, never of the
// agent's text, so one cause is one report; at most one new "other" report per machine per day.
export const stableCode = (code, step = '') => CODES.find(([, test]) => test.test(slug(code)))?.[0]
  ?? `other-${createHash('sha256').update(`${slug(step)}:${slug(code).replace(/\d+/g, '')}`).digest('hex').slice(0, 8)}`;
// Runtime kind is only what happens inside Runtime; every other cause (a refusal of our input, scenario limits, test
// vectors, the pdd command, the core) is a PDD report.
export const RUNTIME_CODES = new Set(['no-verdict', 'maintenance', 'interpreter-error', 'server-incompatible', 'server-internal']);
const COMPONENTS = [['autopilot-core', /autopilot|core/], ['pdd-lint', /lint/], ['pdd-approve', /approve/], ['pdd-workflow', /workflow/],
  ['pdd-test', /test|runtime|interpreter|verdict|scenario|vector/], ['pdd', /pdd/], ['agent', /agent|codex|claude/]];
export const stableComponent = component => COMPONENTS.find(([, test]) => test.test(slug(component)))?.[0] ?? 'other';
// File, count or keep one report for a Runtime or PDD cause. It never throws: a failed send keeps a local draft.
export async function fileReport({ cause, mode, root, machine, versions = {}, step, words = [], runtimeRepo = null, runtimeOwner = null }, ports = {}) {
  if (!['runtime', 'pdd'].includes(cause?.kind) || mode === 'off') return { state: 'off' };
  cause = { ...cause, kind: reportKind(cause), code: stableCode(cause.code, step), component: stableComponent(cause.component) };
  const fs = ports.fs ?? nativeFs, now = (ports.now ?? Date.now)(), draft = draftFor({ cause, versions, step, words, runtimeRepo, runtimeOwner });
  if (mode === 'file') {
    try {
      const sent = await sendDraft(draft, { root, machine, runtimeRepo }, ports);
      if (sent.state !== 'limit') return { ...sent, fingerprint: draft.fingerprint };
    } catch (error) { ports.warn?.(`Autopilot report kept as a local draft: ${error.message}`); }
  }
  keepDraft(fs, root, draft, now);
  return { state: 'draft', fingerprint: draft.fingerprint };
}

export function listReportDrafts({ root }, ports = {}) {
  const fs = ports.fs ?? nativeFs, folder = join(root, 'drafts');
  let names = [];
  try { names = fs.readdirSync(folder).filter(name => name.endsWith('.json')).sort(); } catch { return []; }
  return names.map(name => readJson(fs, join(folder, name), null)).filter(Boolean);
}

export async function sendReportDraft({ root, fingerprint, machine }, ports = {}) {
  const fs = ports.fs ?? nativeFs, file = join(root, 'drafts', `${fingerprint}.json`), draft = readJson(fs, file, null);
  if (!draft || draft.fingerprint !== fingerprint) return { exitCode: 1, message: `No local report draft ${fingerprint}. Run pdd autopilot report to list drafts.` };
  try {
    const sent = await sendDraft(draft, { root, machine, limit: false }, ports);
    fs.unlinkSync(file);
    return { exitCode: 0, message: `${sent.state === 'filed' ? 'Filed' : 'Counted on'} ${sent.ref}.` };
  } catch (error) { return { exitCode: 1, message: `Report not sent: ${error.message}. The draft stays.` }; }
}

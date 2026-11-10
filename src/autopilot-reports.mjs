// Generated from prompts/cli/autopilot-reports.prompt.md (sha256: a2a8f513dab59cca173b68e6cd53b08a10948d16728331e6975d7d2d5e6992aa).
import * as nativeFs from 'node:fs';
import { join } from 'node:path';
import { redactSecrets } from './secret-redaction.mjs';

export const REPORT_REPOSITORY = 'promptdriven/pdd';
export const RUNTIME_OWNER = 'agarwal-ishaan';
const DAY = 24 * 60 * 60 * 1000, RECENT = 14 * DAY, NEW_PER_DAY = 3, COUNT = '{{count}}';
const withCount = draft => ({ ...draft, body: draft.body.replace(COUNT, String(draft.count ?? 1)) });
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

function draftFor({ cause, versions, step, words }) {
  const fingerprint = reportFingerprint({ ...cause, version: versions.pdd });
  const kind = cause.kind === 'runtime' ? 'runtime' : 'pdd';
  const title = `Autopilot report: ${kind === 'runtime' ? 'Runtime' : 'PDD'} ${slug(cause.component) || 'unknown'} ${slug(cause.code) || 'unknown'} (PDD ${minor(versions.pdd)})`;
  const tail = safeTail(cause.detail || cause.text, words);
  const body = [cause.shipped ? 'Autopilot shipped one PR with "Runtime: not run" because Runtime could not check it. The job did not wait for a fix.'
    : `Autopilot ended one job because of a ${kind === 'runtime' ? 'Runtime' : 'PDD'} problem. The job did not wait for a fix.`, '',
    `- Kind: ${kind}`, `- Component: ${slug(cause.component) || 'unknown'}`, `- Error code: ${slug(cause.code) || 'unknown'}`, `- Step: ${slug(step) || 'unknown'}`,
    `- Versions: PDD ${versions.pdd ?? 'unknown'}, Node ${versions.node ?? 'unknown'}, ${versions.platform ?? 'unknown'}, agent ${versions.agent ?? 'unknown'}`, `- Seen on this machine: ${COUNT}`,
    '', 'Redacted detail (no repository code):', '', '```text', tail || '(none)', '```', '', reportMarker(fingerprint)].join('\n');
  return { fingerprint, repository: REPORT_REPOSITORY, title, body, labels: [LABELS[kind]], assignees: kind === 'runtime' ? [RUNTIME_OWNER] : [] };
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

// Send one report through the dedup rules. `limit` false is a person's explicit send.
async function sendDraft(draft, { root, machine, limit = true }, ports) {
  const fs = ports.fs ?? nativeFs, now = (ports.now ?? Date.now)(), api = github(ports), file = join(root, 'ledger.json');
  const ledger = readJson(fs, file, { filed: [], seen: {} });
  const ref = number => `${draft.repository}#${number}`;
  const found = await findReport(api, draft, now);
  if (found) {
    if (now - (ledger.seen[draft.fingerprint] ?? -Infinity) < DAY) return { state: 'counted', number: found.number, id: found.id, ref: ref(found.number) };
    await api('POST', `repos/${draft.repository}/issues/${found.number}/comments`, { body: `Seen again on machine ${slug(machine) || 'unknown'} at ${new Date(now).toISOString()}.\n\n${reportMarker(draft.fingerprint)}` });
    ledger.seen[draft.fingerprint] = now; save(fs, file, ledger);
    return { state: 'seen', number: found.number, id: found.id, ref: ref(found.number) };
  }
  if (limit && ledger.filed.filter(row => now - row.at < DAY).length >= NEW_PER_DAY) return { state: 'limit' };
  const { value } = await api('POST', `repos/${draft.repository}/issues`, { title: draft.title, body: withCount(draft).body, labels: draft.labels, assignees: draft.assignees });
  ledger.filed = [...ledger.filed.filter(row => now - row.at < DAY), { fingerprint: draft.fingerprint, number: value.number, at: now }];
  save(fs, file, ledger);
  return { state: 'filed', number: value.number, id: value.id, ref: ref(value.number) };
}

function keepDraft(fs, root, draft, now) {
  const file = join(root, 'drafts', `${draft.fingerprint}.json`), old = readJson(fs, file, null);
  save(fs, file, { ...draft, count: (old?.count ?? 0) + 1, firstAt: old?.firstAt ?? now, lastAt: now });
}

// The owner of a cause. Test vectors are PDD's: a Runtime case, a scenario value limit (for example a value that is not
// a safe integer) or a vector replay is kind pdd. Kind runtime is what goes in and out of Runtime: interface and binding
// refusals, interpreter errors, no verdict, server compatibility.
const PDD_OWNED = /scenario|vector|replay|safe-integer|integer-out-of-range|runtime-case|test-case/;
export function reportKind(cause) {
  return cause?.kind === 'runtime' && PDD_OWNED.test(`${slug(cause.component)} ${slug(cause.code)}`) ? 'pdd' : cause?.kind;
}
// File, count or keep one report for a Runtime or PDD cause. It never throws: a failed send keeps a local draft.
export async function fileReport({ cause, mode, root, machine, versions = {}, step, words = [] }, ports = {}) {
  if (!['runtime', 'pdd'].includes(cause?.kind) || mode === 'off') return { state: 'off' };
  cause = { ...cause, kind: reportKind(cause) };
  const fs = ports.fs ?? nativeFs, now = (ports.now ?? Date.now)(), draft = draftFor({ cause, versions, step, words });
  if (mode === 'file') {
    try {
      const sent = await sendDraft(draft, { root, machine }, ports);
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

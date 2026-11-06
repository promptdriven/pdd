// Generated from prompts/cli/metrics-store.prompt.md.
import * as fs from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { join } from 'node:path';

const EVENT = 'pdd.metrics.event.v1', BUNDLE = 'pdd.metrics.bundle.v1', DEFINITION = '1', SCOPE = 'all-retained-repo-events';
const types = new Set(['selection','launch','start','outcome','milestone','check','ci','delivery','report','assistance','coverage','step']);
const fields = new Set(['snapshotId','inScope','state','reasons','origin','decisionId','status','cliVersion','skillVersion','candidateVersion','requiredOutcome','stage','reason','pr','head','verdict','reviewer','checkerFamily','checkerMode','evidence','acceptance','classification','humanReported','explicit','complete','since','until','step','area','waitStage']);
const identifier = s => safe(s) && /^[A-Za-z0-9_.:@+-]+(?:\/[A-Za-z0-9_.:@+-]+)*$/.test(s);
const envelope = new Set(['schema','id','repo','issue','type','at','observedAt','source','attempt','data']);
const iso = s => typeof s === 'string' && /^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d(?:\.\d{1,3})?Z$/.test(s) && Number.isFinite(Date.parse(s));
const repo = s => typeof s === 'string' && /^[a-z0-9_.-]+\/[a-z0-9_.-]+$/.test(s);
const safe = s => typeof s === 'string' && s.length > 0 && s.length <= 512 && !/[\r\n\\]/.test(s) && !/(?:^|\s)(?:\/|~\/|[A-Za-z]:\\)/.test(s) && !/(?:token|password|secret|authorization)\s*[:=]/i.test(s);
const canonical = v => v === null || typeof v !== 'object' ? JSON.stringify(v) : Array.isArray(v) ? `[${v.map(canonical).join(',')}]` : `{${Object.keys(v).sort().map(k => `${JSON.stringify(k)}:${canonical(v[k])}`).join(',')}}`;
const hash = s => createHash('sha256').update(s).digest('hex');
function validateEvent(e) {
  if (!e || typeof e !== 'object' || Array.isArray(e) || Object.keys(e).some(k => !envelope.has(k)) || e.schema !== EVENT || (!identifier(e.id) || e.id.includes('/')) || !repo(e.repo) || !Number.isSafeInteger(e.issue) || e.issue < 1 || !types.has(e.type) || !iso(e.at) || !iso(e.observedAt) || !identifier(e.source) || (e.attempt != null && !identifier(e.attempt)) || !e.data || typeof e.data !== 'object' || Array.isArray(e.data)) throw Error('Invalid metrics event');
  for (const [k,v] of Object.entries(e.data)) {
    if (!fields.has(k)) throw Error(`Unsupported metrics field: ${k}`);
    if (v === null) continue;
    if (['inScope','humanReported','explicit','complete'].includes(k)) { if (typeof v !== 'boolean') throw Error('Invalid metrics fact'); }
    else if (k === 'pr') { if (!Number.isSafeInteger(v) || v < 1) throw Error('Invalid metrics fact'); }
    else if (k === 'reasons') { if (!Array.isArray(v) || !v.every(x => identifier(x) && !x.includes('/') || x === 'Selector observation unavailable')) throw Error('Invalid metrics fact'); }
    else if (k === 'since' || k === 'until') { if (!iso(v)) throw Error('Invalid metrics fact'); }
    else if (k === 'evidence') { try { const u = new URL(v); if (u.protocol !== 'https:' || u.username || u.password || u.search || /^(?:localhost|127\.|10\.|192\.168\.|169\.254\.|172\.(?:1[6-9]|2[0-9]|3[01])\.|\[::1\])/i.test(u.hostname) || (u.hash && !(u.hostname === 'github.com' && /^#(?:issuecomment|check-run)-[0-9]+$/.test(u.hash)))) throw Error(); } catch { throw Error('Evidence must be a public HTTPS link'); } }
    else if (k === 'reason' && e.type === 'ci' && safe(v) && v.length <= 100 && !/[\x00-\x1f\x7f]/.test(v)) {}
    else if (k === 'verdict' && v === 'NOT SURE') {}
    else if (k === 'reviewer' && /^[a-z]+ \(same-family; session identified in linked public comment\)$/.test(v)) {}
    else if (!identifier(v) || v.includes('/')) throw Error('Invalid metrics fact');
  }
  return e;
}
function validateEvents(events) { if (!Array.isArray(events)) throw Error('Invalid metrics events'); events.forEach(validateEvent); }
function unique(events) { const m = new Map(); for (const e of events) { const key = e.schema === EVENT ? canonical({...e, observedAt: null}) : canonical(e); const prior = m.get(key); if (!prior || (e.observedAt && e.observedAt < prior.observedAt)) m.set(key,e); } return [...m.entries()].sort(([a],[b]) => a.localeCompare(b)).map(([,e]) => e); }
async function location(root, ports) {
  if (ports?.commonDir) return join(await ports.commonDir(root), 'pdd', 'metrics');
  const result = spawnSync('git', ['rev-parse','--path-format=absolute','--git-common-dir'], {cwd:root, encoding:'utf8'});
  if (result.status !== 0) throw Error('Cannot resolve Git common directory');
  return join(result.stdout.trim(), 'pdd', 'metrics');
}
async function readNative(dir) {
  let names; try { names = await fs.readdir(join(dir,'transactions')); } catch (e) { if (e.code === 'ENOENT') return {events:[],sources:[],snapshots:[]}; throw e; }
  const events = [], sources = [], snapshots = [];
  for (const name of names.filter(n => /^[a-f0-9]{64}\.json$/.test(n)).sort()) {
    const text = await fs.readFile(join(dir,'transactions',name),'utf8');
    if (hash(text) !== name.slice(0,64)) throw Error('Corrupt metrics transaction');
    const batch = JSON.parse(text); validateEvents(batch.events); events.push(...batch.events); if (batch.source) sources.push(batch.source); if (batch.sources) sources.push(...batch.sources); if (batch.snapshots) { if (!Array.isArray(batch.snapshots)) throw Error('Corrupt metrics snapshots'); for (const snapshot of batch.snapshots) validateSnapshot(snapshot,snapshot.repo); snapshots.push(...batch.snapshots); }
  }
  return {events:unique(events),sources:unique(sources),snapshots:unique(snapshots)};
}
async function writeNative(dir, events, source, sources, snapshots) {
  if (!events.length && !source && !sources?.length && !snapshots?.length) return;
  const tx = join(dir,'transactions'); await fs.mkdir(tx,{recursive:true,mode:0o700});
  const text = canonical({events:unique(events),...(source ? {source} : {}),...(sources?.length ? {sources} : {}),...(snapshots?.length ? {snapshots:unique(snapshots)} : {})}); const dest = join(tx, `${hash(text)}.json`), temp = join(tx, `.tmp-${randomUUID()}`);
  const handle = await fs.open(temp,'wx',0o600);
  try { await handle.writeFile(text); await handle.sync(); } finally { await handle.close(); }
  try { await fs.link(temp,dest); } catch (e) { if (e.code !== 'EEXIST') throw e; } finally { await fs.unlink(temp); }
  const parent = await fs.open(tx,'r'); try { await parent.sync(); } finally { await parent.close(); }
}
export async function readEvents({root}, ports = {}) {
  if (ports.ledger) { const saved = await ports.ledger.read({root}); return {events:unique(saved.events),sources:unique(saved.sources ?? []),snapshots:unique(saved.snapshots ?? [])}; }
  return readNative(await location(root,ports));
}
export async function appendEvents({root,events}, ports = {}) {
  validateEvents(events);
  if (ports.ledger) { const saved = await ports.ledger.read({root}); const merged = unique([...saved.events,...events]); await ports.ledger.write({root,...saved,events:merged}); return {...saved,events:merged}; }
  const dir = await location(root,ports); await writeNative(dir,events); return readNative(dir);
}
async function identity(dir, ports) {
  await fs.mkdir(dir,{recursive:true,mode:0o700}); const file = join(dir,'installation.json');
  const value = {source:`install:${ports.uuid?.() ?? randomUUID()}`,captureStartedAt:(ports.now?.() ?? new Date().toISOString())};
  const temp = join(dir, `.identity-${randomUUID()}`); const f = await fs.open(temp,'wx',0o600);
  try { await f.writeFile(JSON.stringify(value)); await f.sync(); } finally { await f.close(); }
  try { await fs.link(temp,file); } catch (e) { if (e.code !== 'EEXIST') throw e; } finally { await fs.unlink(temp); }
  return JSON.parse(await fs.readFile(file,'utf8'));
}
function timezone(s) { try { new Intl.DateTimeFormat('en',{timeZone:s}); return typeof s === 'string' && !!s; } catch { return false; } }
function validateSource(s) {
  if (!s || Object.keys(s).some(k => !['source','captureStartedAt','coverage','cliVersion','definitionVersion','exportedAt','timezone','scope'].includes(k)) || (s.scope !== undefined && s.scope !== SCOPE) || !identifier(s.source) || !iso(s.captureStartedAt) || !identifier(s.cliVersion) || s.definitionVersion !== DEFINITION || !iso(s.exportedAt) || !timezone(s.timezone) || !s.coverage || Object.keys(s.coverage).some(k => !['since','until'].includes(k)) || !('since' in s.coverage) || !('until' in s.coverage) || ![s.coverage.since,s.coverage.until].every(x => x === null || iso(x))) throw Error('Invalid metrics source metadata');
}
function validateBundle(b) {
  if (!b || b.schema !== BUNDLE || b.definitionVersion !== DEFINITION) throw Error('Incompatible metrics bundle schema or definition');
  if ((b.scope !== undefined && b.scope !== SCOPE) || !repo(b.repo) || !iso(b.exportedAt) || !timezone(b.timezone) || !identifier(b.source) || !iso(b.captureStartedAt) || !identifier(b.cliVersion) || !b.coverage || typeof b.coverage !== 'object' || !('since' in b.coverage) || !('until' in b.coverage) || ![b.coverage.since,b.coverage.until].every(x => x === null || iso(x))) throw Error('Invalid metrics bundle metadata');
  if (Object.keys(b).some(k => !['schema','definitionVersion','repo','exportedAt','timezone','source','captureStartedAt','cliVersion','coverage','events','sources','snapshots','scope'].includes(k)) || Object.keys(b.coverage).some(k => !['since','until'].includes(k))) throw Error('Unsupported metrics bundle metadata');
  if (b.sources !== undefined) { if (!Array.isArray(b.sources)) throw Error('Invalid metrics sources'); b.sources.forEach(validateSource); }
  if (b.snapshots !== undefined) { if (!Array.isArray(b.snapshots)) throw Error('Invalid metrics snapshots'); b.snapshots.forEach(s => validateSnapshot(s,b.repo)); }
  validateEvents(b.events); if (b.events.some(e => e.repo !== b.repo)) throw Error('Metrics bundle repository mismatch');
}
function validateSnapshot(s, repository) {
  if (!s || Object.keys(s).some(k => !['snapshotId','repo','observedAt','source','events'].includes(k)) || !/^snapshot:[0-9a-f-]{36}$/i.test(s.snapshotId) || s.repo !== repository || !iso(s.observedAt) || !identifier(s.source) || !Array.isArray(s.events)) throw Error('Invalid metrics snapshot');
  validateEvents(s.events);
  if (new Set(s.events.map(e => e.issue)).size !== s.events.length || s.events.some(e => e.repo !== repository || e.type !== 'selection' || e.data.snapshotId !== s.snapshotId || e.source !== s.source || e.observedAt !== s.observedAt || e.at !== s.observedAt)) throw Error('Invalid metrics snapshot membership');
}
async function readSnapshots(dir, repository) {
  let names; try { names = await fs.readdir(join(dir,'snapshots')); } catch (e) { if (e.code === 'ENOENT') return []; throw e; }
  const snapshots = [];
  for (const name of names.filter(n => /^[0-9a-f-]{36}\.json$/i.test(n))) {
    const value = JSON.parse(await fs.readFile(join(dir,'snapshots',name),'utf8'));
    if (value.repo !== repository) continue;
    validateSnapshot(value,repository); if (`${value.snapshotId.slice(9)}.json` !== name) throw Error('Invalid snapshot identity');
    snapshots.push(value);
  }
  return snapshots;
}
export async function exportMetrics({root,metadata}, ports = {}) {
  const dir = await location(root,ports), installation = await identity(dir,ports);
  const saved = await readEvents({root},ports);
  const events = saved.events.filter(e => e.repo === metadata?.repo);
  const bundle = {schema:BUNDLE, definitionVersion:DEFINITION, scope:SCOPE, repo:metadata?.repo, exportedAt:metadata?.exportedAt ?? ports.now?.() ?? new Date().toISOString(), timezone:metadata?.timezone, source:installation.source, captureStartedAt:installation.captureStartedAt, cliVersion:metadata?.cliVersion ?? 'unknown', coverage:metadata?.coverage ?? {since:installation.captureStartedAt,until:null}, events, sources:unique(saved.sources ?? []), snapshots:unique([...(saved.snapshots ?? []).filter(s => s.repo === metadata?.repo),...await readSnapshots(dir,metadata?.repo)])};
  validateBundle(bundle); return bundle;
}
function sourceMetadata({source,captureStartedAt,coverage,cliVersion,definitionVersion,exportedAt,timezone,scope}) {
  return {source,captureStartedAt,coverage,cliVersion,definitionVersion,exportedAt,timezone,...(scope === undefined ? {} : {scope})};
}
export async function importMetrics({root,bundle}, ports = {}) {
  validateBundle(bundle);
  if (ports.ledger) { const saved = await ports.ledger.read({root}); const value = {events:unique([...saved.events,...bundle.events,...(bundle.snapshots ?? []).flatMap(s => s.events)]),sources:unique([...(saved.sources ?? []),...bundle.sources ?? [],sourceMetadata(bundle)]),snapshots:unique([...(saved.snapshots ?? []),...bundle.snapshots ?? []])}; await ports.ledger.write({root,...value}); return value; }
  const dir = await location(root,ports);
  await writeNative(dir,unique([...bundle.events,...(bundle.snapshots ?? []).flatMap(s => s.events)]),sourceMetadata(bundle),bundle.sources,bundle.snapshots);
  return readNative(dir);
}

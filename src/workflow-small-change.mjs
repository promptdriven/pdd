// Generated from prompts/cli/workflow-small-change.prompt.md.
import {closeSync, constants, fstatSync, ftruncateSync, lstatSync, openSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {sourceFingerprint} from './workflow-replay.mjs';

const CHECKLIST_FILE = 'small-change-checklist.json';
const SCHEMA_VERSION = 'pdd.small-change-checklist.v1';
const SOURCE_KIND = 'git-content-v1';
const SHA256_RE = /^[a-f0-9]{64}$/;
const MAX_BYTES = 1024 * 1024;
const NOFOLLOW = constants.O_NOFOLLOW ?? 0;

const text = value => typeof value === 'string' && value.trim().length > 0;
const object = value => value && typeof value === 'object' && !Array.isArray(value);
const sameRequest = (a, b) => ['request', 'source', 'quote'].every(key => a[key] === b[key]);
const validItem = item => object(item)
  && ['id', 'request', 'source', 'quote'].every(key => text(item[key]))
  && ['pending', 'done', 'excluded'].includes(item.state);
const validItems = items => Array.isArray(items) && items.length > 0
  && items.every(validItem) && new Set(items.map(item => item.id)).size === items.length;
const hasExactEnvelope = (doc, runId, sha256) => doc.schema_version === SCHEMA_VERSION
  && doc.run_id === runId && object(doc.source)
  && doc.source.kind === SOURCE_KIND && doc.source.sha256 === sha256;

// Read only a regular, size-bounded checklist file without following symlinks.
function readRegularChecklistText(runDir) {
  let fd;
  try {
    const path = join(runDir, CHECKLIST_FILE);
    if (!NOFOLLOW && lstatSync(path).isSymbolicLink()) return {status: 'malformed'};
    fd = openSync(path, constants.O_RDONLY | NOFOLLOW);
    const stat = fstatSync(fd);
    if (!stat.isFile() || stat.size > MAX_BYTES) return {status: 'malformed'};
    return {status: 'ok', content: readFileSync(fd, 'utf8')};
  } catch (error) {
    return {status: error?.code === 'ENOENT' ? 'missing' : 'malformed'};
  } finally {
    if (fd !== undefined) closeSync(fd);
  }
}

// Overwrite an existing regular checklist file in place without following symlinks.
function writeRegularChecklistRecord(runDir, record) {
  const pretty = `${JSON.stringify(record, null, 2)}\n`;
  const serialized = Buffer.byteLength(pretty, 'utf8') <= MAX_BYTES ? pretty : `${JSON.stringify(record)}\n`;
  if (Buffer.byteLength(serialized, 'utf8') > MAX_BYTES) throw new Error('Checklist exceeds 1 MiB limit');
  let fd;
  try {
    const path = join(runDir, CHECKLIST_FILE);
    if (!NOFOLLOW && lstatSync(path).isSymbolicLink()) throw new Error('Checklist path is a symlink');
    fd = openSync(path, constants.O_WRONLY | NOFOLLOW);
    if (!fstatSync(fd).isFile()) throw new Error('Checklist path is not a regular file');
    ftruncateSync(fd, 0);
    writeFileSync(fd, serialized, 'utf8');
    return {};
  } finally {
    if (fd !== undefined) closeSync(fd);
  }
}

function readChecklistInput(run, readPort) {
  if (!readPort) return readRegularChecklistText(run.runDir);
  try {
    const result = readPort({runDir: run.runDir});
    if (result?.content === null) return {status: 'missing'};
    if (typeof result?.content !== 'string' || Buffer.byteLength(result.content, 'utf8') > MAX_BYTES)
      return {status: 'malformed'};
    return {status: 'ok', content: result.content};
  } catch { return {status: 'malformed'}; }
}

// Requests come from the independent checker, not from the builder's plan.
export function reviewSmallChangeChecklist(checklist, requests) {
  const items = checklist?.items ?? [], findings = [];
  const add = (item, code) => findings.push({id: item.id, code});
  for (const item of items) {
    if (item.state === 'pending') add(item, 'pending-request');
    else if (item.state === 'done' && !text(item.evidence)) add(item, 'missing-evidence');
    else if (item.state === 'excluded' && (!text(item.exclusion?.reason) || !text(item.exclusion?.quote)
      || requests && !requests.some(request => sameRequest(item, request)
        && item.exclusion.quote === request.exclusion_quote))) add(item, 'unsupported-exclusion');
  }
  for (const request of requests ?? [])
    if (!items.some(item => sameRequest(item, request))) add(request, 'missing-request');
  return findings;
}

/** Read and validate a run's small-change checklist without mutating disk state. */
export function readSmallChangeChecklist(run) {
  const bad = status => ({status, items: [], mustFix: [{id: 'checklist', code: status}]});
  const file = readRegularChecklistText(run?.runDir);
  if (file.status !== 'ok') return bad(file.status);
  let doc;
  try { doc = JSON.parse(file.content); } catch { return bad('malformed'); }
  if (!object(doc) || !text(run?.runId) || doc.schema_version !== SCHEMA_VERSION || doc.run_id !== run.runId
    || !object(doc.source) || doc.source.kind !== SOURCE_KIND || !SHA256_RE.test(doc.source.sha256 ?? '')
    || !validItems(doc.items)) return bad('malformed');
  const current = sourceFingerprint(run.root);
  if (current === null || current !== doc.source.sha256) return bad('stale');
  return {status: 'recorded', items: doc.items, mustFix: reviewSmallChangeChecklist(doc)};
}

/** Auto-stamp the mechanical envelope of a small-change checklist on workflow done. */
export function stampSmallChangeChecklist(run, ports) {
  if (run?.workflow !== 'small-change') return {status: 'skipped', stamped: false, items: [], mustFix: []};
  const bad = status => ({status, stamped: false, items: [], mustFix: [{id: 'checklist', code: status}]});
  const file = readChecklistInput(run, ports?.checklist?.read);
  if (file.status !== 'ok') return bad(file.status);
  let doc;
  try { doc = JSON.parse(file.content); } catch { return bad('malformed'); }
  if (!object(doc) || !text(run.runId)
    || (doc.schema_version !== undefined && doc.schema_version !== null && doc.schema_version !== SCHEMA_VERSION)
    || !validItems(doc.items)) return bad('malformed');
  const fingerprintPort = ports?.source?.fingerprint ?? (({root}) => ({sha256: sourceFingerprint(root)}));
  let sha256;
  try { sha256 = fingerprintPort({root: run.root})?.sha256; } catch { sha256 = null; }
  if (typeof sha256 !== 'string' || !SHA256_RE.test(sha256)) return bad('stale');
  if (hasExactEnvelope(doc, run.runId, sha256))
    return {status: 'recorded', stamped: false, items: doc.items, mustFix: reviewSmallChangeChecklist(doc)};
  const record = {
    schema_version: SCHEMA_VERSION,
    run_id: run.runId,
    source: {kind: SOURCE_KIND, sha256},
    items: doc.items,
  };
  const writePort = ports?.checklist?.write ?? (({runDir, record: next}) => writeRegularChecklistRecord(runDir, next));
  try { writePort({runDir: run.runDir, record}); } catch { return bad('malformed'); }
  return {status: 'recorded', stamped: true, items: doc.items, mustFix: reviewSmallChangeChecklist(record)};
}

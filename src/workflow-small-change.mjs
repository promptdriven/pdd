// Generated from prompts/cli/workflow-small-change.prompt.md.
import {lstatSync, readFileSync} from 'node:fs';
import {join} from 'node:path';
import {sourceFingerprint} from './workflow-replay.mjs';

const text = value => typeof value === 'string' && value.trim().length > 0;
const object = value => value && typeof value === 'object' && !Array.isArray(value);
const sameRequest = (a, b) => ['request', 'source', 'quote'].every(key => a[key] === b[key]);

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

export function readSmallChangeChecklist(run) {
  const bad = status => ({status, items: [], mustFix: [{id: 'checklist', code: status}]});
  let doc;
  try {
    const path = join(run.runDir, 'small-change-checklist.json'), stat = lstatSync(path);
    if (!stat.isFile() || stat.size > 1024 * 1024) return bad('malformed');
    doc = JSON.parse(readFileSync(path, 'utf8'));
  } catch (error) { return bad(error.code === 'ENOENT' ? 'missing' : 'malformed'); }
  if (!object(doc) || doc.schema_version !== 'pdd.small-change-checklist.v1' || doc.run_id !== run.runId
    || !object(doc.source) || doc.source.kind !== 'git-content-v1' || !/^[a-f0-9]{64}$/.test(doc.source.sha256 ?? '')
    || !Array.isArray(doc.items) || !doc.items.length || doc.items.some(item => !object(item)
      || !['id','request','source','quote'].every(key => text(item[key])) || !['pending','done','excluded'].includes(item.state))
    || new Set(doc.items.map(item => item.id)).size !== doc.items.length) return bad('malformed');
  const current = sourceFingerprint(run.root);
  if (current === null || current !== doc.source.sha256) return bad('stale');
  return {status: 'recorded', items: doc.items, mustFix: reviewSmallChangeChecklist(doc)};
}

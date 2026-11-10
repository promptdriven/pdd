// Generated from prompts/cli/issue-mixed.prompt.md (sha256: 8ef1b1cd3ec2d2ec426362839cbaedb2bcb8dbf91918e95f276d2a0266cf2e5c).
import { resolveAreas } from './autopilot-areas.mjs';
import { currentSortIssue } from './issue-sort-github.mjs';
const parse = x => typeof x === 'string' ? JSON.parse(x) : x;
const url = x => typeof x === 'string' && /^https:\/\/github\.com\/[\w.-]+\/[\w.-]+\/issues\/[1-9]\d*$/.test(x);
const requirement = body => (body ?? '').replace(/```[\s\S]*?```/g, '').split('\n').filter(x => !/^\s*>/.test(x)).join('\n');
export async function readOwnerChoice({ labels = [], comments = [], timeline = [] }, authorityFor) {
  const active = labels.filter(x => ['pdd:owner-whole','pdd:owner-split'].includes(x));
  if (active.length > 1) return 'conflict';
  if (active.length) {
    const event = timeline.filter(x => ['labeled','unlabeled'].includes(x.event) && x.label?.name === active[0]).at(-1);
    if (!event || event.event !== 'labeled' || (await authorityFor(event.actor?.login ?? '')).authority !== 'trusted') return 'conflict';
    return active[0].slice(10);
  }
  let mode = '';
  for (const c of comments) {
    if (/<!--\s*pdd/.test(c.body ?? '') || (await authorityFor(c.user?.login ?? '')).authority !== 'trusted') continue;
    const choices = [...requirement(c.body).matchAll(/^\s*(?:pdd:owner-(whole|split)|(?:mixed|owner)\s*:\s*(whole|split)|(?:(whole) issue|(split) this issue))[.!]?\s*$/gim)].map(x => x.slice(1).find(Boolean).toLowerCase());
    if (choices.length) mode = new Set(choices).size === 1 ? choices[0] : 'conflict';
  }
  return mode;
}
export function partIdentity(body = '') {
  try { const p = JSON.parse(/<!-- pdd-issue-part:v1 (.*?) -->/.exec(body)?.[1]); return url(p.parent) && typeof p.area === 'string' && p.area.trim() ? p : null; } catch { return null; }
}
export function readSplitComment(c, authority) {
  if (authority !== 'trusted' || !c.created_at || c.created_at !== c.updated_at) return null;
  try {
    const r = JSON.parse(/<!-- pdd-issue-split:v1 (.*?) -->/.exec(c.body)?.[1]);
    return r.parts?.length === 2 && r.parts.every(p => url(p.issue) && typeof p.area === 'string' && p.area.trim()) && new Set(r.parts.map(p => p.issue)).size === 2 && new Set(r.parts.map(p => p.area)).size === 2 && r.parts.some(p => p.area === r.first) ? r : null;
  } catch { return null; }
}
export function resolveMixed({ snapshot, issue, record }) {
  const parts = resolveAreas({ ...snapshot.sortContext, evidence: { paths: record.paths, keywords: [issue.title, issue.sortText ?? ''], labels: issue.labels ?? [], repository: record.belongs.repository, area: record.belongs.area } });
  if (parts.length <= 1 && (record.touchedAreas?.length ?? 0) <= 1 && !issue.sortOwnerChoice) return null;
  const question = { action: 'question', area: parts.map(x => x.area).join(','), owner: '', reason: 'needs-owner', parts };
  if (!parts.length || record.belongs.kind === 'unknown' || parts.length !== record.touchedAreas?.length || parts.some(p => !record.touchedAreas.some(x => x.area === p.area))) return question;
  const external = parts.filter(p => p.owner !== 'autopilot');
  if (!external.length) return null;
  const defaults = external.map(p => snapshot.sortContext.areas?.find(a => a.name === p.area)?.mixed ?? (snapshot.repository.toLowerCase() === 'promptdriven/pdd' && p.area === 'runtime' ? 'whole' : ''));
  const mode = issue.sortOwnerChoice || (new Set(defaults).size === 1 ? defaults[0] : '');
  if (new Set(external.map(x => x.owner)).size !== 1 || external[0].owner.startsWith('repo:')) return question;
  if (mode === 'whole') return { ...question, action: 'assign', owner: external[0].owner, reason: 'mixed-whole' };
  if (mode !== 'split' || parts.length !== 2 || !parts.some(p => p.owner === 'autopilot') || !parts.some(p => p.area === record.splitOrder?.first)) return question;
  return { ...question, action: 'split', reason: 'mixed-split' };
}
async function pages(ports, repository, issue, kind) {
  const items = [], seen = new Set(); let cursor = '';
  do {
    if (seen.has(cursor)) throw Error('sort-write-pending'); seen.add(cursor);
    const p = parse((await ports.github.page({ repository, issue, kind, cursor })).json);
    if (p.error || !Array.isArray(p.items) || typeof p.next !== 'string') throw Error('sort-write-pending');
    items.push(...p.items); cursor = p.next;
  } while (cursor);
  return items;
}
async function unownedParent({ repository, snapshot, route }, ports) {
  const subject = snapshot.issues.find(x => x.key === route.issue);
  const owners = parse((await ports.owners.read({ repository, issues: [route.issue] })).json);
  const raw = parse((await ports.github.issue({ repository, issue: Number(route.issue.split('/').pop()) })).json);
  const labels = Array.isArray(raw.labels) ? raw.labels.map(x => typeof x === 'string' ? x : x.name) : null;
  if (raw.state !== 'open' || !Array.isArray(raw.assignees) || raw.assignees.length || !Array.isArray(owners.claims) || owners.claims.some(x => x.issue === route.issue && x.active) || !labels || labels.includes('pdd:working')) return null;
  if (raw.title !== subject.title || raw.body !== subject.sortText || JSON.stringify(labels.slice().sort()) !== JSON.stringify(subject.labels.slice().sort())) return null;
  return raw;
}
export async function currentSplitParent({ repository, snapshot, route }, ports, complete = false) {
  const subject = snapshot.issues.find(x => x.key === route.issue);
  const currentParent = () => unownedParent({ repository, snapshot, route }, ports);
  const raw = await currentParent();
  if (!raw) return false;
  const labels = raw.labels?.map(x => typeof x === 'string' ? x : x.name);
  const authorityFor = author => ports.authority.read({ repository, author });
  const comments = await pages(ports, repository, raw.number, 'comments');
  const timeline = await pages(ports, repository, raw.number, 'timeline');
  if (timeline.some(x => x.event === 'cross-referenced' && x.source?.issue?.pull_request && x.source.issue.state === 'open')) return false;
  if (await readOwnerChoice({ labels, comments, timeline }, authorityFor) !== subject.sortOwnerChoice) return false;
  const notes = [];
  for (const c of comments) { const split = readSplitComment(c, (await authorityFor(c.user?.login ?? '')).authority); if (split) notes.push(split); }
  if (!notes.length || notes.some(x => JSON.stringify(x) !== JSON.stringify(subject.sortSplit))) return false;
  if (complete) for (const p of subject.sortSplit.parts) {
    const child = parse((await ports.github.issue({ repository, issue: Number(p.issue.split('/').pop()) })).json);
    if (child.state !== 'closed' || child.state_reason !== 'completed' || (await authorityFor(child.user?.login ?? '')).authority !== 'trusted') return false;
  }
  // Child and trust reads can outlive the first ownership observation. Keep
  // this reread inside the guard that native admission calls before transport.
  return !!await currentParent();
}
export async function syncMixedParts({ cwd = '', repository, snapshot, mode }, ports, write) {
  if (mode !== 'auto' || !snapshot.complete) return;
  // Import through the existing owner avoids a second decision implementation.
  const { sortPlan } = await import('./issue-sort.mjs');
  let count = 0;
  for (const route of sortPlan({ snapshot }).routes.filter(x => x.action === 'split')) {
    if (++count > 10) break;
    const parent = Number(route.issue.split('/').pop());
    const guard = async () => (await ports.settings.read({ cwd, repository })).mode === mode && await currentSortIssue({ cwd, repository, snapshot, route }, ports);
    const effect = action => write(async () => { if (!await guard()) throw Error('sort-owner-changed'); return action(); });
    if (!await guard()) continue;
    const children = [];
    for (const part of route.parts) {
      const marker = `<!-- pdd-issue-part:v1 ${JSON.stringify({ parent: route.issue, area: part.area })} -->`;
      const recover = async () => {
        const found = [];
        for (const raw of await pages(ports, repository, 0, 'splitCandidates')) if (raw.body?.includes(marker) && (await ports.authority.read({ repository, author: raw.user?.login ?? '' })).authority === 'trusted') found.push(raw);
        if (found.length > 1) throw Error('sort-write-pending');
        return found[0];
      };
      let raw = await recover();
      if (!raw) {
        if (!ports.github.createSortPart || !ports.github.withSortGroupAdmission) throw Error('sort-write-unavailable');
        raw = await ports.github.withSortGroupAdmission({ repository, rootCause: `split-${parent}-${Buffer.from(part.area).toString('hex')}`, write }, async () => {
          const found = await recover(); if (found) return found;
          const body = `Part of ${route.issue}\nArea: ${part.area}\n${route.record.touchedAreas.find(x => x.area === part.area).evidence.join('\n')}\n\n${marker}`;
          let attempted = false;
          try {
            return parse((await effect(() => { attempted = true; return ports.github.createSortPart({ repository, title: `${part.area} part of #${parent}`, body, checkOwnership: guard }); })).json);
          } catch (error) {
            // Only proven unsent failures permit release. Lost replies and failed
            // readback retain admission, even across fresh coordinators.
            if (!attempted || error.sortUnsent === true) return '';
            throw error;
          }
        });
        if (!raw) throw Error('sort-write-pending');
      }
      if (!raw.html_url?.startsWith(`https://github.com/${repository}/issues/`) || !/^[1-9]\d*$/.test(String(raw.id)) || !Number.isSafeInteger(raw.number) || raw.html_url !== `https://github.com/${repository}/issues/${raw.number}`) throw Error('sort-write-pending');
      children.push({ raw, area: part.area, owner: part.owner });
    }
    const childGuard = async (endpoints, state = 'link') => {
      if (!await guard()) return false;
      // Evidence and every child claim read precede final issue observations.
      // Ordering links must observe both children as one admission decision.
      for (const child of endpoints) {
        const owners = parse((await ports.owners.read({ repository, issues: [child.raw.html_url] })).json);
        if (!Array.isArray(owners.claims) || owners.claims.some(x => x.issue === child.raw.html_url && x.active)) return false;
      }
      for (const child of endpoints) {
        const raw = parse((await ports.github.issue({ repository, issue: child.raw.number })).json);
        const completed = raw.state === 'closed' && raw.state_reason === 'completed';
        const allowedState = state === 'completed' ? completed : raw.state === 'open' || state === 'link' && completed;
        if (!allowedState || !Array.isArray(raw.assignees) || raw.assignees.length || !Array.isArray(raw.labels) || raw.labels.some(x => (x.name ?? x) === 'pdd:working')) return false;
      }
      // Child observations may introduce parent ownership. Do not reread slow
      // sort evidence here; check the parent directly after the child reads.
      return !!await unownedParent({ repository, snapshot, route }, ports);
    };
    const link = async (issue, childId, kind, checkOwnership) => {
      const result = await effect(() => ports.github.ensureSortLink({ repository, issue, childId: String(childId), kind, checkOwnership }));
      if (result.ok !== true) throw Error('sort-write-pending');
    };
    for (const child of children) {
      const parentGuard = () => childGuard([child]);
      await link(parent, child.raw.id, 'sub', parentGuard);
      await link(parent, child.raw.id, 'blocker', parentGuard);
    }
    const first = children.find(x => x.area === route.record.splitOrder.first), later = children.find(x => x !== first);
    await link(later.raw.number, first.raw.id, 'blocker', () => childGuard([later, first]));
    for (const child of children.filter(x => x.owner !== 'autopilot')) {
      const raw = parse((await ports.github.issue({ repository, issue: child.raw.number })).json);
      if (raw.assignees?.length === 1 && raw.assignees[0].login === child.owner) continue;
      if (raw.state === 'closed' && raw.state_reason === 'completed') {
        if (!await childGuard([child], 'completed')) throw Error('sort-owner-changed');
        continue;
      }
      const result = await effect(async () => {
        if (!await childGuard([child], 'open')) throw Error('sort-owner-changed');
        return ports.github.sortUpdate({ repository, issue: child.raw.number, assignee: child.owner, checkOwnership: () => childGuard([child], 'open') });
      });
      if (result.ok !== true) throw Error('sort-write-pending');
    }
    const split = { parts: children.map(x => ({ issue: x.raw.html_url, area: x.area })), first: first.area };
    const body = `Parts of #${parent}:\n${split.parts.map(x => `${x.area}: ${x.issue}`).join('\n')}\n\n<!-- pdd-issue-route:v1 -->\n<!-- pdd-issue-split:v1 ${JSON.stringify(split)} -->`;
    const saved = parse((await effect(() => ports.github.appendComment({ repository, issue: parent, body, checkOwnership: guard }))).json);
    if (!saved.id) throw Error('sort-write-pending');
    snapshot.issues.find(x => x.key === route.issue).sortSplit = split;
  }
}

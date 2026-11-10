// Generated from prompts/cli/issue-sort.prompt.md (sha256: 01b35872eb8bf099b9f89fce12ebb45df09d8a2972e7f9e58dd4ab8d1848f61e).
import { resolveMixed } from './issue-mixed.mjs';
import { resolveArea, owningModule, canonicalModule, isRuntimeOwned } from './autopilot-areas.mjs';
const issueURL = x => typeof x === 'string' && /^https:\/\/github\.com\/[\w.-]+\/[\w.-]+\/issues\/[1-9]\d*$/i.test(x);
const text = x => typeof x === 'string';
const list = x => Array.isArray(x) && x.every(text);
const exact = (x, keys) => x && typeof x === 'object' && !Array.isArray(x) && Object.keys(x).sort().join() === keys.split(',').sort().join();
const fixLocator = value => /https:\/\/github\.com\/[\w.-]+\/[\w.-]+\/(?:pull\/[1-9]\d*|commit\/[a-f\d]{7,64})\b/i.test(value)
  || /\b[a-f\d]{7,64}\b/i.test(value) || /(?:^|[\s(`])(?:[\w.-]+\/)*[\w.-]+\.[a-z\d]+:[1-9]\d*\b/i.test(value);
const OPTIONAL_SORT_KEYS = new Set(['touchedAreas', 'splitOrder', 'owningModule', 'component', 'symbol', 'errorCode', 'route', 'duplicateOf', 'unify', 'reproduce']);
const MAX_GROUP_SIZE = 5;

function validReproduce(rep) {
  if (rep === undefined) return true;
  if (!rep || typeof rep !== 'object' || Array.isArray(rep) || typeof rep.confirmed !== 'boolean') return false;
  const allowed = ['confirmed', 'owningModule', 'symbol', 'component', 'errorCode', 'route', 'duplicateOf', 'summary'];
  return Object.keys(rep).every(k => allowed.includes(k))
    && allowed.filter(k => k !== 'confirmed').every(k => rep[k] === undefined || text(rep[k]));
}

export function validSort(record) {
  const r = record;
  return !!(exact(Object.fromEntries(Object.entries(r ?? {}).filter(([k]) => !OPTIONAL_SORT_KEYS.has(k))), 'schema_version,issue,base,inputs,belongs,status,genuine,paths,rootCause,severity,question')
    && (r.touchedAreas === undefined || Array.isArray(r.touchedAreas) && r.touchedAreas.length > 0 && r.touchedAreas.every(x => exact(x, 'area,evidence') && text(x.area) && x.area.trim() && list(x.evidence) && x.evidence.length && x.evidence.every(v => v.trim())) && new Set(r.touchedAreas.map(x => x.area)).size === r.touchedAreas.length)
    && (r.splitOrder === undefined || exact(r.splitOrder, 'first,evidence') && text(r.splitOrder.first) && r.splitOrder.first.trim() && list(r.splitOrder.evidence) && r.splitOrder.evidence.length && r.splitOrder.evidence.every(v => v.trim()))
    && ['owningModule', 'component', 'symbol', 'errorCode', 'route', 'unify'].every(k => r[k] === undefined || text(r[k]))
    && (r.duplicateOf === undefined || text(r.duplicateOf) && (!r.duplicateOf || issueURL(r.duplicateOf) || /^#?[1-9]\d*$/.test(r.duplicateOf)))
    && validReproduce(r.reproduce)
    && r.schema_version === 'pdd.issue-sort.v1' && issueURL(r.issue)
    && list(r.base) && new Set(r.base).size === r.base.length && Array.isArray(r.inputs) && r.inputs.length && r.inputs.every(x => exact(x, 'key,revision') && text(x.key) && x.key && text(x.revision) && x.revision) && new Set(r.inputs.map(x => x.key)).size === r.inputs.length
    && exact(r.belongs, 'kind,area,repository') && ['area','repository','old-code','unknown'].includes(r.belongs.kind) && text(r.belongs.area) && text(r.belongs.repository)
    && (r.belongs.kind !== 'repository' || /^[\w.-]+\/[\w.-]+$/.test(r.belongs.repository))
    && exact(r.status, 'state,release,fix,evidence') && ['still-happens','partly-fixed','fixed','unclear'].includes(r.status.state) && text(r.status.release) && r.status.release && text(r.status.fix) && (r.status.state !== 'fixed' || fixLocator(r.status.fix)) && list(r.status.evidence) && r.status.evidence.length && r.status.evidence.every(x => x.trim())
    && exact(r.genuine, 'kind,duplicateOf,reason') && ['bug','feature','docs','duplicate','not-genuine','unclear'].includes(r.genuine.kind) && text(r.genuine.reason) && text(r.genuine.duplicateOf)
    && (r.genuine.kind !== 'duplicate' || issueURL(r.genuine.duplicateOf) && r.genuine.duplicateOf !== r.issue)
    && (!['not-genuine'].includes(r.genuine.kind) && r.belongs.kind !== 'old-code' || r.genuine.reason.trim())
    && list(r.paths) && r.paths.every(x => x && !x.startsWith('/') && !x.split('/').includes('..')) && text(r.rootCause) && ['high','medium','low'].includes(r.severity) && text(r.question));
}

function normalizeIssueRef(ref, repository = '') {
  if (typeof ref !== 'string' || !ref.trim()) return '';
  const trimmed = ref.trim();
  if (/^#?[1-9]\d*$/.test(trimmed) && repository) return `https://github.com/${repository.toLowerCase()}/issues/${trimmed.replace(/^#/, '')}`;
  if (issueURL(trimmed)) return trimmed.toLowerCase();
  return '';
}

export function groupSignalsForRecord(record, repository = '') {
  if (!record || record.reproduce?.confirmed === false) return { owningModule: '', signals: [], primarySignal: '', duplicateOf: '', label: '' };
  const rep = record.reproduce;
  const mod = owningModule(rep?.owningModule ? { owningModule: rep.owningModule, paths: record.paths } : record);
  const dup = normalizeIssueRef(record.duplicateOf || (record.genuine?.kind === 'duplicate' ? record.genuine.duplicateOf : ''), repository);
  const signals = [];
  let primarySignal = '';
  const structured = [
    ['symbol', rep?.symbol ?? record.symbol],
    ['component', rep?.component ?? record.component],
    ['errorCode', rep?.errorCode ?? record.errorCode],
    ['route', rep?.route ?? record.route],
  ];
  if (mod) {
    for (const [kind, raw] of structured) {
      if (typeof raw === 'string' && raw.trim()) {
        const token = `${kind}:${raw.trim().toLowerCase()}`;
        signals.push(`${mod}#${token}`);
        if (!primarySignal) primarySignal = `${kind}:${raw.trim()}`;
      }
    }
  }
  const label = mod && primarySignal ? `${mod}:${primarySignal.split(':').slice(1).join(':')}` : dup ? `duplicate:${dup}` : '';
  return { owningModule: mod, signals, primarySignal, duplicateOf: dup, label };
}

export function chunkGroupMembers(items, maxSize = MAX_GROUP_SIZE) {
  if (!Array.isArray(items) || items.length < 2) return [];
  if (items.length <= maxSize) return [items.slice()];
  const chunks = [];
  for (let i = 0; i < items.length; i += maxSize) chunks.push(items.slice(i, i + maxSize));
  if (chunks.length >= 2 && chunks.at(-1).length === 1) {
    const moved = chunks.at(-2).pop();
    chunks.at(-1).unshift(moved);
  }
  return chunks;
}
export function sortInputs(snapshot, issue) {
  return [{ key: issue.key, revision: issue.revision }, ...(snapshot.inputs ?? []).filter(x => x.key === snapshot.sortContext?.key || x.key === `${issue.key}#sort-labels` || x.key.startsWith(`${issue.key}#issuecomment-`))];
}
export function sortCovered(snapshot, issue) {
  if (!snapshot.coverage) return snapshot.complete === true;
  const row = snapshot.coverage.issues?.find(x => x.key === issue.key);
  return snapshot.coverage.scope === true && !!row && ['issue','authority','comments','context','execution'].every(k => row[k] === true);
}
export const sortSourceKey = (repository, path) => `https://github.com/${repository.toLowerCase()}/blob/HEAD/${path.split('/').map(encodeURIComponent).join('/')}`;
export function selectedSort(snapshot, issue) {
  if (!issue || !sortCovered(snapshot, issue)) return null;
  const all = (issue.sorts ?? []).filter(x => x.authority !== 'outsider');
  const superseded = new Set(all.filter(x => x.authority === 'trusted' && x.intact && validSort(x.record)).flatMap(x => x.record.base));
  const heads = all.filter(x => !superseded.has(x.id));
  if (heads.length !== 1) return null;
  const head = heads[0], r = head.record;
  if ((snapshot.sortContext?.groups ?? []).some(g => g.merged && g.recheck?.some(x => x.issue === issue.key && x.heads.includes(head.id)))) return null;
  if (!head.intact || head.authority !== 'trusted' || !validSort(r) || r.issue !== issue.key || r.status.release !== snapshot.sortContext?.release) return null;
  const current = new Map([...snapshot.issues, ...snapshot.inputs].map(x => [x.key, x.revision]));
  if (r.paths.some(path => !r.inputs.some(x => x.key === sortSourceKey(snapshot.repository, path))) || r.inputs.some(x => current.get(x.key) !== x.revision) || sortInputs(snapshot, issue).some(x => !r.inputs.some(y => y.key === x.key && y.revision === x.revision))) return null;
  return r;
}
export function sortPlan({ snapshot }) {
  const queued = [], routes = [], groups = [];
  if (!snapshot.sortContext) return { queued, routes, groups };
  const prefix = `https://github.com/${snapshot.repository.toLowerCase()}/issues/`;
  for (const issue of snapshot.issues.filter(x => x.key.startsWith(prefix) && x.state === 'open' && x.authority === 'trusted')) {
    const record = selectedSort(snapshot, issue), route = { issue: issue.key, action: 'hold', area: '', owner: '', reason: '', record, umbrella: '', members: [], evidence: record?.status.evidence ?? [] };
    routes.push(route);
    const live = issue.execution !== 'idle' || issue.sortOpenPr === true || issue.holds.some(x => /claim/i.test(x) && !/^Expired claim\b/.test(x));
    if (!Array.isArray(issue.assignees) || issue.assignees.length) { route.reason = 'owned'; continue; }
    if (issue.sortSplit) {
      route.record = record ?? issue.sorts?.find(x => x.authority === 'trusted' && x.intact && x.record)?.record ?? null;
      route.reason = 'split-parts';
      const done = issue.sortSplit.parts.every(p => snapshot.issues.some(x => x.key === p.issue && x.authority === 'trusted' && x.state === 'completed' && x.sortCompleted === true && sortCovered(snapshot, x)));
      route.action = done && !live ? 'close' : 'hold';
      if (done) route.evidence = issue.sortSplit.parts.map(p => `${p.area}: ${p.issue} completed`);
      if (issue.sortOwnerChoice === 'whole' || issue.sortOwnerChoice === 'conflict') { route.action = live ? 'hold' : 'question'; route.reason = 'needs-owner'; }
      continue;
    }
    if (issue.sortPart) {
      const parent = snapshot.issues.find(x => x.key === issue.sortPart.parent);
      if (!parent?.sortSplit?.parts.some(x => x.issue === issue.key && x.area === issue.sortPart.area)) { route.reason = 'split-pending'; continue; }
    }
    if (!record) { if (!live) queued.push(issue.key); route.reason = 'sort-required'; continue; }
    if (live) route.reason = 'owned';
    const dupTarget = normalizeIssueRef(record.duplicateOf || (record.genuine.kind === 'duplicate' ? record.genuine.duplicateOf : ''), snapshot.repository);
    const openTarget = dupTarget && dupTarget !== issue.key
      ? snapshot.issues.find(x => x.key === dupTarget && x.state === 'open' && x.authority === 'trusted' && Array.isArray(x.assignees) && !x.assignees.length)
      : null;
    const openTargetRecord = openTarget ? selectedSort(snapshot, openTarget) : null;
    const joinsOpenDuplicate = Boolean(openTarget && openTargetRecord && openTargetRecord.status.state !== 'fixed' && openTargetRecord.belongs.kind !== 'old-code' && openTargetRecord.genuine.kind !== 'not-genuine');
    if (record.status.state === 'fixed' || record.belongs.kind === 'old-code' || record.genuine.kind === 'not-genuine' || (record.genuine.kind === 'duplicate' && !joinsOpenDuplicate)) {
      route.action = live ? 'hold' : 'close'; route.reason = record.belongs.kind === 'old-code' ? 'old-code' : record.genuine.kind === 'duplicate' ? 'duplicate' : record.status.state === 'fixed' ? 'fixed' : 'not-genuine'; continue;
    }
    const mixed = resolveMixed({ snapshot, issue, record });
    if (mixed) { Object.assign(route, mixed); if (live) { route.action = 'hold'; route.reason = 'owned'; } continue; }
    const area = resolveArea({ ...snapshot.sortContext, evidence: { paths: record.paths, keywords: [issue.title, issue.sortText ?? ''], labels: issue.labels ?? [], repository: record.belongs.kind === 'repository' ? record.belongs.repository : '', area: record.belongs.area } });
    Object.assign(route, { area: area.area, owner: area.owner });
    if (record.belongs.kind === 'unknown' || area.state === 'unsure') { route.action = live ? 'hold' : 'question'; route.reason = 'needs-owner'; continue; }
    if (record.belongs.kind === 'repository' && area.owner === 'autopilot') { route.action = live ? 'hold' : 'link'; route.owner = `repo:${record.belongs.repository}`; route.reason = 'another-repository'; continue; }
    if (area.owner !== 'autopilot') { route.action = live ? 'hold' : area.owner.startsWith('repo:') ? 'link' : 'assign'; route.reason = 'another-owner'; continue; }
    if (record.question || record.status.state === 'unclear' || record.genuine.kind === 'unclear') { route.action = live ? 'hold' : 'question'; route.reason = 'needs-answer'; continue; }
    route.action = live ? 'hold' : 'work'; route.reason = live ? 'owned' : 'local';
  }
  const assigned = key => {
    const issue = snapshot.issues.find(x => x.key === key);
    return !issue ? false : (!Array.isArray(issue.assignees) || issue.assignees.length > 0);
  };
  const runtimeOwned = key => {
    const issue = snapshot.issues.find(x => x.key === key);
    const route = routes.find(x => x.issue === key);
    const record = route?.record ?? (issue ? selectedSort(snapshot, issue) : null);
    return isRuntimeOwned({ issue, record, resolved: route ? { area: route.area, owner: route.owner } : undefined });
  };
  const excluded = key => assigned(key) || runtimeOwned(key);
  const saved = (snapshot.sortContext.groups ?? []).map(group => {
    const splitOut = Array.isArray(group.splitOut) ? group.splitOut : [];
    const members = (group.members ?? []).filter(key => !excluded(key) && !splitOut.includes(key));
    const umbrella = excluded(group.umbrella) || splitOut.includes(group.umbrella) ? '' : group.umbrella;
    return { ...group, members, umbrella, ...(splitOut.length ? { splitOut } : {}) };
  });
  const umbrellaKeys = new Set(saved.filter(x => !x.merged && x.umbrella && !x.members.includes(x.umbrella)).map(x => x.umbrella));
  const synthetic = issue => /<!-- pdd-issue-group:v1 ([a-z\d]+(?:-[a-z\d]+)*) -->/.test(issue?.sortText ?? '');
  const splitPairs = new Set();
  for (const old of saved.filter(x => !x.merged && Array.isArray(x.splitOut))) {
    for (const s of old.splitOut) {
      for (const m of [old.umbrella, ...old.members].filter(Boolean)) {
        splitPairs.add(`${s}\n${m}`);
        splitPairs.add(`${m}\n${s}`);
      }
    }
  }
  const candidateMap = new Map();
  for (const route of routes) {
    const issue = snapshot.issues.find(i => i.key === route.issue);
    if (route.action === 'work' && !issue?.sortPart && !umbrellaKeys.has(route.issue) && !synthetic(issue) && !excluded(route.issue) && route.record?.reproduce?.confirmed !== false) {
      candidateMap.set(route.issue, { route, info: groupSignalsForRecord(route.record, snapshot.repository), oldGroup: null });
    }
  }
  for (const old of saved.filter(x => !x.merged)) {
    const leaderOwned = Boolean(old.umbrella && routes.find(x => x.issue === old.umbrella)?.reason === 'owned');
    for (const key of old.members) {
      if (excluded(key) || old.splitOut?.includes(key)) continue;
      const route = routes.find(x => x.issue === key);
      if (!route || route.record?.reproduce?.confirmed === false) continue;
      const info = route.record ? groupSignalsForRecord(route.record, snapshot.repository) : { owningModule: old.owningModule ?? '', signals: old.signal ? [`${old.owningModule ? `${old.owningModule}#` : ''}${old.signal.toLowerCase()}`] : [], primarySignal: old.signal ?? '', duplicateOf: '', label: old.rootCause ?? '' };
      const matchesOld = !route.record || (old.owningModule && info.owningModule === old.owningModule && (!old.signal || info.signals.includes(`${old.owningModule}#${old.signal.toLowerCase()}`)))
        || (old.signal?.startsWith('duplicate:') && (info.duplicateOf && info.signals.includes(`dup:${info.duplicateOf}`) || key === normalizeIssueRef(old.signal.slice('duplicate:'.length), snapshot.repository)));
      const retainedWork = (key === old.umbrella || leaderOwned) && route.reason === 'owned' && matchesOld;
      if ((!route.record || retainedWork) && !candidateMap.has(key)) {
        candidateMap.set(key, { route, info, oldGroup: old });
      } else if (candidateMap.has(key) && matchesOld && !candidateMap.get(key).oldGroup) {
        candidateMap.get(key).oldGroup = old;
      }
    }
  }
  const candidates = [...candidateMap.values()];
  for (const item of candidates) {
    const dup = item.info.duplicateOf;
    if (dup && candidateMap.has(dup) && !splitPairs.has(`${item.route.issue}\n${dup}`)) {
      const target = candidateMap.get(dup);
      const token = `dup:${dup}`;
      if (!item.info.signals.includes(token)) item.info.signals.push(token);
      if (!target.info.signals.includes(token)) target.info.signals.push(token);
    }
    if (item.oldGroup && !item.route.record) {
      for (const peerKey of item.oldGroup.members) {
        const peer = candidateMap.get(peerKey);
        if (peer && peer !== item && peer.info.signals.length) {
          for (const sig of peer.info.signals) if (!item.info.signals.includes(sig)) item.info.signals.push(sig);
        }
      }
    }
  }
  const groupable = candidates.filter(x => x.info.signals.length > 0);
  const parent = new Map(groupable.map(x => [x.route.issue, x.route.issue]));
  const find = k => { let p = parent.get(k); while (p !== parent.get(p)) p = parent.get(p); parent.set(k, p); return p; };
  const union = (a, b) => { const ra = find(a), rb = find(b); if (ra !== rb) parent.set(rb, ra); };
  for (let i = 0; i < groupable.length; i++) {
    for (let j = i + 1; j < groupable.length; j++) {
      const a = groupable[i], b = groupable[j];
      if (splitPairs.has(`${a.route.issue}\n${b.route.issue}`)) continue;
      if (a.info.signals.some(s => b.info.signals.includes(s))) union(a.route.issue, b.route.issue);
    }
  }
  const clusters = new Map();
  for (const item of groupable) {
    const root = find(item.route.issue);
    if (!clusters.has(root)) clusters.set(root, []);
    clusters.get(root).push(item);
  }
  const handledOld = new Set();
  for (const items of clusters.values()) {
    items.sort((a, b) => Number(a.route.issue.split('/').pop()) - Number(b.route.issue.split('/').pop()));
    const chunks = chunkGroupMembers(items, MAX_GROUP_SIZE);
    for (const chunk of chunks) {
      const members = chunk.map(x => x.route);
      const keys = members.map(x => x.issue);
      const area = [...new Set(members.map(x => x.area).filter(Boolean))].sort().join(',');
      const firstInfo = chunk.find(x => x.info.owningModule || x.info.primarySignal || x.info.label)?.info ?? chunk[0].info;
      const old = saved.find(x => !x.merged && !handledOld.has(x) && x.members.some(m => keys.includes(m)));
      if (old) handledOld.add(old);
      const rootCause = old?.rootCause || firstInfo.label || (firstInfo.owningModule && firstInfo.primarySignal ? `${firstInfo.owningModule}:${firstInfo.primarySignal.split(':').slice(1).join(':')}` : `group-${keys[0].split('/').pop()}`);
      const commonSignals = chunk.map(x => x.info.signals).reduce((common, signals) => common.filter(signal => signals.includes(signal)), chunk[0].info.signals.slice());
      const commonSignal = commonSignals.sort()[0] ?? '';
      const commonModule = chunk.every(x => x.info.owningModule && x.info.owningModule === firstInfo.owningModule) ? firstInfo.owningModule : '';
      const groupSignal = commonSignal.startsWith('dup:') ? `duplicate:${commonSignal.slice(4)}` : commonSignal.includes('#') ? commonSignal.slice(commonSignal.indexOf('#') + 1) : '';
      const legacyLeaderLive = Boolean(old?.umbrella && !old.members.includes(old.umbrella)
        && routes.find(x => x.issue === old.umbrella)?.reason === 'owned');
      const dedicatedSavedUmbrella = legacyLeaderLive ? old.umbrella : '';
      const occupiedLeader = old?.umbrella && keys.includes(old.umbrella) && routes.find(x => x.issue === old.umbrella)?.reason === 'owned' ? old.umbrella : '';
      const umbrella = dedicatedSavedUmbrella || occupiedLeader || keys[0];
      const groupObj = {
        area,
        rootCause,
        umbrella,
        members: keys,
        notified: old?.notified ?? old?.members ?? keys,
        ...(commonModule ? { owningModule: commonModule } : {}),
        ...(groupSignal ? { signal: groupSignal } : {}),
        ...(old?.splitOut?.length ? { splitOut: old.splitOut } : {}),
        ...(old?.reproduced ? { reproduced: true } : {}),
      };
      groups.push(groupObj);
      for (const member of members) Object.assign(member, { umbrella, members: keys });
      const umbrellaRoute = routes.find(x => x.issue === umbrella);
      if (umbrellaRoute) Object.assign(umbrellaRoute, { umbrella, members: keys });
    }
  }
  for (const old of saved.filter(x => !x.merged && !handledOld.has(x) && x.umbrella && !x.members.includes(x.umbrella))) {
    const umbrellaRoute = routes.find(x => x.issue === old.umbrella);
    // Keep a live pre-contract leader bound to its existing members.
    if (umbrellaRoute?.reason === 'owned') {
      groups.push({ ...old });
      Object.assign(umbrellaRoute, { umbrella: old.umbrella, members: old.members });
      for (const key of old.members) {
        const memberRoute = routes.find(x => x.issue === key);
        if (memberRoute) Object.assign(memberRoute, { umbrella: old.umbrella, members: old.members });
      }
    }
  }
  for (const route of routes) if (route.action === 'work' && umbrellaKeys.has(route.issue) && !groups.some(g => g.umbrella === route.issue)) { route.action = 'hold'; route.reason = 'legacy-group-umbrella'; }
  for (const route of routes) if (route.action === 'work' && synthetic(snapshot.issues.find(x => x.key === route.issue)) && !groups.some(g => g.umbrella === route.issue)) { route.action = 'hold'; route.reason = 'orphan-group-umbrella'; }
  // Keep the merge boundary until all previous heads have been superseded.
  for (const group of saved.filter(x => x.merged)) groups.push(group);
  return { queued, routes, groups };
}

export function confirmGroupAfterReproduce({ group, reproduceResults = {} }) {
  if (!group || !Array.isArray(group.members)) {
    return { confirmed: false, umbrella: '', members: [], splitOut: [], reasons: {}, group: null };
  }
  const repository = String(group.members[0] ?? '').match(/^https:\/\/github\.com\/([^/]+\/[^/]+)\/issues\//i)?.[1] ?? '';
  const issueKey = value => normalizeIssueRef(value, repository).toLowerCase();
  const byIssue = new Map();
  if (Array.isArray(reproduceResults)) {
    for (const entry of reproduceResults) {
      const key = issueKey(entry?.issue);
      if (key) byIssue.set(key, entry);
    }
  } else if (reproduceResults && typeof reproduceResults === 'object') {
    for (const [key, value] of Object.entries(reproduceResults)) {
      const normalized = issueKey(key);
      if (normalized) byIssue.set(normalized, value);
    }
  }
  const lookup = key => byIssue.get(issueKey(key)) ?? null;
  const leaderKey = group.members.some(key => issueKey(key) === issueKey(group.umbrella)) ? group.umbrella : group.members[0];
  const leaderRep = lookup(leaderKey)?.reproduce;
  const refModule = canonicalModule(leaderRep?.owningModule || group.owningModule || '');
  const expectedSignal = typeof group.signal === 'string' ? group.signal.trim().toLowerCase() : '';
  const groupMembers = new Set(group.members.map(issueKey));
  const signalMatches = (member, reproduce) => {
    if (!expectedSignal) return false;
    if (expectedSignal.startsWith('duplicate:')) {
      const target = issueKey(expectedSignal.slice('duplicate:'.length));
      const duplicateOf = issueKey(reproduce?.duplicateOf);
      return Boolean(target && (issueKey(member) === target
        || duplicateOf === target && groupMembers.has(target)));
    }
    const at = expectedSignal.indexOf(':');
    if (at < 1) return false;
    const kind = expectedSignal.slice(0, at), expected = expectedSignal.slice(at + 1).trim();
    return ['symbol', 'component', 'errorCode', 'route'].includes(kind)
      && typeof reproduce?.[kind] === 'string' && reproduce[kind].trim().toLowerCase() === expected;
  };
  const confirmedMembers = [], splitOut = [], reasons = {};
  for (const member of group.members) {
    const entry = lookup(member), rep = entry?.reproduce, tested = entry?.test;
    if (!entry || !rep || typeof rep !== 'object' || rep.confirmed !== true
      || entry.failed === true || entry.splitOut === true) {
      splitOut.push(member);
      reasons[member] = rep?.reason || rep?.summary || 'reproduce-not-confirmed';
      continue;
    }
    if (typeof rep.summary !== 'string' || !rep.summary.trim()
      || !tested || typeof tested !== 'object' || tested.passed !== true
      || typeof tested.name !== 'string' || !tested.name.trim()
      || typeof tested.summary !== 'string' || !tested.summary.trim()) {
      splitOut.push(member);
      reasons[member] = 'member-test-evidence-incomplete';
      continue;
    }
    const memberMod = canonicalModule(rep.owningModule || '');
    const duplicate = expectedSignal.startsWith('duplicate:');
    if (!memberMod || (!duplicate && (!refModule || memberMod !== refModule))
      || (!duplicate && group.owningModule && memberMod !== canonicalModule(group.owningModule))) {
      splitOut.push(member);
      reasons[member] = 'different-or-missing-owning-module';
      continue;
    }
    if (!signalMatches(member, rep)) {
      splitOut.push(member);
      reasons[member] = 'different-or-missing-group-signal';
      continue;
    }
    confirmedMembers.push(member);
  }
  const nextUmbrella = confirmedMembers.some(key => issueKey(key) === issueKey(group.umbrella))
    ? group.umbrella : (confirmedMembers[0] ?? '');
  const mergedSplitOut = [...new Set([...(group.splitOut ?? []), ...splitOut])];
  return {
    confirmed: confirmedMembers.length >= 2,
    umbrella: nextUmbrella,
    members: confirmedMembers,
    splitOut,
    reasons,
    standaloneRuns: splitOut.map(issue => ({ issue, action: 'work', umbrella: '', members: [], reason: reasons[issue] ?? 'split-after-reproduce' })),
    group: confirmedMembers.length >= 2 ? {
      ...group,
      umbrella: nextUmbrella,
      members: confirmedMembers,
      splitOut: mergedSplitOut,
      reproduced: true,
    } : null,
  };
}

export function splitGroupMember({ group, member, reason = 'member-diverged' }) {
  if (!group || !Array.isArray(group.members)) {
    return { umbrella: '', members: [], splitOut: [], splitMember: '', reason, standalone: null, group: null };
  }
  const targetNum = String(member ?? '').replace(/^#/, '').split('/').pop();
  const memberKey = group.members.find(k => k === member || k.split('/').pop() === targetNum) ?? String(member ?? '');
  const remaining = group.members.filter(k => k !== memberKey);
  const splitOut = [...new Set([...(group.splitOut ?? []), ...(memberKey ? [memberKey] : [])])];
  const nextUmbrella = remaining.includes(group.umbrella) ? group.umbrella : (remaining[0] ?? '');
  return {
    umbrella: nextUmbrella,
    members: remaining,
    splitOut,
    splitMember: memberKey,
    reason,
    standalone: memberKey ? { issue: memberKey, action: 'work', umbrella: '', members: [], reason } : null,
    group: remaining.length >= 2 ? {
      ...group,
      umbrella: nextUmbrella,
      members: remaining,
      splitOut,
    } : null,
  };
}

export function projectSortGraph(snapshot, graph) {
  if (!snapshot.sortContext) return graph;
  const plan = sortPlan({ snapshot }), unsafeGroups = new Set();
  graph.groups = plan.groups.map(g => ({
    area: g.area,
    rootCause: g.rootCause,
    umbrella: g.umbrella,
    members: g.members,
    ...(g.merged ? { merged: g.merged } : {}),
    ...(g.recheck ? { recheck: g.recheck } : {}),
    ...(g.notified ? { notified: g.notified } : {}),
  }));
  const hasUncertainSibling = (area, signals) => {
    if (!signals?.length) return false;
    return snapshot.issues.some(issue => !issue.assignees?.length && issue.key.startsWith(`https://github.com/${snapshot.repository.toLowerCase()}/issues/`) && issue.state === 'open' && issue.authority === 'trusted' && !selectedSort(snapshot, issue)
      && (issue.sorts ?? []).some(saved => {
        if (saved.authority !== 'trusted' || !saved.intact || !validSort(saved.record)) return false;
        const savedSignals = groupSignalsForRecord(saved.record, snapshot.repository).signals;
        if (!savedSignals.some(s => signals.includes(s))) return false;
        const resolved = resolveArea({ ...snapshot.sortContext, evidence: { paths: saved.record.paths, keywords: [issue.title, issue.sortText ?? ''], labels: issue.labels ?? [], area: saved.record.belongs.area } });
        return ! isRuntimeOwned({ issue, record: saved.record, resolved }) && resolved.area.split(',').some(x => area.split(',').includes(x));
      }));
  };
  for (const group of plan.groups.filter(x => !x.merged)) {
    const umbrella = graph.nodes.find(x => x.key === group.umbrella);
    const members = graph.nodes.filter(x => group.members.includes(x.key));
    const groupSignals = group.members.flatMap(key => {
      const m = snapshot.issues.find(x => x.key === key);
      const rec = m ? selectedSort(snapshot, m) : null;
      return rec ? groupSignalsForRecord(rec, snapshot.repository).signals : [];
    });
    if (!umbrella) { for (const member of members) { unsafeGroups.add(member.key); member.eligible = false; member.reasons.push('Group umbrella pending'); } continue; }
    if (!members.length) { unsafeGroups.add(group.umbrella); umbrella.eligible = false; umbrella.reasons.push('Group has no open members'); }
    if (group.members.some(key => { const member = snapshot.issues.find(x => x.key === key); return !selectedSort(snapshot, member); }) || hasUncertainSibling(group.area, groupSignals)) { unsafeGroups.add(group.umbrella); umbrella.eligible = false; umbrella.reasons.push('Group sort pending'); }
    const leaderRunning = umbrella.executionState === 'running';
    if (members.some(x => x.key === group.umbrella ? !['idle','running'].includes(x.executionState) : leaderRunning ? !['idle','running'].includes(x.executionState) : x.executionState !== 'idle')) unsafeGroups.add(group.umbrella);
    if (unsafeGroups.has(group.umbrella)) umbrella.eligible = false;
    const blockers = [...new Set(members.flatMap(x => x.blockers))];
    if (members.some(x => x.reviewState !== 'current' || x.reasons.includes('Incomplete relevant observations') || x.facts.length)) {
      unsafeGroups.add(group.umbrella); umbrella.eligible = false; umbrella.reasons.push('Group review pending');
    }
    if (blockers.some(x => group.members.includes(x))) {
      unsafeGroups.add(group.umbrella); for (const member of members) { member.eligible = false; member.reasons.push('Group needs dependency review'); }
    }
    const prospective = [...graph.edges, ...group.members.filter(x => x !== group.umbrella).map(dependent => ({ dependent, blocker: group.umbrella }))];
    const cycle = (key, stack = new Set(), done = new Set()) => {
      if (stack.has(key)) return true;
      if (done.has(key)) return false;
      stack.add(key);
      if (prospective.filter(x => x.dependent === key).some(x => cycle(x.blocker, stack, done))) return true;
      stack.delete(key); done.add(key); return false;
    };
    if (cycle(group.umbrella)) { unsafeGroups.add(group.umbrella); for (const member of members) { member.eligible = false; member.reasons.push('Group dependency cycle'); } }
    for (const blocker of blockers.filter(x => !group.members.includes(x))) {
      if (!umbrella.blockers.includes(blocker)) umbrella.blockers.push(blocker);
      const native = graph.nodes.find(x => x.key === blocker);
      if (!native || native.nativeState !== 'completed') { unsafeGroups.add(group.umbrella); umbrella.eligible = false; umbrella.reasons.push('Group prerequisite pending'); }
    }
  }
  for (const node of graph.nodes) {
    const route = plan.routes.find(x => x.issue === node.key);
    if (!route) continue;
    const routeSignals = route.record ? groupSignalsForRecord(route.record, snapshot.repository).signals : [];
    if (!route.umbrella && routeSignals.length && hasUncertainSibling(route.area, routeSignals)) { unsafeGroups.add(node.key); node.eligible = false; node.reasons.push('Group sort pending'); }
    node.sort = { action: route.action, area: route.area, owner: route.owner, umbrella: route.umbrella, members: route.members, rootCause: route.record?.rootCause ?? plan.groups.find(g => g.umbrella === node.key)?.rootCause ?? '', ready: !unsafeGroups.has(route.umbrella || node.key) };
    if (route.action !== 'work' || route.umbrella && route.umbrella !== node.key) {
      node.eligible = false;
      node.reasons.push(route.umbrella && route.umbrella !== node.key ? 'Waiting for root-cause umbrella' : `Sort: ${route.reason}`);
      if (route.umbrella && route.umbrella !== node.key) { node.blockers.push(route.umbrella); node.dependencyState = 'waiting'; graph.edges.push({ dependent: node.key, blocker: route.umbrella, reason: 'Shared root cause', evidence: route.evidence }); }
    }
  }
  return graph;
}

function findMemberEvidence(memberEvidence, issueKeyValue) {
  const repository = String(issueKeyValue ?? '').match(/^https:\/\/github\.com\/([^/]+\/[^/]+)\/issues\//i)?.[1] ?? '';
  const canonical = value => normalizeIssueRef(value, repository).toLowerCase();
  const target = canonical(issueKeyValue);
  if (!target || !memberEvidence) return null;
  if (Array.isArray(memberEvidence)) {
    return memberEvidence.find(entry => entry && canonical(entry.issue) === target) ?? null;
  }
  if (typeof memberEvidence === 'object') {
    for (const [key, value] of Object.entries(memberEvidence)) {
      if (canonical(key) === target && value && typeof value === 'object'
        && (value.issue === undefined || canonical(value.issue) === target)) return value;
    }
  }
  return null;
}

export function hasMemberClosingEvidence(memberEvidence, issueKeyValue, group = null) {
  const entry = findMemberEvidence(memberEvidence, issueKeyValue);
  if (!entry || typeof entry !== 'object') return false;
  const reproduce = entry.reproduce, tested = entry.test;
  const kinds = ['symbol', 'component', 'errorCode', 'route'];
  const target = normalizeIssueRef(issueKeyValue).toLowerCase();
  if (entry.failed === true || entry.splitOut === true || !reproduce || typeof reproduce !== 'object'
    || reproduce.confirmed !== true || typeof reproduce.owningModule !== 'string' || !reproduce.owningModule.trim()
    || typeof reproduce.summary !== 'string' || !reproduce.summary.trim()
    || !tested || typeof tested !== 'object' || tested.passed !== true
    || typeof tested.name !== 'string' || !tested.name.trim()
    || typeof tested.summary !== 'string' || !tested.summary.trim()) return false;
  if (!group) return kinds.some(kind => typeof reproduce[kind] === 'string' && reproduce[kind].trim())
    || typeof reproduce.duplicateOf === 'string' && reproduce.duplicateOf.trim();
  const repository = String(group.members?.[0] ?? '').match(/^https:\/\/github\.com\/([^/]+\/[^/]+)\/issues\//i)?.[1] ?? '';
  const canonical = value => normalizeIssueRef(value, repository).toLowerCase();
  if (!group.members?.some(member => canonical(member) === target)) return false;
  const module = canonicalModule(reproduce.owningModule);
  if (!module) return false;
  const signal = String(group.signal ?? '').trim().toLowerCase();
  if (signal.startsWith('duplicate:')) {
    const duplicateTarget = canonical(signal.slice('duplicate:'.length));
    const duplicateOf = canonical(reproduce.duplicateOf);
    return Boolean(duplicateTarget && (target === duplicateTarget
      || duplicateOf === duplicateTarget && group.members.some(member => canonical(member) === duplicateTarget)));
  }
  if (signal.startsWith('duplicate:')) return true;
  if (group.owningModule && module !== canonicalModule(group.owningModule)) return false;
  const at = signal.indexOf(':');
  if (at < 1) return false;
  const kind = signal.slice(0, at), expected = signal.slice(at + 1).trim();
  return kinds.includes(kind) && typeof reproduce[kind] === 'string' && reproduce[kind].trim().toLowerCase() === expected;
}

export function sortClosingReferences({ snapshot, issue, code = false, graph, memberEvidence = null }) {
  const plan = sortPlan({ snapshot });
  const group = plan.groups.find(x => x.umbrella === issue) ?? (snapshot.sortContext?.groups ?? []).find(x => !x.merged && x.umbrella === issue);
  if (!group || graph?.nodes.find(x => x.key === issue)?.sort?.ready !== true) return [];
  const splitOut = new Set(group.splitOut ?? []);
  const members = (group.members ?? []).filter(x => x !== issue && !splitOut.has(x));
  if (!code || !memberEvidence) return members.map(key => `Refs ${key}`);
  const refs = [];
  for (const key of members) {
    if (hasMemberClosingEvidence(memberEvidence, key, group)) refs.push(`Closes #${key.split('/').pop()}`);
    else refs.push(`Refs ${key}`);
  }
  return refs;
}

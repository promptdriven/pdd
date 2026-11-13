// Generated from prompts/cli/process-lifecycle.prompt.md (sha256: 633979f76a75c5eafe13c915d6c0982e6f71ea2125afa24fb03a8bf80be6da83).

const rowPattern = /^\s*(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+((?:(?:Mon|Tue|Wed|Thu|Fri|Sat|Sun) .{20})|@\S+)\s+(.*)$/;

export function parseProcessTable(text) {
  const lines = String(text ?? '').split('\n').filter(line => line.trim());
  const matches = lines.map(line => rowPattern.exec(line));
  if (matches.some(match => !match)) return null;
  const rows = matches.map(match => ({
    pid: Number(match[1]), ppid: Number(match[2]), pgid: Number(match[3]), rss: Number(match[4]), start: match[5].trim(), args: match[6]
  }));
  return rows.every(row => Number.isSafeInteger(row.pid) && row.pid > 0 && Number.isSafeInteger(row.ppid) && Number.isSafeInteger(row.pgid) && row.start) ? rows : null;
}

export const sameProcess = (saved, current) => typeof saved?.start === 'string' && saved.start.length > 0
  && saved.pid === current?.pid && saved.start === current.start && saved.args === current.args;

export function descendants(rows, roots) {
  const children = new Map(), found = [], seen = new Set(), queue = [];
  for (const row of rows ?? []) children.set(row.ppid, [...(children.get(row.ppid) ?? []), row]);
  for (const root of roots ?? []) if (root?.pid && !seen.has(root.pid)) { seen.add(root.pid); found.push(root); queue.push(root.pid); }
  let incomplete = false;
  for (let i = 0; i < queue.length; i++) {
    if (i >= 4000) { incomplete = true; break; }
    for (const row of children.get(queue[i]) ?? []) if (!seen.has(row.pid)) { seen.add(row.pid); found.push(row); queue.push(row.pid); }
  }
  Object.defineProperty(found, 'incomplete', { value: incomplete });
  return found;
}

// Returns false rather than guessing when the table is unavailable.  The caller then
// retains its worktree and record for a later retry.
export async function terminateCaptured(captured, ports) {
  const list = ports.list, signal = ports.signal, sleep = ports.sleep ?? (ms => new Promise(resolve => setTimeout(resolve, ms)));
  const grace = ports.grace ?? 2000, poll = ports.poll ?? 100;
  if (!Array.isArray(captured) || captured.incomplete) return { confirmed: false, stopped: 0, killed: 0, remaining: captured?.length ?? 0 };
  const read = async () => {
    try {
      const rows = await list();
      return Array.isArray(rows) && rows.incomplete !== true && rows.every(row => row && Number.isSafeInteger(row.pid) && row.pid > 0
        && Number.isSafeInteger(row.ppid) && Number.isSafeInteger(row.pgid) && Number.isSafeInteger(row.rss)
        && typeof row.start === 'string' && row.start.length > 0 && typeof row.args === 'string') ? rows : null;
    } catch { return null; }
  };
  const leaders = [], seenGroups = new Set();
  for (const row of captured) {
    if (Number.isSafeInteger(row?.pgid) && row.pgid > 1 && row.pid === row.pgid && row.pgid !== process.pid && !seenGroups.has(row.pgid)) {
      seenGroups.add(row.pgid); leaders.push(row);
    }
  }
  const groupState = (rows, leader) => {
    const current = rows.find(row => row.pid === leader.pid);
    if (current && current.start !== leader.start) return { active: false, uncertain: false, members: [] };
    if (current && !sameProcess(leader, current)) return { active: false, uncertain: true, members: [current] };
    const members = rows.filter(row => row.pgid === leader.pgid && row.pid !== process.pid);
    return { active: members.some(row => row.pid !== leader.pid), uncertain: false, members };
  };
  const matching = (rows, targets) => {
    const now = new Map(rows.map(row => [row.pid, row]));
    const live = [], uncertain = [];
    for (const row of targets) {
      const current = now.get(row.pid);
      if (!current || current.start !== row.start) continue; // It ended, or this PID was reused.
      if (sameProcess(row, current)) live.push(row); else uncertain.push(row); // Same process, changed command: retain it.
    }
    return { live, uncertain };
  };
  const remainingCount = (liveRows, rows, groupRows) => {
    const pids = new Set(liveRows.map(row => row.pid));
    for (const leader of groupRows) for (const member of groupState(rows, leader).members) pids.add(member.pid);
    return pids.size;
  };
  let rows = await read();
  if (!rows) return { confirmed: false, stopped: 0, killed: 0, remaining: captured.length };
  let { live, uncertain } = matching(rows, captured), stopped = 0, killed = 0;
  if (uncertain.length || leaders.some(leader => groupState(rows, leader).uncertain))
    return { confirmed: false, stopped, killed, remaining: Math.max(1, live.length + uncertain.length) };
  let activeGroups = leaders.filter(leader => groupState(rows, leader).active);
  const termRows = [], termPids = new Set();
  for (const row of live) {
    rows = await read();
    if (!rows) return { confirmed: false, stopped, killed, remaining: Math.max(1, live.length) };
    const current = matching(rows, [row]);
    if (current.uncertain.length) return { confirmed: false, stopped, killed, remaining: Math.max(1, current.uncertain.length + termRows.length) };
    if (!current.live.length) continue;
    try { signal(row.pid, 'SIGTERM'); stopped++; } catch { /* A later inventory decides. */ }
    termRows.push(row); termPids.add(row.pid);
  }
  const termGroups = [];
  for (const leader of activeGroups) {
    termGroups.push(leader);
    if (!groupState(rows, leader).members.some(member => !termPids.has(member.pid))) continue;
    rows = await read();
    if (!rows) return { confirmed: false, stopped, killed, remaining: Math.max(1, termRows.length + activeGroups.length) };
    const state = groupState(rows, leader);
    if (state.uncertain) return { confirmed: false, stopped, killed, remaining: Math.max(1, state.members.length + termGroups.length) };
    if (!state.members.some(member => !termPids.has(member.pid))) continue;
    try { signal(-leader.pgid, 'SIGTERM'); if (!termPids.has(leader.pid)) stopped++; } catch { /* A later inventory decides. */ }
  }
  live = termRows;
  activeGroups = termGroups;
  for (let waited = 0; (live.length || activeGroups.length) && waited < grace; waited += poll) {
    await sleep(Math.min(poll, grace - waited));
    rows = await read();
    if (!rows) return { confirmed: false, stopped, killed, remaining: Math.max(1, live.length + activeGroups.length) };
    ({ live, uncertain } = matching(rows, live));
    if (uncertain.length || activeGroups.some(leader => groupState(rows, leader).uncertain))
      return { confirmed: false, stopped, killed, remaining: Math.max(1, live.length + uncertain.length) };
    activeGroups = activeGroups.filter(leader => groupState(rows, leader).members.length > 0);
  }
  const killRows = [], killPids = new Set();
  for (const row of live) {
    rows = await read();
    if (!rows) return { confirmed: false, stopped, killed, remaining: Math.max(1, live.length) };
    const current = matching(rows, [row]);
    if (current.uncertain.length) return { confirmed: false, stopped, killed, remaining: Math.max(1, current.uncertain.length + killRows.length) };
    if (!current.live.length) continue;
    try { signal(row.pid, 'SIGKILL'); killed++; } catch { /* A later inventory decides. */ }
    killRows.push(row); killPids.add(row.pid);
  }
  const killGroups = [];
  for (const leader of activeGroups) {
    if (!groupState(rows, leader).members.some(member => !killPids.has(member.pid))) continue;
    rows = await read();
    if (!rows) return { confirmed: false, stopped, killed, remaining: Math.max(1, killRows.length + activeGroups.length) };
    const state = groupState(rows, leader);
    if (state.uncertain) return { confirmed: false, stopped, killed, remaining: Math.max(1, state.members.length + killGroups.length) };
    if (!state.members.some(member => !killPids.has(member.pid))) continue;
    try { signal(-leader.pgid, 'SIGKILL'); if (!killPids.has(leader.pid)) killed++; } catch { /* A later inventory decides. */ }
    killGroups.push(leader);
  }
  live = killRows;
  if (killRows.length || killGroups.length) {
    await sleep(poll);
    rows = await read();
    if (!rows) return { confirmed: false, stopped, killed, remaining: Math.max(1, killRows.length + killGroups.length) };
    ({ live, uncertain } = matching(rows, killRows));
    if (uncertain.length || killGroups.some(leader => groupState(rows, leader).uncertain))
      return { confirmed: false, stopped, killed, remaining: Math.max(1, live.length + uncertain.length) };
  }
  const remaining = rows ? remainingCount(live, rows, killGroups) : live.length;
  return { confirmed: remaining === 0, stopped, killed, remaining };
}

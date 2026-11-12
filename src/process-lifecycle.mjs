// Generated from prompts/cli/process-lifecycle.prompt.md (sha256: de04fa68ad1a4008e5a1558f65bb0a37d627643318e5d30ca12102d60edaa091).

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
  let rows;
  try { rows = await list(); } catch { return { confirmed: false, stopped: 0, killed: 0, remaining: captured.length }; }
  if (!Array.isArray(rows)) return { confirmed: false, stopped: 0, killed: 0, remaining: captured.length };
  const matching = () => {
    const now = new Map(rows.map(row => [row.pid, row]));
    const live = [], uncertain = [];
    for (const row of captured) {
      const current = now.get(row.pid);
      if (!current || current.start !== row.start) continue; // It ended, or this PID was reused.
      if (sameProcess(row, current)) live.push(row); else uncertain.push(row); // Same process, changed command: retain it.
    }
    return { live, uncertain };
  };
  let { live, uncertain } = matching(), stopped = 0, killed = 0;
  if (uncertain.length) return { confirmed: false, stopped, killed, remaining: live.length + uncertain.length };
  for (const row of live) try { signal(row.pid, 'SIGTERM'); stopped++; } catch { /* A later inventory decides. */ }
  for (let waited = 0; live.length && waited < grace; waited += poll) {
    await sleep(Math.min(poll, grace - waited));
    try { rows = await list(); } catch { return { confirmed: false, stopped, killed, remaining: live.length }; }
    if (!Array.isArray(rows)) return { confirmed: false, stopped, killed, remaining: live.length };
    ({ live, uncertain } = matching());
    if (uncertain.length) return { confirmed: false, stopped, killed, remaining: live.length + uncertain.length };
  }
  for (const row of live) try { signal(row.pid, 'SIGKILL'); killed++; } catch { /* A later inventory decides. */ }
  if (live.length) {
    await sleep(poll);
    try { rows = await list(); } catch { return { confirmed: false, stopped, killed, remaining: live.length }; }
    if (!Array.isArray(rows)) return { confirmed: false, stopped, killed, remaining: live.length };
    ({ live, uncertain } = matching());
    if (uncertain.length) return { confirmed: false, stopped, killed, remaining: live.length + uncertain.length };
  }
  return { confirmed: live.length === 0, stopped, killed, remaining: live.length };
}

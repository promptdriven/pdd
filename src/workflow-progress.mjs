// Generated from prompts/cli/workflow-progress.prompt.md (sha256: 3e1522ccdd18f454aea3c3b6f29dab1687750a548769c7b63ea692758f4bc009).
const clean = value => String(value ?? '').replace(/[\x00-\x1f\x7f-\x9f]/g, ' ').replace(/\s+/g, ' ').trim();
const uuid = value => /^[a-f0-9]{8}-[a-f0-9]{4}-4[a-f0-9]{3}-[89ab][a-f0-9]{3}-[a-f0-9]{12}$/i.test(value ?? '');
const AGENTS = { codex: 'Codex', claude: 'Claude' };
const HEARTBEAT_MS = 2 * 60 * 1000;
const clock = (ms, timeZone) => new Intl.DateTimeFormat('en-GB', { hour: '2-digit', minute: '2-digit', hourCycle: 'h23', ...(timeZone ? { timeZone } : {}) }).format(new Date(ms));

export function createWorkflowProgress({ stdout = process.stdout, now = () => Date.now(), timeZone } = {}) {
  let current, running = null, gate = false;
  const seen = new Set();
  const line = text => stdout.write(`${text}\n`);
  const timed = text => line(`${clock(now(), timeZone)}  ${text}`);
  const once = (key, text) => { if (!seen.has(key)) { seen.add(key); line(text); } };
  const observe = value => {
    current = value;
    const id = uuid(value.runId) ? value.runId : null;
    if (!id) return;
    if (value.root) {
      const title = value.title ? ` "${clean(value.title)}"` : '';
      once(`run:${id}`, `Run ${id}: ${clean(value.name)} for #${clean(value.issue)}${title}. Stage ${Math.min(value.ordinal, value.total)}/${value.total}: ${clean(value.stage?.id ?? 'complete')}.`);
      once(`root:${id}`, `Working copy: ${clean(value.root)} (branch ${clean(value.branch)})\nOpen the agent: pdd workflow attach ${id} (pdd pauses while you are attached; close it to let the run go on)`);
    }
    const backend = value.backend;
    if (backend?.session && backend.workspaceId) once(`backend:${id}:${backend.session}:${backend.workspaceId}`,
      `${AGENTS[value.agent] ?? 'The agent'} is working in Herdr session ${clean(backend.session)}, workspace "#${clean(value.issue)} ${clean(value.name)}".`);
    const stage = clean(value.stage?.id ?? 'complete');
    if (['agent.intent', 'pr.intent'].includes(value.event)) { timed(`${stage} started`); running = { stage, since: now(), beats: 0 }; }
    else if (running) {
      const beats = Math.floor((now() - running.since) / HEARTBEAT_MS);
      if (beats > running.beats) { running.beats = beats; timed(`${running.stage} still working (${Math.floor((now() - running.since) / 60000)} min)`); }
    }
    if (['agent.completed', 'pr.completed', 'merge.observed', 'human.approved'].includes(value.event)) { timed(`${clean(value.ended)} done`); running = null; }
    if (['optional.skipped', 'merge.skipped'].includes(value.event)) { timed(`${clean(value.ended)} skipped`); running = null; }
    if (value.event === 'test.intent') timed(`${stage}: running approved tests`);
    if (['test.completed', 'test.failed'].includes(value.event)) timed(`${stage}: tests ${value.event === 'test.completed' ? 'passed' : 'failed'}`);
    if (value.event !== 'result') return;
    running = null;
    if (value.state !== 'waiting') timed(`${stage}: ${clean(value.state)}`);
    else timed(value.stage?.kind === 'merge' ? 'waiting for you to merge the PR' : `waiting for you before ${stage}`);
    if (value.state === 'waiting') {
      gate = true;
      if (value.stage?.kind === 'merge') {
        line(`Review and merge the PR on GitHub. PDD never merges.\nCheck merge: pdd workflow resume ${id}`);
      } else if (value.pending) {
        line(`Inspect: pdd workflow resume ${id}\nWatch: pdd workflow attach ${id}\nAfter reviewing the saved state, continue: pdd workflow resume ${id} --decision approve`);
      } else {
        if (value.summary) line(`Summary: ${clean(value.summary).slice(0, 1200)}`);
        const files = value.files ?? [], inside = value.root ? files.filter(path => String(path).startsWith(`${value.root}/`)) : [];
        for (const path of inside.length ? inside : files) line(`Read: ${clean(path)}`);
        line(`Approve: pdd workflow resume ${id} --decision approve`);
        if (value.stage?.optional) line(`Skip: pdd workflow resume ${id} --decision skip`);
      }
    }
    for (const url of new Set(value.prs ?? [])) line(`PR: ${clean(url)}`);
  };
  const interrupt = () => {
    line('\nPDD stopped advancing this run. The agent may keep working in Herdr.');
    if (uuid(current?.runId)) {
      const id = current.runId;
      line(`Watch: pdd workflow attach ${id}\nInspect: pdd workflow resume ${id}\nAfter the agent finishes, review its result. PDD moves on when you run: pdd workflow resume ${id} --decision approve`);
    } else line('Preparation was interrupted before a run identity was confirmed. Check .git/pdd/workflow-inputs in your repository for any saved run ID.');
  };
  return { observe, interrupt, gateShown: () => gate };
}

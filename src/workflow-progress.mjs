// Generated from prompts/cli/workflow-progress.prompt.md (sha256: 09b3629ac091453e1fbf63aa1deaa0f4c13ddab52b92dd362a012d0408130ed1).
const clean = value => String(value ?? '').replace(/[\x00-\x1f\x7f-\x9f]/g, ' ').replace(/\s+/g, ' ').trim();
const uuid = value => /^[a-f0-9]{8}-[a-f0-9]{4}-4[a-f0-9]{3}-[89ab][a-f0-9]{3}-[a-f0-9]{12}$/i.test(value ?? '');

export function createWorkflowProgress({ stdout = process.stdout, now = () => Date.now() } = {}) {
  let current;
  const seen = new Set();
  const line = text => stdout.write(`${text}\n`);
  const timed = text => line(`[${new Date(now()).toISOString()}] ${text}`);
  const once = (key, text) => { if (!seen.has(key)) { seen.add(key); line(text); } };
  const observe = value => {
    current = value;
    const id = uuid(value.runId) ? value.runId : null;
    if (!id) return;
    if (value.root) {
      once(`run:${id}`, `Run ${id} (${clean(value.name)}, issue #${clean(value.issue)}). Stage ${Math.min(value.ordinal, value.total)}/${value.total}: ${clean(value.stage?.id ?? 'complete')}.`);
      once(`root:${id}`, `Worktree: ${clean(value.root)}\nBranch: ${clean(value.branch)}\nSaved run: ${clean(value.journal)}\nWatch: pdd workflow attach ${id}`);
    }
    const backend = value.backend;
    if (backend?.session) once(`backend:${id}:${backend.session}:${backend.workspaceId ?? ''}`,
      `Herdr session: ${clean(backend.session)}; workspace: ${clean(backend.workspaceId ?? 'preparing')}. Watch: pdd workflow attach ${id}`);
    const stage = clean(value.stage?.id ?? 'complete');
    if (['agent.intent', 'pr.intent'].includes(value.event)) timed(`stage ${stage} started`);
    if (['agent.completed', 'pr.completed', 'merge.observed', 'human.approved'].includes(value.event)) timed(`stage ${clean(value.ended)} done`);
    if (['optional.skipped', 'merge.skipped'].includes(value.event)) timed(`stage ${clean(value.ended)} skipped`);
    if (value.event === 'test.intent') timed(`stage ${stage}: running approved tests`);
    if (['test.completed', 'test.failed'].includes(value.event)) timed(`stage ${stage}: tests ${value.event === 'test.completed' ? 'passed' : 'failed'}`);
    if (value.event !== 'result') return;
    timed(`stage ${stage}: ${clean(value.state)}`);
    if (value.state === 'waiting') {
      if (value.stage?.kind === 'merge') {
        line(`Review and merge the PR on GitHub. PDD never merges.\nCheck merge: pdd workflow resume ${id}`);
      } else if (value.pending) {
        line(`Inspect: pdd workflow resume ${id}\nWatch: pdd workflow attach ${id}\nAfter reviewing the saved state, continue: pdd workflow resume ${id} --decision approve`);
      } else {
        if (value.summary) line(`Summary: ${clean(value.summary).slice(0, 1200)}`);
        for (const path of value.files ?? []) line(`Read: ${clean(path)}`);
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
      if (current.journal) line(`Saved run: ${clean(current.journal)}`);
    } else line('Preparation was interrupted before a run identity was confirmed. Check .git/pdd/workflow-inputs in your repository for any saved run ID.');
  };
  return { observe, interrupt };
}

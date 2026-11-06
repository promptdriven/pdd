// Generated from prompts/cli/workflow-worker-completion.prompt.md.
import { spawn, execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { readFileSync, realpathSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { readRun, updateRun, currentChat } from './workflow-runs.mjs';
import { launchAnchor, START_GRACE_MS } from './workflow-chat.mjs';

const exec = promisify(execFile);
const modulePath = fileURLToPath(import.meta.url);

export function armWorkerCompletion(identity, ports = {}) {
  const child = (ports.spawn ?? spawn)(process.execPath, [modulePath, JSON.stringify(identity)], {
    detached: true, stdio: 'ignore', env: ports.env ?? process.env,
  });
  child.on('error', () => {});
  child.unref();
}

export function armSavedWorkerCompletion(run, coordinatorPaneId, ports = {}) {
  const chat = currentChat(run), anchor = launchAnchor(chat);
  if (!run.automaticOrigin || !chat?.paneId || !Number.isFinite(anchor) || !coordinatorPaneId) return false;
  const requireActivity = Number.isFinite(chat.resumedAt) && chat.resumedAt === anchor && chat.completionActivityAnchor !== anchor;
  (ports.armWorkerCompletion ?? armWorkerCompletion)({ runId: run.runId, number: run.number, sourceRoot: run.sourceRoot, runDir: run.runDir, area: chat.area, paneId: chat.paneId, startAnchor: anchor, coordinatorPaneId, ...(requireActivity ? { requireActivity: true } : {}) }, { env: ports.env });
  return true;
}

function coordinatorState(identity, env) {
  const root = realpathSync(identity.sourceRoot);
  const id = createHash('sha256').update(root).digest('hex').slice(0, 20);
  return JSON.parse(readFileSync(join(env.HOME || homedir(), '.local', 'state', 'pdd', 'autopilot', `${id}.json`), 'utf8'));
}

export async function waitForWorkerCompletion(identity, ports = {}) {
  let release;
  try {
    const env = ports.env ?? process.env;
    const wait = ports.wait ?? ((session, pane, until) => exec('herdr', ['--session', session, 'agent', 'wait', pane, ...until.flatMap(value => ['--until', value])], { timeout: 0, env }));
    const now = ports.now ?? Date.now;
    const sleep = ports.sleep ?? (ms => new Promise(resolve => setTimeout(resolve, ms)));
    const current = () => {
      const run = (ports.readRun ?? readRun)(identity.runDir);
      const chat = run && currentChat(run);
      return run && run.runId === identity.runId && run.areas?.[run.area]?.name === identity.area && chat?.paneId === identity.paneId && launchAnchor(chat) === identity.startAnchor;
    };
    for (const status of identity.requireActivity ? ['working', 'done'] : ['done']) {
      while (true) {
      try {
        await wait('pdd', identity.paneId, [status]);
        if (!current()) return null;
        if (status === 'working') {
          const mark = ports.markActivity ?? ((id) => updateRun(id.runDir, run => {
            const chat = currentChat(run);
            if (run.runId !== id.runId || run.areas?.[run.area]?.name !== id.area || chat?.paneId !== id.paneId || launchAnchor(chat) !== id.startAnchor) throw Error('Worker attempt changed');
            chat.completionActivityAnchor = id.startAnchor;
            return run;
          }, { env }));
          await mark(identity);
        }
        break;
      }
      catch (error) {
        let code = error.code;
        try { code = JSON.parse(error.stderr).error.code; } catch { /* not a native JSON error */ }
        const remaining = identity.startAnchor + START_GRACE_MS - now();
        if (code !== 'agent_not_found' || !Number.isFinite(remaining) || remaining <= 0 || !current()) throw error;
        await sleep(Math.min(250, remaining));
        if (now() >= identity.startAnchor + START_GRACE_MS || !current()) return null;
      }
    }
    }
    const state = await (ports.coordinatorState ?? coordinatorState)(identity, env);
    if (!state || typeof state.enabled !== 'boolean') return null;
    if (state.enabled) {
      if (!identity.coordinatorPaneId || state.paneId !== identity.coordinatorPaneId) return null;
      await wait('pdd-autopilot', identity.coordinatorPaneId, ['idle', 'done']);
    }
    const runner = await import('./workflow-runner.mjs');
    const unlock = (ports.acquireRunLock ?? runner.acquireRunLock)(identity.runDir);
    let released = false;
    release = () => { if (!released) { released = true; unlock(); } };
    const run = (ports.readRun ?? readRun)(identity.runDir);
    const chat = run && currentChat(run);
    if (!run || run.runId !== identity.runId || run.areas?.[run.area]?.name !== identity.area || chat?.paneId !== identity.paneId || launchAnchor(chat) !== identity.startAnchor) return null;
    const yieldCapacity = ports.yieldCapacity ?? runner.yieldAutomaticCapacity;
    return await yieldCapacity({ ref: String(identity.number), cwd: identity.sourceRoot }, { env, expectedCompletion: identity, releaseRunLock: release });
  } catch {
    return null;
  } finally { release?.(); }
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  try {
    const arg = process.argv[2];
    const identity = JSON.parse(arg.trimStart().startsWith('{') ? arg : readFileSync(arg, 'utf8'));
    await waitForWorkerCompletion(identity);
  } catch { /* An unavailable listener is not completion. */ }
}

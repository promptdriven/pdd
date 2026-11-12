// Generated from prompts/cli/accounts-reset.prompt.md (sha256: e2c5348fa2b68324ab593a9608da16ac07b269f4e4353c0d61cc51b52f9930b2).
import { createInterface } from 'node:readline';
import { approvalActor } from './approval-policy.mjs';
import { resetNoticeText, usedTodayFromLog } from './accounts-pick.mjs';

const NAME = /^[a-z0-9][a-z0-9._-]{0,31}$/;
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const finite = value => typeof value === 'number' && Number.isFinite(value);
const nonempty = value => typeof value === 'string' && value.length > 0;
const done = (exitCode, message) => ({ exitCode, message });
const ownRow = (rows, name) => object(rows) && Object.hasOwn(rows, name) ? rows[name] : null;

// consumeReset has no default: this version never spends a reset by itself.
function defaultPorts(env) {
  const store = () => import('./accounts-store.mjs'), usage = () => import('./accounts-usage.mjs');
  return {
    now: () => Date.now(),
    findLogin: async name => {
      const { readPool, orderedLogins } = await store();
      return orderedLogins(await readPool({ env })).find(login => login?.name === name) ?? null;
    },
    readLog: async name => (await store()).readLog({ env, name }),
    appendLog: async row => (await store()).appendLog({ env }, row),
    readUsage: async name => ownRow(await (await usage()).loadUsage({ env }), name),
    forgetUsage: async name => {
      const { loadUsage, saveUsage } = await usage();
      const rows = await loadUsage({ env });
      if (!object(rows) || !Object.hasOwn(rows, name)) return;
      delete rows[name];
      await saveUsage({ env }, rows);
    },
  };
}

function readLine(stdin) {
  return new Promise(resolve => {
    const lines = createInterface({ input: stdin, terminal: false });
    let answered = false;
    const finish = value => { if (answered) return; answered = true; lines.close(); resolve(value); };
    lines.once('line', finish);
    lines.once('close', () => finish(null));
  });
}

const agentCaller = env => approvalActor(env).kind === 'agent' || nonempty(env.PDD_AGENT) || nonempty(env.PDD_AUTOPILOT_CONTEXT);

export async function runReset({ name, env = process.env, stdin = process.stdin, stdout = process.stdout } = {}, ports = {}) {
  try {
    const p = { ...defaultPorts(env), ...ports };
    if (agentCaller(env ?? {})) return done(2, 'pdd accounts reset runs only for a person at a terminal. It does not run under an agent or Autopilot. No reset was used.');
    if (stdin?.isTTY !== true) return done(2, 'pdd accounts reset needs a person at a terminal to type the login name. No reset was used.');
    if (typeof p.consumeReset !== 'function') return done(2, 'This pdd has no Codex reset call yet. No reset was used.');
    if (typeof name !== 'string' || !NAME.test(name)) return done(2, 'Give a login name: pdd accounts reset NAME. No reset was used.');
    let login;
    try { login = await p.findLogin(name); } catch { return done(1, 'Could not read the login pool. No reset was used.'); }
    if (!object(login)) return done(2, `No login named ${name} in this pool. See pdd accounts list. No reset was used.`);
    if (login.provider !== 'codex') return done(2, `${name} is a Claude login. Only Codex logins have resets. No reset was used.`);
    if (login.mode !== undefined && login.mode !== 'local') return done(2, `${name} is on the login server. This version resets only local logins. No reset was used.`);
    if (login.reset !== 'ask' && login.reset !== 'auto') return done(2, `${name} has reset never. To allow resets, run: pdd accounts set ${name} --reset ask. No reset was used.`);
    const now = p.now();
    let used;
    try { used = usedTodayFromLog(await p.readLog(name), now); } catch { return done(1, `Could not read the reset log of ${name}. No reset was used.`); }
    if (used.includes(name)) return done(2, `${name} used a reset less than 24 hours ago. pdd allows one reset per login per day. No reset was used.`);
    stdout.write(`Reset ${name} now? This uses one of its Codex resets. pdd cannot undo it.\nType ${name} to confirm, or press Enter to stop: `);
    const typed = await readLine(stdin);
    if (typed === null || typed.trim() !== name) return done(1, 'Not confirmed. No reset was used.');
    let row = null;
    try { row = await p.readUsage(name); } catch {}
    let outcome;
    try { outcome = (await p.consumeReset(login))?.outcome; } catch { outcome = 'unclear'; }
    if (outcome === 'noCredit') return done(1, `${name} has no reset left. No reset was used.`);
    if (outcome === 'nothingToReset') return done(1, `${name} has no limit that a reset can clear now. No reset was used.`);
    if (outcome === 'failed') return done(1, `Could not reach Codex for ${name}. No reset was used.`);
    const usedReset = outcome === 'reset' || outcome === 'alreadyRedeemed';
    let logged = true;
    try { await p.appendLog({ at: new Date(now).toISOString(), action: 'reset', login: name, detail: usedReset ? 'used by a person at a terminal' : 'outcome unclear' }); }
    catch { logged = false; }
    try { await p.forgetUsage(name); } catch {}
    const logNote = logged ? '' : ' The local log could not be written.';
    if (!usedReset) return done(1, `The reset of ${name} did not finish clearly. It may have used a reset. Run pdd accounts list to see its usage.${logNote}`);
    const facts = { name, now, timeZone: p.timeZone,
      until: object(row) && object(row.week) && finite(row.week.resetsAt) ? row.week.resetsAt : undefined,
      left: object(row) && object(row.resets) && finite(row.resets.left) ? row.resets.left : undefined };
    if (typeof p.notify === 'function') { try { await p.notify(resetNoticeText({ ...facts, actor: 'A person at a terminal' })); } catch {} }
    return done(0, `${resetNoticeText({ ...facts, actor: 'You' })}${logged ? '' : `.${logNote}`}`);
  } catch {
    return done(1, 'pdd accounts reset failed. No reset was used.');
  }
}

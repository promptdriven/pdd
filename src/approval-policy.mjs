// Generated from prompts/cli/approval-policy.prompt.md (sha256: e3cdbbc059d8558d16c27a2fad313b2015f4aeff75975ef2621a0c0d1c732556).
import * as nativeFs from 'node:fs';
import { join } from 'node:path';
import { randomUUID } from 'node:crypto';
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
export function readApprovalPolicy({ root }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  let text;
  try { text = fs.readFileSync(join(root, 'pdd.json'), 'utf8'); }
  catch (error) { if (error.code === 'ENOENT') return { strictApprovals: false }; throw Error('Cannot read pdd.json.'); }
  let config;
  try { config = JSON.parse(text); } catch { throw Error('Invalid JSON in pdd.json.'); }
  if (!object(config) || Object.hasOwn(config, 'strict_approvals') && typeof config.strict_approvals !== 'boolean') throw Error('pdd.json must be an object with boolean strict_approvals.');
  return { strictApprovals: config.strict_approvals ?? false };
}
export function approvalActor(env = process.env) {
  for (const key of ['CODEX_THREAD_ID', 'CLAUDECODE', 'PDD_AGENT_SESSION']) if (typeof env[key] === 'string' && env[key].length) return { kind: 'agent', id: `${key}=${env[key]}` };
  return { kind: 'terminal', id: env.USER || env.LOGNAME || 'unknown' };
}
function validEvidence(e) {
  return object(e) && (!Object.hasOwn(e, 'id') || typeof e.id === 'string' && e.id.length > 0) && ['said','terminal','chat'].includes(e.route) && object(e.actor) && ['agent','terminal'].includes(e.actor.kind) && typeof e.actor.id === 'string' && Number.isSafeInteger(e.at) && (e.words === null || typeof e.words === 'string') && Array.isArray(e.prompts) && e.prompts.every(p => object(p) && typeof p.path === 'string' && /^[a-f0-9]{64}$/.test(p.proseSha256));
}
export function readPromptApprovals({ commonDir }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  let text;
  try { text = fs.readFileSync(join(commonDir, 'pdd', 'approvals.json'), 'utf8'); }
  catch (error) { if (error.code === 'ENOENT') return []; throw Error('Cannot read pdd/approvals.json.'); }
  let journal;
  try { journal = JSON.parse(text); } catch { throw Error('Invalid pdd/approvals.json.'); }
  if (!object(journal) || journal.v !== 1 || !Array.isArray(journal.approvals) || !journal.approvals.every(validEvidence)) throw Error('Invalid pdd/approvals.json.');
  return journal.approvals;
}
export async function recordPromptApproval({ commonDir, evidence }, ports = {}) {
  if (!validEvidence(evidence)) throw Error('Invalid approval evidence.');
  const fs = ports.fs ?? nativeFs, dir = join(commonDir, 'pdd'), lock = join(dir, 'approvals.lock');
  fs.mkdirSync(dir, { recursive: true, mode: 0o700 });
  let locked = false;
  for (let attempt = 0; attempt < 500; attempt++) {
    try { fs.mkdirSync(lock); locked = true; break; }
    catch (error) { if (error.code !== 'EEXIST') throw error; await new Promise(done => setTimeout(done, 10)); }
  }
  if (!locked) throw Error('pdd/approvals.json is busy; retry approval.');
  const temporary = join(dir, `.approvals.${randomUUID()}.tmp`);
  try {
    const approvals = readPromptApprovals({ commonDir }, ports);
    fs.writeFileSync(temporary, JSON.stringify({ v: 1, approvals: [...approvals, evidence] }, null, 2) + '\n', { mode: 0o600 });
    fs.renameSync(temporary, join(dir, 'approvals.json'));
  } finally {
    try { fs.unlinkSync(temporary); } catch { /* Already renamed or never written. */ }
    fs.rmdirSync(lock);
  }
}

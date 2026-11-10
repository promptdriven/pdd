// Generated from prompts/cli/workflow-pr-evidence.prompt.md (sha256: eaa7434b35e61c4022b3e14c8ea25c792be12cd286d9223cac15d6e3cef3f374).
import { execFile } from 'node:child_process';
import { lstatSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { formatProof, validateProofRecord } from './workflow-prove.mjs';

function safeValue(value) {
  let content = JSON.stringify(String(value)).slice(1,-1).replace(/[\u007f-\u009f\u2028\u2029]/g, char => '\\u'+char.charCodeAt(0).toString(16).padStart(4,'0')).replaceAll('pdd-workflow:', 'pdd-workflow\\u003a');
  let fenceLength = 1;
  for (const run of content.matchAll(/`+/g)) fenceLength = Math.max(fenceLength, run[0].length + 1);
  const fence = '`'.repeat(fenceLength);
  const padding = content.startsWith('`') || content.endsWith('`') || content.startsWith(' ') && content.endsWith(' ') && content.trim() ? ' ' : '';
  return fence+padding+content+padding+fence;
}
// Approval values retain JSON quoting, unlike ordinary lifted prose.
function approvalValue(value) {
  const content = JSON.stringify(String(value)).replace(/[\u007f-\u009f\u061c\u200e\u200f\u2028-\u202e\u2066-\u2069]/g, char => '\\u'+char.charCodeAt(0).toString(16).padStart(4,'0')).replaceAll('pdd-workflow:', 'pdd-workflow\\u003a');
  const fence = '`'.repeat(Math.max(1, ...[...content.matchAll(/`+/g)].map(match => match[0].length + 1)));
  return fence + content + fence;
}
// Each approval once, oldest first: gate decisions and the matching prompt approvals. The readable PR part (#3042)
// reads these plain facts for its one approval line; the rendered approval lines stay in Details.
export function approvalRecords(run) {
  const seen = new Set(), rows = [];
  for (const decision of run.decisions ?? []) {
    if (decision.decision !== 'approve') continue;
    if (decision.evidence) rows.push(decision.evidence);
    else rows.push({ route: decision.via, at: decision.at, ...(decision.text !== undefined ? { words: decision.text } : {}) });
  }
  rows.push(...(run.promptApprovals ?? []));
  return rows.sort((a,b) => a.at-b.at).filter(evidence => {
    const key = typeof evidence.id === 'string' && evidence.id.length
      ? `id:${evidence.id}` : `legacy:${JSON.stringify([evidence.route, evidence.actor, evidence.at, evidence.words, evidence.prompts])}`;
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });
}
function approvalLines(records) {
  return records.flatMap(evidence => {
    const label = evidence.route === 'said' ? 'Approved in chat:' : evidence.route === 'chat' ? 'Approved in area chat:'
      : evidence.route === 'automatic-check-pass' ? 'Opened after a full check pass (no person asked):' : evidence.route === 'card-choice' ? 'Code PR chosen at the Story card:' : evidence.route === 'prompt-reentry' ? 'Code PR resumed under the existing automatic scope:' : 'Approved in terminal:';
    const values = [evidence.words !== undefined && evidence.words !== null ? approvalValue(evidence.words) : null,
      evidence.actor ? `actor ${approvalValue(evidence.actor.kind)} ${approvalValue(evidence.actor.id)}` : null,
      evidence.at !== undefined ? `at ${approvalValue(new Date(evidence.at).toISOString())}` : null,
      `route ${approvalValue(evidence.route)}`,
      ...(evidence.prompts ?? []).map(prompt => `${approvalValue(prompt.path)} ${approvalValue(prompt.proseSha256)}`)].filter(Boolean);
    return [`${label} ${values.join('; ')}`];
  });
}
const execute = promisify(execFile);
const labels = ['Not fixed yet:', 'Not checked:', 'Defect:', 'Not caught because:', 'Proof (defect fixed):', 'Proof (gap closed):', 'Review:'];
const safeStep = step => typeof step === 'string' && step.length > 0 && !/[\\/\u0000-\u001f]/u.test(step) && step !== '.' && step !== '..';
const sha = value => typeof value === 'string' && /^[a-f0-9]{40}$/.test(value);
const defaults = {
  async currentHead({ root, baseBranch }) {
    try {
      await execute('git',['check-ref-format',`refs/heads/${baseBranch}`],{cwd:root});
      await execute('git',['fetch','origin',`refs/heads/${baseBranch}:refs/remotes/origin/${baseBranch}`],{cwd:root});
      const { stdout } = await execute('git', ['rev-parse', '--verify', 'HEAD^{commit}'], { cwd: root, encoding: 'utf8' });
      const headSha = stdout.trim();
      const baseSha=(await execute('git',['merge-base',headSha,`refs/remotes/origin/${baseBranch}`],{cwd:root,encoding:'utf8'})).stdout.trim();
      return sha(headSha)&&sha(baseSha) ? { headSha, baseSha, error: '' } : { headSha: '', baseSha:'', error: 'Current Git head unavailable.' };
    } catch { return { headSha: '', baseSha:'', error: 'Current Git head unavailable.' }; }
  },
  async readStepNotes({ runDir, steps }) {
    const notes = [];
    for (const step of steps.filter(safeStep)) {
      try {
        const path = join(runDir, `${step}.md`);
        if (lstatSync(path).isFile()) notes.push({ step, text: readFileSync(path, 'utf8') });
      } catch { /* Missing or unreadable notes contribute nothing. */ }
    }
    return { notes };
  },
  async readOldCodeProof({ runDir }) {
    try {
      const path = join(runDir, 'old-code-proof.json');
      if (!lstatSync(path).isFile()) return { content: '', error: 'Proof is not a regular file.' };
      return { content: readFileSync(path, 'utf8'), error: '', savedAt: lstatSync(path).mtimeMs };
    } catch (error) { return { content: '', error: error.code === 'ENOENT' ? 'missing' : 'Proof could not be read.' }; }
  }
};

// One freshness rule for a saved old-code proof (#2904): the PR renderer and the step reader both call it, so they never disagree.
const UNAVAILABLE = { line: 'Old-code proof: unavailable.', status: 'unavailable' };
export function judgeOldCodeProof({ content = '', error = '', savedAt } = {}, { runId, startedAt, headSha, baseSha } = {}) {
  if (!sha(headSha) || !sha(baseSha)) return UNAVAILABLE;
  if (error === 'missing') return { line: 'Old-code proof: not run.', status: 'not-run' };
  if (error) return UNAVAILABLE;
  let record;
  try { record = JSON.parse(content); } catch { return UNAVAILABLE; }
  if (!validateProofRecord(record) || !sha(record.baseSha) || !sha(record.headSha) || record.runId !== runId) return UNAVAILABLE;
  if (Number.isFinite(startedAt)) {
    if (!Number.isFinite(savedAt)) return UNAVAILABLE;
    if (savedAt < startedAt) return { line: 'Old-code proof: stale (saved before this run started; rerun pdd workflow prove).', status: 'stale' };
  }
  const head = { headSha, baseSha };
  if (record.headSha !== head.headSha || record.baseSha !== head.baseSha) return { line: 'Old-code proof: stale (base or head changed; rerun pdd workflow prove).', status: 'stale' };
  return { line: formatProof(record), status: record.outcome, record };
}

export function judgeRealValidation(saved, { runId, workflow, headSha, builderSessions = [] } = {}) {
  if (!['bug', 'feature'].includes(workflow)) return { applicable: false, status: 'not-applicable', line: null, reason: null };
  if (saved === null || saved === undefined || (typeof saved === 'object' && saved.error === 'missing')) {
    return { applicable: true, status: 'missing', line: 'Real validation: missing (no real-validation.json recorded for this head).', reason: 'missing fresh-verifier real-validation record (real-validation.json)' };
  }
  let record = saved;
  if (typeof saved === 'object' && typeof saved.content === 'string') {
    if (saved.error) return { applicable: true, status: 'invalid', line: 'Real validation: invalid (real-validation.json could not be read).', reason: 'invalid fresh-verifier real-validation record (real-validation.json could not be read)' };
    try { record = JSON.parse(saved.content); }
    catch { return { applicable: true, status: 'invalid', line: 'Real validation: invalid (real-validation.json is malformed).', reason: 'invalid fresh-verifier real-validation record (real-validation.json is malformed)' }; }
  }
  if (!record || typeof record !== 'object' || Array.isArray(record) || record.unreadable === true) {
    return { applicable: true, status: 'invalid', line: 'Real validation: invalid (real-validation.json is malformed).', reason: 'invalid fresh-verifier real-validation record (real-validation.json is malformed)' };
  }
  const recRunId = record.runId ?? record.run_id;
  if (recRunId !== undefined && runId && recRunId !== runId) {
    return { applicable: true, status: 'invalid', line: 'Real validation: invalid (real-validation.json belongs to another workflow run).', reason: 'real-validation.json belongs to a different workflow run' };
  }
  const head = String(record.head ?? record.headSha ?? '').trim().toLowerCase();
  if (!sha(head)) {
    return { applicable: true, status: 'invalid', line: 'Real validation: invalid (missing 40-character head SHA).', reason: 'real-validation.json is missing a 40-character head SHA' };
  }
  if (typeof headSha === 'string' && sha(headSha.toLowerCase()) && head !== headSha.toLowerCase()) {
    return { applicable: true, status: 'stale', head, headSha: headSha.toLowerCase(), line: `Real validation: stale (recorded for ${head.slice(0, 7)}, current head is ${headSha.slice(0, 7)}).`, reason: `fresh-verifier real-validation record is stale (recorded for ${head.slice(0, 7)}, PR head is ${headSha.slice(0, 7)})` };
  }
  const rawVerifier = typeof record.verifier === 'string' ? record.verifier : typeof record.verifier?.id === 'string' ? record.verifier.id : typeof record.verifier?.session === 'string' ? record.verifier.session : typeof record.session === 'string' ? record.session : '';
  const verifier = rawVerifier.trim();
  if (!verifier) {
    return { applicable: true, status: 'failed', line: 'Real validation: failed (missing fresh verifier identity).', reason: 'real-validation.json is missing a fresh verifier identity' };
  }
  const builders = new Set((builderSessions ?? []).map(item => String(item ?? '').trim()).filter(Boolean));
  if (record.fresh === false || record.verifier?.fresh === false || builders.has(verifier)) {
    return { applicable: true, status: 'failed', line: 'Real validation: failed (verifier reused a builder session instead of a fresh verifier).', reason: 'real-validation.json was recorded by a builder session instead of a fresh verifier' };
  }
  const recipe = (typeof record.recipe === 'string' ? record.recipe : typeof record.recipe?.path === 'string' && record.recipe.path.trim() ? record.recipe.path : typeof record.recipe?.command === 'string' ? record.recipe.command : '').trim();
  if (!recipe) {
    return { applicable: true, status: 'failed', line: 'Real validation: failed (missing verification recipe).', reason: 'real-validation.json is missing the verification recipe used' };
  }
  const oldCode = typeof record.oldCode === 'string' ? { outcome: record.oldCode.trim() } : record.oldCode;
  const oldOutcome = typeof oldCode?.outcome === 'string' ? oldCode.outcome.trim().toLowerCase() : oldCode?.reproduced === true ? 'reproduced' : '';
  const validOld = workflow === 'bug' ? ['reproduced', 'failed', 'fail'].includes(oldOutcome) : ['reproduced', 'failed', 'fail', 'absent', 'baseline'].includes(oldOutcome);
  if (!oldOutcome || oldOutcome === 'setup-error' || !validOld) {
    const target = workflow === 'bug' ? 'bug' : 'missing feature baseline';
    return { applicable: true, status: 'failed', line: `Real validation: failed (old-code run did not reproduce the ${target}).`, reason: `fresh-verifier real-validation old-code run did not reproduce the ${target} (${oldOutcome || 'missing'})` };
  }
  const newCode = typeof record.newCode === 'string' ? { outcome: record.newCode.trim() } : record.newCode;
  const newOutcome = typeof newCode?.outcome === 'string' ? newCode.outcome.trim().toLowerCase() : newCode?.passed === true ? 'passed' : '';
  const newExitOk = newCode?.exitCode === undefined || newCode?.exitCode === 0;
  if (!['passed', 'pass'].includes(newOutcome) || !newExitOk) {
    return { applicable: true, status: 'failed', line: 'Real validation: failed (new-code validation did not pass).', reason: `fresh-verifier real-validation failed on the new code (${newOutcome || 'missing'}${newCode?.exitCode !== undefined ? `, exit ${newCode.exitCode}` : ''})` };
  }
  const evidencePaths = Array.isArray(record.evidencePaths)
    ? record.evidencePaths.filter(item => typeof item === 'string' && item.trim() && !/[\u0000-\u001f]/.test(item) && !item.trim().startsWith('/') && !/^[a-zA-Z]:[\\/]/.test(item.trim()) && !item.split(/[\\/]/).includes('..')).map(item => item.trim())
    : [];
  if (!evidencePaths.length) {
    return { applicable: true, status: 'failed', line: 'Real validation: failed (evidence paths are missing).', reason: 'fresh-verifier real-validation record is missing relative evidence paths' };
  }
  return {
    applicable: true, status: 'passed', head, verifier, recipe,
    oldCode: { ...(typeof oldCode === 'object' ? oldCode : {}), outcome: oldOutcome },
    newCode: { ...(typeof newCode === 'object' ? newCode : {}), outcome: 'passed' },
    evidencePaths,
    line: `Real validation: PASS (head ${head.slice(0, 7)}, recipe ${recipe}, old-code ${oldOutcome}, new-code passed, evidence ${evidencePaths.join(', ')}).`,
    reason: null,
  };
}

export function judgeSuiteReceipt(receipt, { headSha } = {}) {
  if (!receipt) {
    return { status: 'missing', line: `Full-suite receipt: missing${headSha ? ` (no pdd suite receipt for head ${headSha.slice(0, 7)})` : ''}.`, reason: `missing pdd full-suite receipt${headSha ? ` for head ${headSha}` : ''}` };
  }
  if (receipt.state === 'unavailable') {
    return { status: 'unavailable', line: `Full-suite receipt: unavailable (${receipt.reason ?? 'queue unreadable'}).`, reason: `pdd full-suite receipt custody is unavailable (${receipt.reason ?? 'queue unreadable'})` };
  }
  const recHead = typeof receipt.source?.head === 'string' ? receipt.source.head.trim().toLowerCase() : '';
  if (!sha(recHead)) {
    return { status: 'invalid', line: 'Full-suite receipt: invalid (missing 40-character source head SHA).', reason: 'pdd full-suite receipt is missing a 40-character source head SHA' };
  }
  if (typeof headSha === 'string' && sha(headSha.toLowerCase()) && recHead !== headSha.toLowerCase()) {
    return { status: 'stale', head: recHead, headSha: headSha.toLowerCase(), line: `Full-suite receipt: stale (recorded for ${recHead.slice(0, 7)}, current head is ${headSha.slice(0, 7)}).`, reason: `pdd full-suite receipt (ticket ${receipt.ticket ?? 'unknown'}) was recorded for ${recHead.slice(0, 7)}, not PR head ${headSha.slice(0, 7)}` };
  }
  if (receipt.source?.clean === false) {
    return { status: 'dirty', head: recHead, line: `Full-suite receipt: dirty (ticket ${receipt.ticket} for ${recHead.slice(0, 7)} ran on an uncommitted checkout).`, reason: `pdd full-suite receipt (ticket ${receipt.ticket}) for head ${recHead} was recorded on a dirty checkout` };
  }
  if (receipt.state !== 'finished' || receipt.outcome !== 'completed') {
    return { status: 'incomplete', head: recHead, line: `Full-suite receipt: incomplete (ticket ${receipt.ticket}, outcome ${receipt.outcome ?? receipt.state}).`, reason: `pdd full-suite receipt (ticket ${receipt.ticket}) for head ${recHead} is not completed (outcome ${receipt.outcome ?? receipt.state})` };
  }
  const counts = receipt.counts;
  const countsOk = counts && typeof counts === 'object' && Number.isSafeInteger(counts.pass) && counts.pass > 0 && counts.fail === 0 && (counts.cancelled ?? 0) === 0;
  if (receipt.exitCode !== 0 || receipt.signal || !countsOk || typeof receipt.commandFingerprint !== 'string' || !/^[a-f0-9]{64}$/.test(receipt.commandFingerprint)) {
    return { status: 'failed', head: recHead, exitCode: receipt.exitCode ?? null, counts: counts ?? null, line: `Full-suite receipt: FAIL (ticket ${receipt.ticket}, head ${recHead.slice(0, 7)}, exit ${receipt.exitCode ?? 'null'}, pass ${counts?.pass ?? 0}, fail ${counts?.fail ?? 0}).`, reason: `pdd full-suite receipt (ticket ${receipt.ticket}) for head ${recHead} did not pass (exit ${receipt.exitCode ?? 'null'}, pass ${counts?.pass ?? 0}, fail ${counts?.fail ?? 0})` };
  }
  return {
    status: 'passed', ticket: receipt.ticket, head: recHead,
    command: receipt.command ?? '[redacted]', commandFingerprint: receipt.commandFingerprint,
    exitCode: 0, counts, receiptPath: receipt.receiptPath ?? null, logPath: receipt.logPath ?? null,
    line: `Full-suite receipt: PASS (ticket ${receipt.ticket}, head ${recHead.slice(0, 7)}, command sha256:${receipt.commandFingerprint.slice(0, 12)}, pass ${counts.pass}/${counts.tests ?? counts.pass}, fail 0, exit 0).`,
    reason: null,
  };
}

export function findVerificationRecipe(root, fsPort = { lstatSync, readFileSync }) {
  if (!root || typeof root !== 'string') return { present: false, path: null, recipe: null };
  const readText = rel => {
    try {
      const full = join(root, rel);
      if (!fsPort.lstatSync(full).isFile()) return null;
      return fsPort.readFileSync(full, 'utf8');
    } catch { return null; }
  };
  for (const rel of ['docs/verification-recipe.md', 'verification-recipe.md']) {
    const text = readText(rel);
    if (text && text.trim()) return { present: true, path: rel, recipe: rel, content: text };
  }
  for (const rel of ['AGENTS.md', 'CLAUDE.md', 'CONTRIBUTING.md']) {
    const text = readText(rel);
    if (text && /^#{1,3}\s+Verification(?:\s+recipe)?\b[\s\S]*?\S/im.test(text)) {
      return { present: true, path: rel, recipe: `${rel}#Verification`, content: text };
    }
  }
  const pddText = readText('pdd.json');
  if (pddText) {
    try {
      const parsed = JSON.parse(pddText);
      const configured = parsed?.verification?.recipe ?? parsed?.autopilot?.verificationRecipe;
      if (typeof configured === 'string' && configured.trim()) {
        return { present: true, path: 'pdd.json', recipe: configured.trim(), content: configured.trim() };
      }
    } catch {}
  }
  return { present: false, path: null, recipe: null };
}

export async function preparePrEvidence({ run, isCode }, ports = {}) {
  const p = { ...defaults, ...ports }, steps = run.steps.filter(item => safeStep(item.step));
  let notes = [];
  try { notes = (await p.readStepNotes({ runDir: run.runDir, steps: steps.map(item => item.step) })).notes ?? []; } catch { /* Keep stored summaries when notes are unavailable. */ }
  const grouped = new Map(labels.map(label => [label, new Set()]));
  const allowed = (label,step,note) => label==='Review:' ? step==='review' && note : label==='Not fixed yet:' ? ['build','verify'].includes(step) : label==='Not checked:' ? ['check','try','verify','formal','review','reproduce'].includes(step) : label.startsWith('Proof (') ? step==='verify' : run.workflow==='bug' ? step==='reproduce' : run.workflow==='small-change' && step==='scope';
  const scan = (text,step,note=false) => {
    for (const row of String(text ?? '').split(/\r?\n/)) {
      const label = labels.find(label => row.startsWith(label));
      if (!label || !allowed(label,step,note)) continue;
      const payload = row.slice(label.length).trim();
      if (payload) {const rows=grouped.get(label), key=payload.replace(/\.$/,'');if(![...rows].some(row=>row.key===key))rows.add({key,line:`${label} ${safeValue(payload)}`});}
    }
  };
  for (const { step, summary } of steps) {
    scan(summary,step);
    for (const note of notes.filter(note => note.step === step)) scan(note.text,step,true);
  }
  const lines = [];
  let proofStatus = 'not-applicable';
  if (isCode) {
    let line = 'Old-code proof: unavailable.';
    proofStatus = 'unavailable';
    try {
      const head = await p.currentHead({ root: run.root, baseBranch:run.baseBranch });
      const saved = await p.readOldCodeProof({ runDir: run.runDir });
      ({ line, status: proofStatus } = judgeOldCodeProof(saved, { runId: run.runId, startedAt: run.startedAt, headSha: head.error ? '' : head.headSha, baseSha: head.error ? '' : head.baseSha }));
    } catch { /* Publication retains an explicit unavailable result. */ }
    lines.push(line);
  }
  lines.push(...labels.flatMap(label => [...grouped.get(label)].map(row => `Agent note — not checked by pdd: ${row.line}`)));
  const issueReference = `${grouped.get('Not fixed yet:').size ? 'Refs' : isCode ? 'Closes' : 'Part of'} #${run.number}`;
  return { lines, approvalLines: approvalLines(approvalRecords(run)), issueReference, proofStatus };
}

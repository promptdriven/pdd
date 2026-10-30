// Generated from prompts/cli/workflow-pr-evidence.prompt.md (sha256: e0e3e3b683d89f3521777d5613757e6417384177289721e256be4469dc26ec48).
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
      return { content: readFileSync(path, 'utf8'), error: '' };
    } catch (error) { return { content: '', error: error.code === 'ENOENT' ? 'missing' : 'Proof could not be read.' }; }
  }
};

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
  const lines = labels.slice(0, -1).flatMap(label => [...grouped.get(label)].map(row=>row.line));
  let proofStatus = 'not-applicable';
  if (isCode) {
    let line = 'Old-code proof: unavailable.';
    proofStatus = 'unavailable';
    try {
      const head = await p.currentHead({ root: run.root, baseBranch:run.baseBranch });
      const saved = await p.readOldCodeProof({ runDir: run.runDir });
      if (!head.error && sha(head.headSha) && sha(head.baseSha)) {
        if (saved.error === 'missing') { line = 'Old-code proof: not run.'; proofStatus = 'not-run'; }
        else if (!saved.error) {
          const record = JSON.parse(saved.content);
          if (validateProofRecord(record) && sha(record.baseSha) && sha(record.headSha) && record.runId === run.runId) {
            if (record.headSha !== head.headSha || record.baseSha !== head.baseSha) { line = 'Old-code proof: stale (base or head changed; rerun pdd workflow prove).'; proofStatus = 'stale'; }
            else { line = formatProof(record); proofStatus = record.outcome; }
          }
        }
      }
    } catch { /* Publication retains an explicit unavailable result. */ }
    lines.push(line);
  }
  lines.push(...[...grouped.get('Review:')].map(row=>row.line));
  const issueReference = `${grouped.get('Not fixed yet:').size ? 'Refs' : isCode ? 'Closes' : 'Part of'} #${run.number}`;
  return { lines, issueReference, proofStatus };
}

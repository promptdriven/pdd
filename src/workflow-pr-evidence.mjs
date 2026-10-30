// Generated from prompts/cli/workflow-pr-evidence.prompt.md (sha256: 179545d99d51553641672997c85924b642b5c50e243ea2cbca122bcc1e01b398).
import { execFile } from 'node:child_process';
import { lstatSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { formatProof, validateProofRecord } from './workflow-prove.mjs';

const execute = promisify(execFile);
const labels = ['Not fixed yet:', 'Not checked:', 'Defect:', 'Not caught because:', 'Proof (defect fixed):', 'Proof (gap closed):', 'Review:'];
const safeStep = step => typeof step === 'string' && step.length > 0 && !/[\\/\u0000-\u001f]/u.test(step) && step !== '.' && step !== '..';
const sha = value => typeof value === 'string' && /^[a-f0-9]{40}$/.test(value);
const defaults = {
  async currentHead({ root }) {
    try {
      const { stdout } = await execute('git', ['rev-parse', '--verify', 'HEAD^{commit}'], { cwd: root, encoding: 'utf8' });
      const headSha = stdout.trim();
      return sha(headSha) ? { headSha, error: '' } : { headSha: '', error: 'Current Git head unavailable.' };
    } catch { return { headSha: '', error: 'Current Git head unavailable.' }; }
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
  const scan = text => {
    for (const row of String(text ?? '').split(/\r?\n/)) {
      const label = labels.find(label => row.startsWith(label));
      if (!label) continue;
      const payload = row.slice(label.length).trim();
      if (payload) grouped.get(label).add(`${label} ${payload}`);
    }
  };
  for (const { step, summary } of steps) {
    scan(summary);
    for (const note of notes.filter(note => note.step === step)) scan(note.text);
  }
  const lines = labels.slice(0, -1).flatMap(label => [...grouped.get(label)]);
  let proofStatus = 'not-applicable';
  if (isCode) {
    let line = 'Old-code proof: unavailable.';
    proofStatus = 'unavailable';
    try {
      const head = await p.currentHead({ root: run.root });
      const saved = await p.readOldCodeProof({ runDir: run.runDir });
      if (!head.error && sha(head.headSha)) {
        if (saved.error === 'missing') { line = 'Old-code proof: not run.'; proofStatus = 'not-run'; }
        else if (!saved.error) {
          const record = JSON.parse(saved.content);
          if (validateProofRecord(record) && sha(record.baseSha) && sha(record.headSha) && record.runId === run.runId && record.baseSha === run.baseSha) {
            if (record.headSha !== head.headSha) { line = 'Old-code proof: stale (head changed; rerun pdd workflow prove).'; proofStatus = 'stale'; }
            else { line = formatProof(record); proofStatus = record.outcome; }
          }
        }
      }
    } catch { /* Publication retains an explicit unavailable result. */ }
    lines.push(line);
  }
  lines.push(...grouped.get('Review:'));
  const issueReference = `${grouped.get('Not fixed yet:').size ? 'Refs' : isCode ? 'Closes' : 'Part of'} #${run.number}`;
  return { lines, issueReference, proofStatus };
}

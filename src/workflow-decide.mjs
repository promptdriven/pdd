// Shared decision seam for terminal shortcuts, authenticated Link and area chats.
// The public selectors resolve the run and current gate; this module owns the
// common admission shape so another caller cannot bypass the same evidence hook.
const UUID = /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i;
const validStage = value => typeof value === 'string' && /^[a-z][a-z0-9-]{0,63}$/.test(value);
function evidenceStage(run, expectStage) {
  const rows = Array.isArray(run?.steps) ? run.steps : [];
  const row = rows.find(step => step.id === expectStage && step.agent && Number.isFinite(step.startedAt) && Number.isFinite(step.endedAt))
    ?? [...rows].reverse().find(step => step.state === 'done' && step.agent && Number.isFinite(step.startedAt) && Number.isFinite(step.endedAt));
  return { agent: row?.agent ?? run?.agent, root: run?.root, startedAt: row?.startedAt ?? run?.startedAt, endedAt: row?.endedAt ?? run?.updatedAt };
}
async function checkAgentEvidence(input, ports) {
  let checker = ports.readApprovalEvidence ?? ports.approvalEvidence;
  if (typeof checker !== 'function') {
    try { checker = (await import('./approval-evidence.mjs')).readApprovalEvidence; } catch { checker = null; }
  }
  if (typeof checker !== 'function') return { ok: false, code: 'approval_evidence_unavailable', message: 'Approval evidence is unavailable for this agent session.' };
  let answer;
  try {
    answer = await checker({ stage: evidenceStage(ports.run, input.expectStage), gateAskedAt: ports.run?.gateAskedAt ?? ports.run?.updatedAt ?? Date.now(), decision: input.decision }, ports);
  } catch { return { ok: false, code: 'approval_evidence_unavailable', message: 'Approval evidence is unavailable for this agent session.' }; }
  if (answer === true) return { ok: true };
  if (answer?.ok === true) return answer;
  return { ok: false, code: answer?.code ?? 'approval_evidence_unavailable', message: answer?.message ?? 'Approval requires a USER message after the current gate.' };
}
export async function decideWorkflow(input = {}, ports = {}) {
  const { runId, decision, decisionId, expectStage, expectSeq, cwd, packageRoot, text, yes } = input;
  let approvalRecord;
  if (!UUID.test(runId ?? '') || !['approve', 'changes', 'skip'].includes(decision) || !UUID.test(decisionId ?? '')
    || !validStage(expectStage) || !Number.isSafeInteger(expectSeq) || expectSeq < 1 || typeof cwd !== 'string' || typeof packageRoot !== 'string')
    return { exitCode: 2, state: 'refused', code: 'bad_args', runId: runId ?? null, decisionId: decisionId ?? null, decision: decision ?? null, stage: expectStage ?? null, journalSeq: expectSeq ?? null, controller: null, message: 'Decision binding is invalid.' };
  if (decision === 'changes' && (typeof text !== 'string' || [...text].length < 1 || [...text].length > 4000 || /[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]/.test(text)))
    return { exitCode: 2, state: 'refused', code: 'bad_args', runId, decisionId, decision, stage: expectStage, journalSeq: expectSeq, controller: null, message: 'The changes text is invalid.' };
  if (ports.env?.PDD_AGENT_SESSION) {
    const evidence = await checkAgentEvidence(input, ports);
    if (!evidence.ok) return { exitCode: 1, state: 'refused', code: evidence.code, runId, decisionId, decision, stage: expectStage, journalSeq: expectSeq, controller: null, message: evidence.message };
    if (evidence.sessionId || evidence.userMessage || evidence.userMessageAt) approvalRecord = { kind: 'chat', agent: evidence.agent, sessionId: evidence.sessionId, userMessage: evidence.userMessage, userMessageAt: evidence.userMessageAt, at: Date.now() };
  }
  if (decision === 'changes') return { exitCode: 0, state: 'recorded', code: 'unsupported', runId, decisionId, decision, stage: expectStage, journalSeq: expectSeq, controller: null, message: 'Request changes comes in the next release', ...(approvalRecord ? { approvalRecord } : {}) };
  const runner = ports.runner ?? await import('./workflow-runner.mjs');
  const result = await runner.resumeWorkflow({ runId, cwd, packageRoot, decision }, ports.runnerPorts ?? ports);
  return { ...result, state: result.state === 'completed' ? 'started' : result.state, code: result.state === 'waiting' ? 'run_not_waiting' : 'started', decisionId, decision, stage: expectStage, journalSeq: expectSeq, controller: null, ...(approvalRecord ? { approvalRecord } : {}) };
}

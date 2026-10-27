// Generated from prompts/cli/workflow-area-chats.prompt.md (sha256: 8b5a41fef396b44be23f2b14268175533779da818fb6066e9867ea2f2ded04d0).
const AREA_CHATS = Object.freeze({
  'small-change': Object.freeze([
    Object.freeze({ id: 'plan', label: 'Chat 1: plan', stages: Object.freeze(['scope']), gate: 'approve-plan' }),
    Object.freeze({ id: 'build', label: 'Chat 2: build', stages: Object.freeze(['change', 'verify', 'open-pr', 'wait-merge']), gate: 'merge' })
  ])
});
export { AREA_CHATS };

export function areaChatForStage(workflowName, stageId) {
  const areas = AREA_CHATS[workflowName];
  return areas?.find(area => area.stages.includes(stageId)) ?? null;
}
function areaForState(state) {
  if (state.proposal && !state.accepted) return AREA_CHATS[state.name]?.[0] ?? null;
  return areaChatForStage(state.name, state.definitions?.[state.index]?.id)
    ?? [...(state.completed ?? [])].reverse().map(step => areaChatForStage(state.name, step.id)).find(Boolean) ?? null;
}
export function areaChatStatus({ state, base, event = null, now = Date.now() } = {}) {
  if (!state || state.chat !== true) return null;
  const currentArea = areaForState(state);
  const currentStage = state.definitions?.[state.index];
  const gate = currentStage?.kind === 'merge' ? 'merge' : state.proposal && !state.accepted ? 'approve-plan' : null;
  return { ...base, mode: 'area-chats',
    area: currentArea ? { id: currentArea.id, label: currentArea.label, stages: [...currentArea.stages] } : null,
    chat: currentArea?.label ?? null, gate, event, updatedAt: now };
}

// Generated from prompts/cli/runtime-binding-plan.prompt.md (sha256: 5287e914876856ec130dfdbff660f78b68805ea54e6c75760aaa3db373f5f0d6).

const rows = value => Array.isArray(value) ? value : [];
const selectedResources = (iface, operation) => {
  const entries = rows(iface?.entries), selected = entries.filter(entry => entry?.operation === operation);
  const declared = new Set(rows(iface?.resources).flatMap(resource => rows(resource?.operations)
    .map(member => `${resource.name}.${member?.name}`)));
  if (selected.length !== 1 || entries.some(entry => typeof entry?.operation !== 'string' || !entry.operation)
      || new Set(entries.map(entry => entry.operation)).size !== entries.length
      || !entries.every(entry => Array.isArray(entry?.resource_operations)
      && entry.resource_operations.every(name => typeof name === 'string' && declared.has(name))
      && new Set(entry.resource_operations).size === entry.resource_operations.length)) return null;
  if (new Set(entries.flatMap(entry => entry.resource_operations)).size !== declared.size) return null;
  return new Set(selected[0].resource_operations);
};
const boundaryNote = (notes, reason) => {
  notes.push({code:'boundary-not-applied',reason,message:reason === 'legacy-syntax'
    ? 'boundary not applied: use the pdd-boundary block'
    : `boundary not applied: ${reason === 'unsupported-line-ends' ? 'unsupported line ends' : reason}; full dependency closure is required`});
  return null;
};
export function runtimeBoundary(storyPath, text, {notes=[]}={}) {
  // Scope removal needs unambiguous line boundaries throughout the Story.
  // Do not normalize unsupported separators into apparent top-level authority.
  if (/\r(?!\n)|[\v\f\u001c-\u001e\u0085\u2028\u2029]/u.test(text)) {
    return boundaryNote(notes,'unsupported-line-ends');
  }
  const lines = text.split(/\r?\n/);
  // Admission is deliberately stricter than Markdown discovery. Count even
  // unsupported/example markers so uncertain declarations never yield a subset.
  const markers = lines.flatMap((line,index)=>/[`~]{3,}[ \t]*pdd-boundary\b/.test(line) ? [index] : []);
  if (!markers.length) return boundaryNote(notes,/runtime boundary/i.test(text) ? 'legacy-syntax' : 'missing-block');
  if (markers.length !== 1) return boundaryNote(notes,'duplicate-blocks');
  const start = markers[0];
  let fence = null, uncertain = false;
  for (let index=0;index<start;index++) {
    const line=lines[index], match=line.match(/^ {0,3}(`{3,}|~{3,})(.*)$/);
    if (fence) {
      if (match && match[1][0] === fence.char && match[1].length >= fence.length && !match[2].trim()) fence=null;
    } else if (match) fence={char:match[1][0],length:match[1].length};
    else if (/<(?:[!?]|\/?[A-Za-z])/.test(line)) uncertain=true;
  }
  const end=lines.indexOf('```',start+1);
  if (lines[start] !== '```pdd-boundary' || fence || uncertain || end < 0
      || start > 0 && lines[start-1].trim() || end+1 < lines.length && lines[end+1].trim()) {
    return boundaryNote(notes,'unsupported-syntax');
  }
  // Reject HTML after the block too: an enclosing/raw example is not authority.
  if (/<(?:[!?]|\/?[A-Za-z])/.test(lines.slice(end+1).join('\n'))) return boundaryNote(notes,'unsupported-syntax');
  const paths=lines.slice(start+1,end);
  if (!paths.length || paths.some(path=>!/^[A-Za-z0-9_./-]+\.prompt\.md$/.test(path)
      || path.split('/').some(part=>!part || part==='.' || part==='..'))) return boundaryNote(notes,'invalid-path');
  if (/runtime boundary/i.test(text)) boundaryNote(notes,'legacy-syntax');
  return [...new Set(paths)].sort();
}

export function buildBindingPlan({test, storyText, prompts, dependencyPaths=[], boundaryState}) {
  const notes=[];
  const boundary = boundaryState ? boundaryState.boundary : runtimeBoundary(test.storyPath,storyText,{notes});
  if (boundaryState) notes.push(...boundaryState.notes);
  const steps = [], edges = [], problems = [];
  const allowed = path => boundary === null || boundary.includes(path);
  for (const step of rows(test.doc?.steps)) {
    if (!step || typeof step.entry_path !== 'string') continue;
    const closure = new Set(), pending = [step.entry_path, ...(boundary ?? dependencyPaths)];
    for (let index = 0; index < pending.length; index++) {
      const path = pending[index];
      if (closure.has(path)) continue;
      closure.add(path);
      if (!allowed(path)) { problems.push({step_id:step.step_id,prompt_path:path,code:'out-of-boundary'}); continue; }
      const iface = prompts.get(path);
      if (!iface) { problems.push({step_id:step.step_id,prompt_path:path,code:'interface-unavailable'}); continue; }
      for (const call of rows(iface.calls)) if (typeof call?.target==='string') pending.push(call.target);
    }
    steps.push({step_id:step.step_id,closure:[...closure].sort()});
    const simulation = {...test.doc.simulation,...step.simulation_overrides};
    const otherEntryCall = [...closure].some(path => rows(prompts.get(path)?.calls).some(call =>
      call?.target === step.entry_path && call.target_operation !== step.operation));
    const active = otherEntryCall ? null : selectedResources(prompts.get(step.entry_path), step.operation);
    for (const path of [...closure].sort()) {
      if (!allowed(path)) continue;
      for (const resource of rows(prompts.get(path)?.resources)) for (const operation of rows(resource?.operations)) {
        if (typeof resource?.name !== 'string' || typeof operation?.name !== 'string') continue;
        const key = `${resource.name}.${operation.name}`, candidates = [];
        if (path === step.entry_path && active !== null && !active.has(key)) continue;
        for (const [name,binding] of Object.entries(simulation)) {
          const split = name.lastIndexOf('.'), resourceName = name.slice(0,split), operationName = name.slice(split+1);
          const cause = resourceName !== resource.name ? 'wrong-name' : operationName !== operation.name ? 'wrong-operation'
            : !binding || typeof binding !== 'object' || binding.action === 'fixture.lookup' && (!Array.isArray(binding.cases) || !binding.cases.length) ? 'invalid-fixture' : 'selected';
          candidates.push({kind:'simulation',name,cause});
        }
        for (const [candidate,iface] of prompts) for (const entry of rows(iface?.entries)) {
          if (!entry) continue;
          if (entry.operation !== operation.name) continue;
          candidates.push({kind:'prompt',name:`${candidate}#${entry.operation}`,
            cause:!allowed(candidate)?'out-of-boundary':!closure.has(candidate)?'not-in-dependency-closure':'wrong-name'});
        }
        const internal = ['key-value','collection','blob','sql','compute'].includes(resource.kind);
        const state = candidates.some(candidate=>candidate.cause==='selected') ? 'bound' : internal ? 'internal' : 'missing';
        const rename = candidates.some(candidate=>candidate.kind==='simulation' && ['wrong-name','wrong-operation'].includes(candidate.cause)
          && (candidate.name.startsWith(`${resource.name}.`) || candidate.name.endsWith(`.${operation.name}`)));
        const repair = state !== 'missing' ? null : rename ? `Fix the fixture name or operation to ${key}.`
          : `Add a binding for ${key}; if this module is context only, declare the Story pdd-boundary block.`;
        edges.push({step_id:step.step_id,prompt_path:path,resource:resource.name,operation:operation.name,key,state,candidates,repair});
      }
    }
  }
  return {schema_version:'pdd.binding-plan.v1',test:test.path,story:test.storyPath,boundary,notes,steps,edges,problems};
}

export function bindingPlanLines(plan) {
  return [`Bindings: ${plan.test}; boundary: ${plan.boundary?.join(', ') ?? 'full dependency closure'}`,
    ...plan.edges.map(edge=>`${edge.step_id}: ${edge.prompt_path}: ${edge.key}: ${edge.state}; considered: ${edge.candidates.map(candidate=>`${candidate.kind} ${candidate.name} (${candidate.cause})`).join(', ') || 'none'}${edge.repair ? `; repair: ${edge.repair}` : ''}`),
    ...(plan.notes ?? []).map(note=>`${note.code}: ${note.message}`),
    ...plan.problems.map(problem=>`${problem.step_id}: ${problem.prompt_path}: ${problem.code}; repair: correct the declared boundary or Runtime call target.`)];
}

export function bindingRefusals(plan, compatibility) {
  return (compatibility?.reported?.edges ?? []).filter(edge=>edge.reason_code==='binding-missing').map(edge=>{
    const {step_id,prompt_path}=edge.selection, key=edge.selection.edge.resource_operation;
    const local=plan.edges.find(row=>row.step_id===step_id && row.prompt_path===prompt_path && row.key===key);
    const closure=plan.steps.find(row=>row.step_id===step_id)?.closure ?? [];
    const cause=plan.boundary && !plan.boundary.includes(prompt_path) ? 'out-of-boundary'
      : !closure.includes(prompt_path) ? 'not-in-dependency-closure'
      : local?.state==='bound' ? 'server-binding-disagreement'
      : local?.candidates.find(candidate=>candidate.kind==='simulation' && (candidate.name.startsWith(`${local.resource}.`) || candidate.name.endsWith(`.${local.operation}`)))?.cause ?? 'binding-missing';
    const repair=cause==='server-binding-disagreement' ? `The exact fixture ${key} is selected locally. Ask the compatibility owner to diagnose fixture selection before retrying.`
      : ['out-of-boundary','not-in-dependency-closure'].includes(cause) ? 'Check the declared Story Runtime boundary and compatibility closure before retrying.'
      : local?.repair ?? `Add a binding for ${key}.`;
    return {step_id,prompt_path,key,cause,candidates:local?.candidates ?? [],repair};
  });
}

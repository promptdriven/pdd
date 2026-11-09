// Generated from prompts/cli/runtime-binding-plan.prompt.md (sha256: 668730e6cf3fd4bc747861525aeb304c577d9eb6a5fe92d68bda40c988421e91).
import { posix } from 'node:path';

const rows = value => Array.isArray(value) ? value : [];
const invalid = detail => { throw Object.assign(Error(`binding-boundary-invalid: ${detail}`), {code:'binding-boundary-invalid'}); };
export function runtimeBoundary(storyPath, text) {
  const sections = [...text.matchAll(/^## Runtime boundary\s*\r?\n([\s\S]*?)(?=^## |$(?![\s\S]))/gm)];
  if (!sections.length) return null;
  if (sections.length !== 1) invalid('declare one Runtime boundary section');
  const paths = [...sections[0][1].matchAll(/\[[^\]\n]*\]\(([^)\s]+)\)/g)].map(match => {
    const raw = match[1].split('#')[0];
    if (!raw || /[:\\%]/.test(raw) || raw.startsWith('/')) invalid('use relative local prompt links');
    const path = posix.normalize(posix.join(posix.dirname(storyPath), raw));
    if (path.startsWith('../') || !path.endsWith('.prompt.md')) invalid('use in-repository .prompt.md paths');
    return path;
  });
  if (!paths.length) invalid('name the executable prompts with Markdown links');
  return [...new Set(paths)].sort();
}

export function buildBindingPlan({test, storyText, prompts}) {
  const boundary = runtimeBoundary(test.storyPath, storyText), steps = [], edges = [], problems = [];
  const allowed = path => boundary === null || boundary.includes(path);
  for (const step of rows(test.doc?.steps)) {
    if (!step || typeof step.entry_path !== 'string') continue;
    const closure = new Set(), pending = [step.entry_path];
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
    for (const path of [...closure].sort()) {
      if (!allowed(path)) continue;
      for (const resource of rows(prompts.get(path)?.resources)) for (const operation of rows(resource?.operations)) {
        if (typeof resource?.name !== 'string' || typeof operation?.name !== 'string') continue;
        const key = `${resource.name}.${operation.name}`, candidates = [];
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
          : `Add a binding for ${key}; if this module is context only, declare the Story Runtime boundary.`;
        edges.push({step_id:step.step_id,prompt_path:path,resource:resource.name,operation:operation.name,key,state,candidates,repair});
      }
    }
  }
  return {schema_version:'pdd.binding-plan.v1',test:test.path,story:test.storyPath,boundary,steps,edges,problems};
}

export function bindingPlanLines(plan) {
  return [`Bindings: ${plan.test}; boundary: ${plan.boundary?.join(', ') ?? 'entry and Runtime calls'}`,
    ...plan.edges.map(edge=>`${edge.step_id}: ${edge.prompt_path}: ${edge.key}: ${edge.state}; considered: ${edge.candidates.map(candidate=>`${candidate.kind} ${candidate.name} (${candidate.cause})`).join(', ') || 'none'}${edge.repair ? `; repair: ${edge.repair}` : ''}`),
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

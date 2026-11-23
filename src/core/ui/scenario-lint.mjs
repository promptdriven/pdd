// Generated from prompts/cli/svg-layout.prompt.md.
// Scenario schema_version, simulation/override alignment, and native-only dependency preflight.
import { dirname, relative, resolve, sep } from 'node:path';
import { compileScenario, isShortScenarioDoc, needsScenarioCompile, V1_SCENARIO_SCHEMA } from '../../scenario-compile.mjs';
import { workspace } from '../../shared/workspace-policy.mjs';
import { hasPointer, isFixturePath, setPointer } from './app-map-lint.mjs';
import { escaped } from './svg-controls.mjs';

const ROOT_PLACEHOLDER = '/__pdd_root__';
const PORT_OP_RE = /^[A-Za-z][A-Za-z0-9_-]*\.[A-Za-z][A-Za-z0-9_-]*$/;

function proseMentionsPortOp(prose, opKey) {
  if (prose.includes(opKey)) return true;
  const dot = opKey.indexOf('.');
  if (dot <= 0) return false;
  const port = opKey.slice(0, dot);
  const op = opKey.slice(dot + 1);
  const portRe = new RegExp(`(?<![A-Za-z0-9_-])${escaped(port)}(?![A-Za-z0-9_-])`, 'i');
  const opRe = new RegExp(`(?<![A-Za-z0-9_-])${escaped(op)}(?![A-Za-z0-9_-])`, 'i');
  return portRe.test(prose) && opRe.test(prose);
}

function resolveInitialWorld(root, testFile, initialWorld, safeRead) {
  if (!initialWorld || typeof initialWorld !== 'object' || Array.isArray(initialWorld)) {
    return { resolvable: true, world: initialWorld };
  }
  if (typeof initialWorld.$seed !== 'string') return { resolvable: true, world: initialWorld };
  const rawSeed = initialWorld.$seed.trim();
  if (!rawSeed) return { resolvable: false, world: null };
  let seedDoc = null;
  const relCandidate = relative(ROOT_PLACEHOLDER, resolve(dirname(resolve(ROOT_PLACEHOLDER, testFile)), rawSeed)).split(sep).join('/');
  for (const candidate of [...new Set([rawSeed, relCandidate])]) {
    try {
      seedDoc = JSON.parse(safeRead(root, candidate));
      break;
    } catch { /* try fallback or mark unresolvable */ }
  }
  if (!seedDoc || typeof seedDoc !== 'object') return { resolvable: false, world: null };
  const world = structuredClone(seedDoc);
  if (initialWorld.set && typeof initialWorld.set === 'object' && !Array.isArray(initialWorld.set)) {
    for (const [ptr, val] of Object.entries(initialWorld.set)) {
      if (ptr === '') continue;
      setPointer(world, ptr, val);
    }
  }
  for (const [k, v] of Object.entries(initialWorld)) {
    if (k === '$seed' || k === 'set') continue;
    Object.defineProperty(world, k, { value: v, writable: true, enumerable: true, configurable: true });
  }
  return { resolvable: true, world };
}

function schemaAllowsPointer(schema, pointer) {
  if (typeof pointer !== 'string' || pointer === '') return true;
  if (!pointer.startsWith('/')) return false;
  const walk = (cur, segs) => {
    if (!segs.length || !cur || typeof cur !== 'object') return true;
    for (const union of ['oneOf', 'anyOf']) {
      if (Array.isArray(cur[union])) return cur[union].some(branch => walk(branch, segs));
    }
    const kind = cur.type;
    if (Array.isArray(kind)) return kind.some(candidate => walk({ ...cur, type: candidate }, segs));
    const token = segs[0].replaceAll('~1', '/').replaceAll('~0', '~');
    const rest = segs.slice(1);
    if (kind === 'object') {
      const props = cur.properties && typeof cur.properties === 'object' ? cur.properties : {};
      if (Object.hasOwn(props, token)) return walk(props[token], rest);
      return cur.additionalProperties !== false;
    }
    if (kind === 'array') {
      if (!/^(?:0|[1-9]\d*)$/.test(token)) return false;
      const items = cur.items;
      return items && typeof items === 'object' ? walk(items, rest) : true;
    }
    if (kind === undefined || kind === null) return true;
    return false;
  };
  return walk(schema, pointer.slice(1).split('/'));
}

export function lintScenarioFiles({
  root,
  files,
  policy,
  promptFilter,
  visiblePromptSet,
  testJsonPaths,
  parsedTests,
  parsedAppMaps,
  safeRead,
  getMeta,
  collectClosure,
  warnings,
}) {
  const storyFiles = files.filter(
    p =>
      p.endsWith('.md') &&
      p.split('/').slice(0, -1).includes('user_stories') &&
      !['plan.md', 'readme.md'].includes(p.split('/').at(-1).toLowerCase()),
  );
  const storyPathByStem = new Map();
  for (const sp of storyFiles) {
    const stem = sp.split('/').at(-1).slice(0, -3);
    if (!storyPathByStem.has(stem)) storyPathByStem.set(stem, sp);
  }
  const checkableScenarioEntries = new Set();

  const summarizeClosure = closureSet => {
    const resources = new Map();
    const resultSchemas = new Map();
    const addResourceAccess = (key, access, resultSchema) => {
      if (typeof key !== 'string' || !key) return;
      if (!resources.has(key)) resources.set(key, new Set());
      if (typeof access === 'string' && access) resources.get(key).add(access);
      if (resultSchema && typeof resultSchema === 'object' && !resultSchemas.has(key)) resultSchemas.set(key, resultSchema);
    };
    let hasPlainPrompt = false;
    const proseChunks = [];
    for (const p of closureSet) {
      const meta = getMeta(p);
      if (!meta) continue;
      proseChunks.push(meta.prose);
      if (!meta.hasEmbeddedInterface) hasPlainPrompt = true;
      for (const res of Array.isArray(meta.iface?.resources) ? meta.iface.resources : []) {
        if (res?.kind === 'port' && typeof res.name === 'string' && Array.isArray(res.operations)) {
          for (const op of res.operations) {
            if (typeof op?.name === 'string' && op.name) {
              addResourceAccess(`${res.name}.${op.name}`, op.access ?? res.access, op.result_schema ?? op.output_schema ?? null);
            }
          }
        } else if (typeof res?.operation === 'string') {
          addResourceAccess(res.operation, res.access, res.result_schema ?? res.output_schema ?? null);
        }
      }
    }
    return { resources, resultSchemas, hasPlainPrompt, combinedProse: proseChunks.join('\n') };
  };

  for (const testFile of testJsonPaths) {
    const isFixtureJson = isFixturePath(testFile);
    const baseStem = testFile.split('/').at(-1).slice(0, -5);
    const primaryStem = baseStem.split('.')[0];
    const isCasesJson = baseStem === 'cases' || baseStem.endsWith('-cases');
    const pairedStoryPath = !isFixtureJson && !isCasesJson
      ? (storyPathByStem.get(baseStem) ?? storyPathByStem.get(primaryStem) ?? null)
      : null;
    const pairedWithStory = pairedStoryPath !== null;
    const cached = parsedTests.get(testFile);
    if (!cached || cached.error) {
      if (pairedWithStory && !promptFilter) {
        const text = `Warning: ${testFile}: scenario test file is not valid JSON; fix JSON syntax (omit "schema_version" for compact scenario JSON or set "schema_version": "prompt-runtime.program-scenario.v1").`;
        warnings.push({ key: `${testFile}\0testjson`, text });
      }
      continue;
    }
    let doc = cached.doc;
    const isNativeCaseDoc = isCasesJson || Array.isArray(doc?.cases) || /^pdd\.native-cases\./.test(String(doc?.schema_version ?? ''));
    let shortCompileHandled = false;
    if (
      !isFixtureJson &&
      !isNativeCaseDoc &&
      doc &&
      typeof doc === 'object' &&
      !Array.isArray(doc) &&
      needsScenarioCompile(doc)
    ) {
      shortCompileHandled = isShortScenarioDoc(doc);
      const targetStoryPath = typeof doc.story_path === 'string' && doc.story_path ? doc.story_path : pairedStoryPath;
      let storySource = null;
      if (typeof targetStoryPath === 'string' && workspace.allows(policy, targetStoryPath)) {
        try { storySource = safeRead(root, targetStoryPath); } catch { storySource = null; }
      }
      const compiled = compileScenario(doc, { path: testFile, storyPath: pairedStoryPath, storySource });
      const candidateSteps = Array.isArray(doc.steps) ? doc.steps : [];
      const matchesShortFilter = !promptFilter
        || (typeof doc.entry_path === 'string' && promptFilter.has(doc.entry_path))
        || candidateSteps.some(s => typeof s?.entry_path === 'string' && promptFilter.has(s.entry_path));
      if (compiled.refusal) {
        if (matchesShortFilter) {
          const r = compiled.refusal;
          const loc = r.section ? ` (${r.section})` : '';
          const text = `Warning: ${testFile}${loc}: compact scenario compile failed [${r.code}]: ${r.message}`;
          warnings.push({ key: `${testFile}\0shortrefusal\0${r.code}`, text });
        }
      } else {
        if (matchesShortFilter) {
          for (const w of Array.isArray(compiled.warnings) ? compiled.warnings : []) {
            const msg = typeof w?.message === 'string' && w.message.trim() ? w.message.trim() : null;
            if (msg) warnings.push({ key: `${testFile}\0shortwarn\0${msg}`, text: msg });
          }
        }
        doc = compiled.doc;
      }
    }
    const looksLikeScenario = !isFixtureJson && !isNativeCaseDoc && doc && typeof doc === 'object' && !Array.isArray(doc) && (
      pairedWithStory
      || typeof doc.story_path === 'string'
      || (Array.isArray(doc.steps) && doc.steps.some(s => s && typeof s === 'object' && (typeof s.entry_path === 'string' || typeof s.operation === 'string') && Array.isArray(s.checks)))
    );
    if (looksLikeScenario && !shortCompileHandled && doc.schema_version !== V1_SCENARIO_SCHEMA) {
      const candidateSteps = Array.isArray(doc.steps) ? doc.steps : [];
      const matchesFilter = !promptFilter || candidateSteps.some(s => typeof s?.entry_path === 'string' && promptFilter.has(s.entry_path));
      if (matchesFilter) {
        const text = `Warning: ${testFile}: scenario schema_version ${JSON.stringify(doc.schema_version ?? null)} is invalid; omit "schema_version" for compact scenario JSON or set "schema_version": "prompt-runtime.program-scenario.v1".`;
        warnings.push({ key: `${testFile}\0testschema`, text });
      }
    }
    if (isFixtureJson || isNativeCaseDoc || !doc || typeof doc !== 'object' || doc.schema_version !== V1_SCENARIO_SCHEMA || !Array.isArray(doc.steps)) continue;
    for (const mapCandidate of Array.isArray(doc.app_maps) ? doc.app_maps : []) {
      const mapDoc = typeof mapCandidate === 'string' ? parsedAppMaps.get(mapCandidate) : null;
      if (!mapDoc) continue;
      for (const s of Array.isArray(mapDoc.screens) ? mapDoc.screens : []) {
        if (typeof s?.prompt_path === 'string' && visiblePromptSet.has(s.prompt_path) && !getMeta(s.prompt_path)?.isNativeOnly) checkableScenarioEntries.add(s.prompt_path);
      }
      for (const h of Array.isArray(mapDoc.handlers) ? mapDoc.handlers : []) {
        const hp = h?.handler?.prompt_path;
        if (typeof hp === 'string' && visiblePromptSet.has(hp) && !getMeta(hp)?.isNativeOnly) checkableScenarioEntries.add(hp);
      }
      for (const t of Array.isArray(mapDoc.timers) ? mapDoc.timers : []) {
        const tp = t?.handler?.prompt_path;
        if (typeof tp === 'string' && visiblePromptSet.has(tp) && !getMeta(tp)?.isNativeOnly) checkableScenarioEntries.add(tp);
      }
    }
    const inRepoSteps = doc.steps.filter(step => step && typeof step.entry_path === 'string' && visiblePromptSet.has(step.entry_path));
    for (const step of inRepoSteps) {
      if (!getMeta(step.entry_path)?.isNativeOnly) checkableScenarioEntries.add(step.entry_path);
    }
    if (!inRepoSteps.length) continue;
    const stepClosures = new Map();
    const allClosurePrompts = new Set();
    for (const step of inRepoSteps) {
      if (!stepClosures.has(step.entry_path)) stepClosures.set(step.entry_path, collectClosure(step.entry_path));
      for (const p of stepClosures.get(step.entry_path)) allClosurePrompts.add(p);
    }
    if (promptFilter && ![...allClosurePrompts].some(p => promptFilter.has(p))) continue;
    const resolvedWorld = resolveInitialWorld(root, testFile, doc.initial_world, safeRead);
    const criteriaById = new Map(
      (Array.isArray(doc.criteria) ? doc.criteria : [])
        .filter(c => c && typeof c.id === 'string')
        .map(c => [c.id, typeof c.text === 'string' ? c.text : '']),
    );
    const wholeSummary = summarizeClosure(allClosurePrompts);
    if (doc.simulation && typeof doc.simulation === 'object' && !Array.isArray(doc.simulation)) {
      for (const [opKey, rawSim] of Object.entries(doc.simulation)) {
        if (!PORT_OP_RE.test(opKey)) {
          if (wholeSummary.hasPlainPrompt) {
            warnings.push({ key: `${testFile}\0simfmt\0${opKey}`, text: `Warning: ${testFile}: simulation key "${opKey}" must have <port>.<operation> form` });
          }
          continue;
        }
        if (wholeSummary.hasPlainPrompt && !wholeSummary.resources.has(opKey) && !proseMentionsPortOp(wholeSummary.combinedProse, opKey)) {
          warnings.push({ key: `${testFile}\0simprose\0${opKey}`, text: `Warning: ${testFile}: simulation port "${opKey}" is not mentioned in reachable prompt prose; name ${opKey} explicitly so lazy interface synthesis binds the port` });
        }
        const simBinding = rawSim?.binding && typeof rawSim.binding === 'object' ? rawSim.binding : rawSim;
        const rvp = typeof simBinding?.result_value_pointer === 'string' ? simBinding.result_value_pointer : null;
        if (rvp !== null) {
          const rSchema = wholeSummary.resultSchemas.get(opKey);
          if (rSchema && !schemaAllowsPointer(rSchema, rvp)) {
            warnings.push({ key: `${testFile}\0simrvpschema\0${opKey}`, text: `Warning: ${testFile}: simulation "${opKey}" result_value_pointer "${rvp}" is excluded by "${opKey}" result_schema (impossible-result-value-pointer)` });
          }
          if (rvp !== '' && simBinding && Object.hasOwn(simBinding, 'result_template') && !hasPointer(simBinding.result_template, rvp)) {
            warnings.push({ key: `${testFile}\0simrvptpl\0${opKey}`, text: `Warning: ${testFile}: simulation "${opKey}" result_template is missing result_value_pointer "${rvp}" (missing-result-placeholder)` });
          }
        }
      }
    }
    for (const [idx, step] of doc.steps.entries()) {
      const overrides = step?.simulation_overrides;
      if (!overrides || typeof overrides !== 'object' || typeof step.entry_path !== 'string' || !visiblePromptSet.has(step.entry_path)) continue;
      const stepLabel = typeof step.step_id === 'string' && step.step_id ? step.step_id : `steps[${idx}]`;
      const summary = summarizeClosure(stepClosures.get(step.entry_path) ?? collectClosure(step.entry_path));
      const checkedIds = new Set((Array.isArray(step.checks) ? step.checks : []).map(ch => ch?.criterion_id).filter(Boolean));
      const entries = Array.isArray(overrides)
        ? overrides.filter(row => row && typeof row === 'object').map((row, rowIdx) => ({
            opKey: typeof row.operation === 'string' ? row.operation : '',
            binding: row.binding && typeof row.binding === 'object' ? row.binding : row,
            cid: typeof row.criterion_id === 'string' ? row.criterion_id : '',
            fquote: typeof row.failure_quote === 'string' ? row.failure_quote : '',
            rowKey: String(rowIdx),
          }))
        : Object.entries(overrides).map(([opKey, binding]) => ({
            opKey,
            binding: binding?.binding && typeof binding.binding === 'object' ? binding.binding : binding,
            cid: typeof binding?.criterion_id === 'string' ? binding.criterion_id : '',
            fquote: typeof binding?.failure_quote === 'string' ? binding.failure_quote : '',
            rowKey: opKey,
          }));
      if (!Array.isArray(overrides)) {
        warnings.push({ key: `${testFile}\0ovshape\0${stepLabel}`, text: `Warning: ${testFile} (${stepLabel}): simulation_overrides should be an array of {operation, criterion_id, failure_quote, reason, binding} objects` });
      }
      for (const { opKey, binding, cid, fquote, rowKey } of entries) {
        if (!PORT_OP_RE.test(opKey)) {
          warnings.push({ key: `${testFile}\0ovfmt\0${stepLabel}\0${rowKey}`, text: `Warning: ${testFile} (${stepLabel}): simulation_overrides operation "${opKey}" must have <port>.<operation> form` });
          continue;
        }
        const declared = summary.resources.get(opKey);
        if (!declared) {
          if (!summary.hasPlainPrompt) {
            warnings.push({ key: `${testFile}\0ovres\0${stepLabel}\0${rowKey}`, text: `Warning: ${testFile} (${stepLabel}): simulation_overrides port "${opKey}" is not declared in reachable Runtime interface resources for ${step.entry_path}` });
          } else if (!proseMentionsPortOp(summary.combinedProse, opKey)) {
            warnings.push({ key: `${testFile}\0ovprose\0${stepLabel}\0${rowKey}`, text: `Warning: ${testFile} (${stepLabel}): simulation_overrides port "${opKey}" is not mentioned in reachable prompt prose (${step.entry_path}); name ${opKey} explicitly so lazy interface synthesis binds the port` });
          }
        } else if (binding?.action === 'port.write' && !declared.has('read') && !declared.has('write') && !declared.has('read_write')) {
          warnings.push({ key: `${testFile}\0ovacc\0${stepLabel}\0${rowKey}`, text: `Warning: ${testFile} (${stepLabel}): port.write simulation_overrides on "${opKey}" requires read or write port access in reachable Runtime interface resources` });
        }
        if (binding?.action === 'port.write' && typeof binding.world_pointer === 'string' && resolvedWorld.resolvable && !hasPointer(resolvedWorld.world, binding.world_pointer)) {
          warnings.push({ key: `${testFile}\0ovwp\0${stepLabel}\0${rowKey}`, text: `Warning: ${testFile} (${stepLabel}): simulation_overrides "${opKey}" world_pointer "${binding.world_pointer}" is missing from initial_world` });
        }
        const ovRvp = typeof binding?.result_value_pointer === 'string' ? binding.result_value_pointer : null;
        if (ovRvp !== null) {
          const ovSchema = summary.resultSchemas.get(opKey);
          if (ovSchema && !schemaAllowsPointer(ovSchema, ovRvp)) {
            warnings.push({ key: `${testFile}\0ovrvpschema\0${stepLabel}\0${rowKey}`, text: `Warning: ${testFile} (${stepLabel}): simulation_overrides "${opKey}" result_value_pointer "${ovRvp}" is excluded by "${opKey}" result_schema (impossible-result-value-pointer)` });
          }
          if (ovRvp !== '' && binding && Object.hasOwn(binding, 'result_template') && !hasPointer(binding.result_template, ovRvp)) {
            warnings.push({ key: `${testFile}\0ovrvptpl\0${stepLabel}\0${rowKey}`, text: `Warning: ${testFile} (${stepLabel}): simulation_overrides "${opKey}" result_template is missing result_value_pointer "${ovRvp}" (missing-result-placeholder)` });
          }
        }
        if (!cid || !checkedIds.has(cid)) {
          warnings.push({ key: `${testFile}\0ovcid\0${stepLabel}\0${rowKey}`, text: `Warning: ${testFile} (${stepLabel}): simulation_overrides "${opKey}" criterion_id "${cid}" is not checked by step ${stepLabel}` });
        } else if (fquote.trim() && !criteriaById.get(cid)?.includes(fquote)) {
          warnings.push({ key: `${testFile}\0ovfq\0${stepLabel}\0${rowKey}`, text: `Warning: ${testFile} (${stepLabel}): simulation_overrides "${opKey}" failure_quote "${fquote}" is absent from criterion ${cid}` });
        }
      }
    }
  }

  const storyReachablePrompts = new Set();
  for (const entry of checkableScenarioEntries) {
    const closure = collectClosure(entry);
    if (promptFilter && ![...closure].some(p => promptFilter.has(p))) continue;
    for (const p of closure) storyReachablePrompts.add(p);
  }
  for (const prompt of [...storyReachablePrompts].sort()) {
    if (promptFilter && !promptFilter.has(prompt)) continue;
    const meta = getMeta(prompt);
    if (!meta || meta.isNativeOnly || (meta.hasEmbeddedInterface && !meta.hasFrontmatter)) continue;
    for (const dep of collectClosure(prompt)) {
      if (dep === prompt) continue;
      if (getMeta(dep)?.isNativeOnly) {
        warnings.push({ key: `${prompt}\0native\0${dep}`, text: `Warning: ${prompt}: checkable prompt links kind: native-only prompt ${dep} (invert the dependency and inject a <port>.<op> port so Story checks do not skip)` });
      }
    }
  }
}

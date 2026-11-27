// Generated from prompts/cli/svg-layout.prompt.md.
// Single-pass test-JSON / app-map discovery and app-map structural schema/timer/state_schema preflight.
import { workspace } from '../../shared/workspace-policy.mjs';

export const APP_MAP_PATH_RE = /(?:^|\/)(?:app-map\.json|app\/maps\/[^/]+\.json)$/;
export const APP_MAP_SCHEMA_VERSIONS = new Set(['prompt-runtime.app-map.v1', 'prompt-runtime.app-map.v2']);
export const TEST_JSON_PATH_RE = /^(?:tests?|.*\/tests?)\/.*\.json$/;
export const isFixturePath = path => /(?:^|\/)fixtures\//.test(path);
export const isValidAppMapSchemaVersion = doc => !Object.hasOwn(doc, 'schema_version') || APP_MAP_SCHEMA_VERSIONS.has(doc.schema_version);

const MAX_SAFE_TIMER_INT = 9007199254740991;

export function readPointer(obj, pointer) {
  if (typeof pointer !== 'string') return { found: false, value: undefined };
  if (pointer === '') return { found: obj !== undefined, value: obj };
  if (!pointer.startsWith('/')) return { found: false, value: undefined };
  let cur = obj;
  for (const seg of pointer.slice(1).split('/')) {
    if (cur === null || typeof cur !== 'object') return { found: false, value: undefined };
    const key = seg.replaceAll('~1', '/').replaceAll('~0', '~');
    if (Array.isArray(cur)) {
      const idx = Number(key);
      if (!Number.isInteger(idx) || idx < 0 || idx >= cur.length) return { found: false, value: undefined };
      cur = cur[idx];
    } else {
      if (!Object.hasOwn(cur, key)) return { found: false, value: undefined };
      cur = cur[key];
    }
  }
  return { found: true, value: cur };
}

export function readSchemaPointer(stateSchema, pointer) {
  const miss = { exists: false, required: false, schema: null };
  if (!stateSchema || typeof stateSchema !== 'object' || typeof pointer !== 'string' || !pointer.startsWith('/')) return miss;
  const segments = pointer.slice(1).split('/');
  const visit = (cur, idx, required) => {
    if (!cur || typeof cur !== 'object' || Array.isArray(cur)) return miss;
    if (typeof cur.$contract === 'string' || typeof cur.$ref === 'string') return { exists: true, required: false, schema: cur };
    if (idx >= segments.length) return { exists: true, required, schema: cur };
    for (const branch of [...(Array.isArray(cur.oneOf) ? cur.oneOf : []), ...(Array.isArray(cur.anyOf) ? cur.anyOf : []), ...(Array.isArray(cur.allOf) ? cur.allOf : [])]) {
      const branchHit = visit(branch, idx, false);
      if (branchHit.exists) return branchHit;
    }
    const key = segments[idx].replaceAll('~1', '/').replaceAll('~0', '~');
    const types = Array.isArray(cur.type) ? cur.type : typeof cur.type === 'string' ? [cur.type] : [];
    if ((types.includes('array') || cur.items !== undefined || Array.isArray(cur.prefixItems)) && /^(?:0|[1-9][0-9]*|-)$/.test(key)) {
      if (Array.isArray(cur.prefixItems) && key !== '-' && Number(key) < cur.prefixItems.length) return visit(cur.prefixItems[Number(key)], idx + 1, false);
      if (cur.items && typeof cur.items === 'object' && !Array.isArray(cur.items)) return visit(cur.items, idx + 1, false);
      if (cur.items !== false) return { exists: true, required: false, schema: null };
    }
    if (cur.properties && typeof cur.properties === 'object' && Object.hasOwn(cur.properties, key)) {
      return visit(cur.properties[key], idx + 1, required && Array.isArray(cur.required) && cur.required.includes(key));
    }
    if (types.includes('object') || cur.additionalProperties !== undefined) {
      if (cur.additionalProperties === true) return { exists: true, required: false, schema: null };
      if (cur.additionalProperties && typeof cur.additionalProperties === 'object' && !Array.isArray(cur.additionalProperties)) {
        return visit(cur.additionalProperties, idx + 1, false);
      }
      if (!cur.properties && cur.additionalProperties !== false && types.includes('object')) return { exists: true, required: false, schema: null };
    }
    return miss;
  };
  return visit(stateSchema, 0, true);
}

export function hasPointer(obj, pointer) {
  return readPointer(obj, pointer).found;
}

export function setPointer(obj, pointer, value) {
  if (!obj || typeof obj !== 'object' || typeof pointer !== 'string' || !pointer.startsWith('/')) return;
  const segs = pointer.slice(1).split('/').map(s => s.replaceAll('~1', '/').replaceAll('~0', '~'));
  let cur = obj;
  for (let i = 0; i < segs.length - 1; i++) {
    const key = segs[i];
    if (Array.isArray(cur)) {
      const idx = Number(key);
      if (!Number.isInteger(idx) || idx < 0 || idx >= cur.length || cur[idx] === null || typeof cur[idx] !== 'object') return;
      cur = cur[idx];
    } else {
      if (!Object.hasOwn(cur, key) || cur[key] === null || typeof cur[key] !== 'object') {
        Object.defineProperty(cur, key, { value: {}, writable: true, enumerable: true, configurable: true });
      }
      cur = cur[key];
    }
  }
  const last = segs.at(-1);
  if (Array.isArray(cur)) {
    const idx = Number(last);
    if (Number.isInteger(idx) && idx >= 0 && idx <= cur.length) cur[idx] = value;
  } else {
    Object.defineProperty(cur, last, { value, writable: true, enumerable: true, configurable: true });
  }
}

export function discoverTestAndAppMaps({ root, files, policy, safeRead }) {
  const testJsonPaths = files.filter(path => TEST_JSON_PATH_RE.test(path));
  const parsedTests = new Map();
  const mapPaths = new Set(files.filter(path => !isFixturePath(path) && APP_MAP_PATH_RE.test(path)));

  for (const testFile of testJsonPaths) {
    let doc = null;
    let error = null;
    try {
      doc = JSON.parse(safeRead(root, testFile));
    } catch (err) {
      error = err;
    }
    parsedTests.set(testFile, { doc, error });
    if (!isFixturePath(testFile) && Array.isArray(doc?.app_maps)) {
      for (const candidate of doc.app_maps) {
        const normalized = typeof candidate === 'string' ? candidate.trim().replace(/^\.\//, '') : '';
        if (normalized && !isFixturePath(normalized) && workspace.allows(policy, normalized)) {
          mapPaths.add(normalized);
        }
      }
    }
  }

  const parsedAppMaps = new Map();
  const appMapParseErrors = new Set();
  for (const mapPath of [...mapPaths].sort()) {
    try {
      const mapDoc = JSON.parse(safeRead(root, mapPath));
      parsedAppMaps.set(mapPath, mapDoc);
    } catch {
      appMapParseErrors.add(mapPath);
    }
  }
  return { testJsonPaths, parsedTests, mapPaths, parsedAppMaps, appMapParseErrors };
}

export function lintAppMaps({
  root,
  safeRead,
  promptFilter,
  appMapFilter = null,
  parsedAppMaps,
  appMapParseErrors,
  mapPaths,
  promptExists,
  promptDeclaresOp,
  warnings,
}) {
  let inspectedCount = 0;
  for (const mapPath of [...mapPaths].sort()) {
    if (appMapFilter && !appMapFilter.has(mapPath)) continue;
    if (appMapParseErrors.has(mapPath)) {
      if (appMapFilter || !promptFilter) {
        inspectedCount++;
        const text = `Warning: ${mapPath}: app-map.json is not valid JSON; fix syntax (omit "schema_version" for compact app-map.json or set "schema_version": "prompt-runtime.app-map.v1").`;
        warnings.push({ key: `${mapPath}\0mapjson`, text });
      }
      continue;
    }
    const mapDoc = parsedAppMaps.get(mapPath);
    if (!mapDoc || typeof mapDoc !== 'object' || Array.isArray(mapDoc)) continue;
    const screenEntries = Array.isArray(mapDoc.screens)
      ? mapDoc.screens.map((s, idx) => [s, idx]).filter(([s]) => s && typeof s === 'object' && !Array.isArray(s))
      : [];
    const timers = Array.isArray(mapDoc.timers) ? mapDoc.timers : [];
    const handlers = Array.isArray(mapDoc.handlers) ? mapDoc.handlers : [];
    if (!appMapFilter && promptFilter) {
      const referenced = new Set([
        ...screenEntries.map(([s]) => s.prompt_path).filter(p => typeof p === 'string'),
        ...handlers.map(h => h?.handler?.prompt_path).filter(p => typeof p === 'string'),
        ...timers.map(t => t?.handler?.prompt_path).filter(p => typeof p === 'string'),
      ]);
      if (![...referenced].some(p => promptFilter.has(p))) continue;
    }
    inspectedCount++;
    if (Object.hasOwn(mapDoc, 'schema_version') && !APP_MAP_SCHEMA_VERSIONS.has(mapDoc.schema_version)) {
      const text = `Warning: ${mapPath}: app-map schema_version ${JSON.stringify(mapDoc.schema_version ?? null)} is invalid; set "schema_version": "prompt-runtime.app-map.v1" (or omit it for compact app-map.json).`;
      warnings.push({ key: `${mapPath}\0mapschema`, text });
    }
    if (!screenEntries.length && (appMapFilter || !promptFilter)) {
      const text = `Warning: ${mapPath}: app-map.json must declare a non-empty "screens" array.`;
      warnings.push({ key: `${mapPath}\0mapscreens`, text });
    }
    const validScreenIds = new Set();
    const screenPromptById = new Map();
    for (const [screen, sIdx] of screenEntries) {
      const sId = typeof screen.id === 'string' && screen.id ? screen.id : (sIdx === 0 ? 'main' : `screen-${sIdx + 1}`);
      if (sId !== '*') validScreenIds.add(sId);
      if (typeof screen.prompt_path === 'string' && screen.prompt_path.trim()) {
        screenPromptById.set(sId, screen.prompt_path);
        if (!promptExists(screen.prompt_path)) {
          const text = `Warning: ${mapPath} (screen "${sId}"): screen prompt_path "${screen.prompt_path}" does not exist in Git-visible prompts; point prompt_path to an existing prompts/*.prompt.md file and run git add.`;
          warnings.push({ key: `${mapPath}\0mapscreen\0${sIdx}`, text });
        }
      } else if (screen.source !== 'static') {
        const text = `Warning: ${mapPath} (screen "${sId}"): screen prompt_path is missing; set "prompt_path": "prompts/<screen>.prompt.md".`;
        warnings.push({ key: `${mapPath}\0mapscreenmissing\0${sIdx}`, text });
      }
    }
    if (root && typeof safeRead === 'function') {
      const cssPaths = new Set(Array.isArray(mapDoc.stylesheets) ? mapDoc.stylesheets.filter(item => typeof item === 'string' && item) : []);
      for (const [screen] of screenEntries) {
        if (Array.isArray(screen?.stylesheets)) {
          for (const css of screen.stylesheets) if (typeof css === 'string' && css) cssPaths.add(css);
        }
      }
      for (const cssPath of [...cssPaths].sort()) {
        try { safeRead(root, cssPath); }
        catch (error) {
          const text = `Warning: SVG layout ${mapPath} -> ${cssPath}: stylesheet: ${error.message}.`;
          warnings.push({ key: `${mapPath}\0css\0${cssPath}`, text });
        }
      }
    }
    const hasStateSchema = Boolean(mapDoc.state_schema && typeof mapDoc.state_schema === 'object' && !Array.isArray(mapDoc.state_schema));
    if (Object.hasOwn(mapDoc, 'state_schema') && !hasStateSchema) {
      const text = `Warning: ${mapPath}: state_schema must be a JSON Schema object (or omit it for compact app-map.json).`;
      warnings.push({ key: `${mapPath}\0mapstateschema`, text });
    }
    if (mapDoc.timers !== undefined) {
      lintTimers({ mapPath, mapDoc, validScreenIds, screenPromptById, hasStateSchema, promptExists, promptDeclaresOp, warnings });
    }
    if (hasStateSchema) {
      lintStateSchemaRefs({ mapPath, mapDoc, screenEntries, warnings });
    }
  }
  return inspectedCount;
}

function lintTimers({ mapPath, mapDoc, validScreenIds, screenPromptById, hasStateSchema, promptExists, promptDeclaresOp, warnings }) {
  if (!Array.isArray(mapDoc.timers) || mapDoc.timers.length > 16) {
    warnings.push({ key: `${mapPath}\0timersarr`, text: `Warning: ${mapPath}: timers must be an array of at most 16 timer objects.` });
    return;
  }
  const seenTimerScreens = new Set();
  for (const [tIdx, timer] of mapDoc.timers.entries()) {
    const tLabel = typeof timer?.id === 'string' && timer.id ? timer.id : `timers[${tIdx}]`;
    if (!timer || typeof timer !== 'object' || Array.isArray(timer)) {
      warnings.push({ key: `${mapPath}\0timerobj\0${tIdx}`, text: `Warning: ${mapPath} (timer "${tLabel}"): timer entry must be an object with id, screen, interval_ms, enabled_pointer, generation_pointer, handler, input, state and next.` });
      continue;
    }
    if (typeof timer.screen !== 'string' || timer.screen === '*' || !validScreenIds.has(timer.screen) || seenTimerScreens.has(timer.screen)) {
      warnings.push({ key: `${mapPath}\0timerscreen\0${tIdx}`, text: `Warning: ${mapPath} (timer "${tLabel}"): timer screen ${JSON.stringify(timer.screen ?? null)} must name a unique existing non-wildcard screen id from screens[].` });
    } else {
      seenTimerScreens.add(timer.screen);
    }
    if (!Number.isInteger(timer.interval_ms) || timer.interval_ms < 1000 || timer.interval_ms > 3600000) {
      warnings.push({ key: `${mapPath}\0timerinterval\0${tIdx}`, text: `Warning: ${mapPath} (timer "${tLabel}"): interval_ms (${JSON.stringify(timer.interval_ms)}) must be an integer from 1000 to 3600000 (for example "interval_ms": 1000).` });
    }
    const enInit = readPointer(mapDoc.initial_state, timer.enabled_pointer);
    const enSchema = hasStateSchema ? readSchemaPointer(mapDoc.state_schema, timer.enabled_pointer) : null;
    if (
      typeof enInit.value !== 'boolean'
      || (hasStateSchema && (!enSchema.exists || !enSchema.required || enSchema.schema?.type !== 'boolean' || Array.isArray(enSchema.schema?.oneOf)))
    ) {
      warnings.push({ key: `${mapPath}\0timerenabled\0${tIdx}`, text: `Warning: ${mapPath} (timer "${tLabel}"): enabled_pointer ${JSON.stringify(timer.enabled_pointer ?? null)} must resolve to a boolean in initial_state and a required {"type": "boolean"} property (without oneOf) in state_schema.` });
    }
    const genInit = readPointer(mapDoc.initial_state, timer.generation_pointer);
    const genSchema = hasStateSchema ? readSchemaPointer(mapDoc.state_schema, timer.generation_pointer) : null;
    const genMin = genSchema?.schema?.minimum;
    const genMax = genSchema?.schema?.maximum;
    const validGenInit = Number.isSafeInteger(genInit.value) && genInit.value >= 0 && genInit.value <= MAX_SAFE_TIMER_INT;
    const validGenMax = genMax === undefined || (Number.isSafeInteger(genMax) && genMax <= MAX_SAFE_TIMER_INT && Number.isSafeInteger(genMin) && genMin <= genMax);
    const validGenSchema = !hasStateSchema || (
      genSchema.exists && genSchema.required && genSchema.schema?.type === 'integer' && !Array.isArray(genSchema.schema?.oneOf)
      && Number.isSafeInteger(genMin) && genMin >= 0 && genMin <= MAX_SAFE_TIMER_INT && validGenMax
    );
    if (!validGenInit || !validGenSchema) {
      warnings.push({ key: `${mapPath}\0timergen\0${tIdx}`, text: `Warning: ${mapPath} (timer "${tLabel}"): generation_pointer ${JSON.stringify(timer.generation_pointer ?? null)} must resolve to a safe integer 0..9007199254740991 in initial_state and a required {"type": "integer", "minimum": 0} property (without oneOf) in state_schema.` });
    }
    if (timer.tick_operation !== undefined && (!timer.handler || typeof timer.handler !== 'object')) {
      const fallbackPrompt = screenPromptById.get(timer.screen) ?? 'prompts/<screen>.prompt.md';
      const opHint = typeof timer.tick_operation === 'string' && timer.tick_operation.trim() ? timer.tick_operation : '<tick_op>';
      warnings.push({ key: `${mapPath}\0timertickkey\0${tIdx}`, text: `Warning: ${mapPath} (timer "${tLabel}"): replace tick_operation ${JSON.stringify(timer.tick_operation)} with "handler": {"prompt_path": "${fallbackPrompt}", "operation": "${opHint}"} naming an existing prompt and declared tick operation.` });
    } else {
      const hPrompt = timer.handler?.prompt_path;
      const hOp = timer.handler?.operation;
      if (typeof hPrompt !== 'string' || !promptExists(hPrompt)) {
        warnings.push({ key: `${mapPath}\0timerhprompt\0${tIdx}`, text: `Warning: ${mapPath} (timer "${tLabel}"): handler.prompt_path ${JSON.stringify(hPrompt ?? null)} must reference an existing Git-visible prompts/*.prompt.md file.` });
      } else if (typeof hOp !== 'string' || !hOp.trim() || !promptDeclaresOp(hPrompt, hOp)) {
        warnings.push({ key: `${mapPath}\0timerhop\0${tIdx}`, text: `Warning: ${mapPath} (timer "${tLabel}"): tick_operation / handler.operation ${JSON.stringify(hOp ?? null)} is not declared in ${hPrompt}; declare "${hOp || '<tick_op>'}" in ${hPrompt} or update handler.operation.` });
      }
    }
  }
}

function lintStateSchemaRefs({ mapPath, mapDoc, screenEntries, warnings }) {
  const checkStateRefs = (node, label) => {
    if (!node || typeof node !== 'object') return;
    if (!Array.isArray(node) && Object.keys(node).length === 1 && typeof node.$ref === 'string') {
      if (node.$ref.startsWith('/state/')) {
        const statePtr = node.$ref.slice('/state'.length);
        if (!readSchemaPointer(mapDoc.state_schema, statePtr).exists) {
          warnings.push({ key: `${mapPath}\0stateref\0${label}\0${node.$ref}`, text: `Warning: ${mapPath} (${label}): $ref ${JSON.stringify(node.$ref)} does not resolve in state_schema; declare ${statePtr} in state_schema and initial_state or fix the $ref pointer.` });
        }
      }
      return;
    }
    for (const child of Object.values(node)) checkStateRefs(child, label);
  };
  const checkStateTargets = (stateNode, label) => {
    if (!stateNode || typeof stateNode !== 'object' || Array.isArray(stateNode)) return;
    if (Object.keys(stateNode).length === 1 && typeof stateNode.$ref === 'string') return;
    for (const key of Object.keys(stateNode)) {
      const ptr = key.startsWith('/') ? key : `/${key.replaceAll('~', '~0').replaceAll('/', '~1')}`;
      if (!readSchemaPointer(mapDoc.state_schema, ptr).exists) {
        warnings.push({ key: `${mapPath}\0statetarget\0${label}\0${key}`, text: `Warning: ${mapPath} (${label}): state target ${JSON.stringify(key)} does not resolve in state_schema; declare ${ptr} in state_schema and initial_state or update state.` });
      }
    }
  };
  for (const [screen, sIdx] of screenEntries) {
    checkStateRefs(screen.input, `screen "${typeof screen.id === 'string' && screen.id ? screen.id : `screens[${sIdx}]`}"`);
  }
  for (const [hIdx, handler] of (Array.isArray(mapDoc.handlers) ? mapDoc.handlers : []).entries()) {
    if (!handler || typeof handler !== 'object' || Array.isArray(handler)) continue;
    const hLabel = `handler "${typeof handler.id === 'string' && handler.id ? handler.id : `handlers[${hIdx}]`}"`;
    checkStateRefs(handler.input, hLabel);
    checkStateRefs(handler.state, hLabel);
    checkStateTargets(handler.state, hLabel);
    for (const [aIdx, afterStep] of (Array.isArray(handler.after) ? handler.after : []).entries()) {
      if (!afterStep || typeof afterStep !== 'object' || Array.isArray(afterStep)) continue;
      const aLabel = `${hLabel} after[${aIdx}]`;
      checkStateRefs(afterStep.input, aLabel);
      if (typeof afterStep.bind === 'string' && afterStep.bind.startsWith('/') && !readSchemaPointer(mapDoc.state_schema, afterStep.bind).exists) {
        warnings.push({ key: `${mapPath}\0afterbind\0${aLabel}\0${afterStep.bind}`, text: `Warning: ${mapPath} (${aLabel}): bind ${JSON.stringify(afterStep.bind)} does not resolve in state_schema; declare ${afterStep.bind} in state_schema and initial_state or update bind.` });
      }
    }
  }
  for (const [tIdx, timer] of (Array.isArray(mapDoc.timers) ? mapDoc.timers : []).entries()) {
    if (!timer || typeof timer !== 'object' || Array.isArray(timer)) continue;
    const tLabel = `timer "${typeof timer.id === 'string' && timer.id ? timer.id : `timers[${tIdx}]`}"`;
    checkStateRefs(timer.input, tLabel);
    checkStateRefs(timer.state, tLabel);
    checkStateTargets(timer.state, tLabel);
  }
}

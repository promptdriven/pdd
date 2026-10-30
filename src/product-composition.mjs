// Generated from prompts/cli/product-composition.prompt.md (sha256: da83412c73f29715e647a6d906a58df0187e8a1fe63ea40fbf91ac95827a2285).
import { basename, join } from 'node:path';
import { checkInput, interfaceBlocks, PreflightError, selectTests } from './runtime-preflight.mjs';
import { parseProductDocuments, parseProductWorldWriters } from './product.mjs';
import { expandSource, isJsonNumber, jsonNumberIdentity, parseJsonValue, stringifyJsonValue } from './contract-refs.mjs';

const fail = (code, message) => { throw Object.assign(Error(message), { code }); };
const badMap = message => fail('invalid-product-map', message);
const escape = value => value.replace(/~/g, '~0').replace(/\//g, '~1');
const plain = value => value !== null && typeof value === 'object' && !Array.isArray(value) && !isJsonNumber(value);
const ref = path => ({ $ref: path });

function matcherEqual(a, b) {
  if (a === b) return true;
  const numeric = value => isJsonNumber(value) || typeof value === 'number' || typeof value === 'boolean';
  if (numeric(a) && numeric(b)) return jsonNumberIdentity(typeof a === 'boolean' ? Number(a) : a) === jsonNumberIdentity(typeof b === 'boolean' ? Number(b) : b);
  if (Array.isArray(a) && Array.isArray(b)) return a.length === b.length && a.every((value, index) => matcherEqual(value, b[index]));
  return plain(a) && plain(b) && Object.keys(a).length === Object.keys(b).length
    && Object.entries(a).every(([key, value]) => Object.hasOwn(b, key) && matcherEqual(value, b[key]));
}

function scopeTemplate(value, part) {
  if (Array.isArray(value)) return value.map(item => scopeTemplate(item, part));
  if (!plain(value)) return value;
  return Object.fromEntries(Object.entries(value).map(([key, item]) => [key,
    key === '$ref' && typeof item === 'string' && /^\/state(?:\/|$)/.test(item)
      ? `/state/${escape(part)}${item.slice(6)}` : scopeTemplate(item, part)]));
}

function scopedHandlers(handlers, screen, encode) {
  const applicable = handlers.filter(rule => rule.screen === '*' || rule.screen === screen);
  const output = [];
  for (const kind of new Set(applicable.map(rule => rule.kind))) {
    const rules = applicable.filter(rule => rule.kind === kind);
    if (!rules.some(rule => rule.screen === '*') || !rules.some(rule => rule.screen === screen)) { output.push(...rules); continue; }
    const entries = value => Object.entries(value);
    const compatible = (a, b) => entries(a).every(([key, value]) => !Object.hasOwn(b, key) || matcherEqual(value, b[key]));
    const covers = (a, b) => entries(a).every(([key, value]) => Object.hasOwn(b, key) && matcherEqual(value, b[key]));
    const behavior = rule => encode(Object.fromEntries(entries(rule).filter(([key]) => !['screen', 'match'].includes(key))));
    const conditions = [], queue = [];
    const addCondition = match => { if (!conditions.some(prior => matcherEqual(prior, match))) { conditions.push(match); queue.push(match); } };
    for (const rule of rules) addCondition(rule.match);
    for (let index = 0; index < queue.length; index++) for (const rule of rules) {
      const match = queue[index];
      if (!compatible(match, rule.match)) continue;
      addCondition({ ...match, ...rule.match });
    }
    const compiled = conditions.map(match => {
      const eligible = rules.filter(rule => covers(rule.match, match));
      eligible.sort((a, b) => Number(a.screen === screen) - Number(b.screen === screen) || Object.keys(a.match).length - Object.keys(b.match).length);
      return { ...eligible.at(-1), match };
    });
    const minimal = compiled.filter(rule => !compiled.some(other => other !== rule && Object.keys(other.match).length < Object.keys(rule.match).length
      && covers(other.match, rule.match) && behavior(other) === behavior(rule)
      && !compiled.some(competitor => behavior(competitor) !== behavior(rule) && compatible(competitor.match, rule.match)
        && Object.keys(competitor.match).length >= Object.keys(other.match).length)));
    for (let index = 0; index < minimal.length; index++) for (const other of minimal.slice(index + 1)) {
      if (Object.keys(minimal[index].match).length === Object.keys(other.match).length && compatible(minimal[index].match, other.match)) {
        badMap(`Unsupported wildcard priority on ${screen}: overlapping ${kind} rules cannot retain their original priority after scoping.`);
      }
    }
    output.push(...minimal);
  }
  return output;
}

function validateMap(map, part) {
  const invalid = field => badMap(`app/maps/${part}.json has a missing or malformed ${field} field.`);
  const required = (value, fields, parent) => {
    if (!plain(value)) invalid(parent);
    for (const field of fields) if (!Object.hasOwn(value, field)) invalid(`${parent}.${field}`);
  };
  required(map, ['schema_version', 'name', 'initial_screen', 'initial_route', 'initial_state', 'state_schema', 'synthetic', 'screens', 'router', 'routes', 'handlers', 'stylesheets'], 'map');
  if (map.schema_version !== 'prompt-runtime.app-map.v1') invalid('schema_version');
  for (const field of ['name', 'initial_screen']) if (typeof map[field] !== 'string' || !map[field]) invalid(field);
  if (map.initial_route !== null && typeof map.initial_route !== 'string') invalid('initial_route');
  if (typeof map.synthetic !== 'boolean') invalid('synthetic');
  for (const field of ['initial_state', 'state_schema']) if (!plain(map[field])) invalid(field);
  for (const field of ['screens', 'routes', 'handlers', 'stylesheets']) if (!Array.isArray(map[field])) invalid(field);
  for (const screen of map.screens) {
    required(screen, ['id', 'prompt_path', 'operation', 'source', 'format', 'input', 'result_pointer'], 'screen');
    if (typeof screen.prompt_path !== 'string' || !screen.prompt_path) invalid('screen.prompt_path');
    if (!['operation', 'mockup'].includes(screen.source)) invalid('screen.source');
    if (screen.source === 'mockup') {
      if (screen.operation !== null) invalid('screen.operation');
      if (screen.format !== 'svg') invalid('screen.format');
      if (screen.result_pointer !== null) invalid('screen.result_pointer');
    } else {
      if (typeof screen.operation !== 'string' || !screen.operation) invalid('screen.operation');
      if (!['html', 'text', 'grid'].includes(screen.format)) invalid('screen.format');
      if (typeof screen.result_pointer !== 'string' || !/^(?:\/(?:[^~]|~[01])*)?$/.test(screen.result_pointer)) invalid('screen.result_pointer');
    }
  }
  if (map.router !== null) required(map.router, ['handler', 'input', 'result_pointer'], 'router');
  for (const route of map.routes) required(route, ['name', 'screen', 'input'], 'route');
  for (const handler of map.handlers) {
    required(handler, ['screen', 'kind', 'match', 'handler', 'input', 'next', 'state'], 'handler');
    required(handler.next, ['kind', 'screen', 'route_pointer'], 'handler.next');
    if (!plain(handler.match)) invalid('handler.match');
    if (Object.hasOwn(handler, 'after') && !Array.isArray(handler.after)) invalid('handler.after');
    for (const after of handler.after ?? []) required(after, ['handler', 'input', 'bind'], 'handler.after');
  }
}

function joinMaps(product, parts, maps, chain, encode, selectedParts) {
  maps.forEach((map, index) => validateMap(map, parts[index]));
  let scratch = 'product_after';
  while (selectedParts.includes(scratch)) scratch += '_';
  const slots = Object.fromEntries(chain.map((operation, index) => [String(index), checkInput(null, operation.resultSchema, 0).refusals.length
    ? { oneOf: [{ type: 'null' }, operation.resultSchema] } : operation.resultSchema]));
  const initial = Object.fromEntries(parts.map((part, index) => [part, maps[index].initial_state]));
  const properties = Object.fromEntries(parts.map((part, index) => [part, maps[index].state_schema]));
  if (chain.length) {
    initial[scratch] = Object.fromEntries(chain.map((_operation, index) => [String(index), null]));
    properties[scratch] = { type: 'object', properties: slots, required: Object.keys(slots), additionalProperties: false };
  }
  const stateKeys = Object.keys(initial);
  const allScreens = maps.flatMap((map, index) => (Array.isArray(map.screens) ? map.screens : []).map(screen => `${parts[index]}/${screen.id}`));
  const globalIds = new Set(allScreens);
  if (globalIds.size !== allScreens.length) badMap('Selected parts produce duplicate qualified screen IDs.');
  const joined = { schema_version: 'prompt-runtime.app-map.v1', name: product.name,
    initial_screen: `${parts[0]}/${maps[0].initial_screen}`, initial_route: maps[0].initial_route,
    initial_state: initial, state_schema: { type: 'object', properties, required: stateKeys, additionalProperties: false },
    synthetic: maps.some(map => map.synthetic === true), screens: [], router: null, routes: [], handlers: [], stylesheets: [] };
  const labels = [], routers = [], routes = new Map();
  let tapOperations = 0;
  for (const [index, map] of maps.entries()) {
    const part = parts[index], screenId = id => `${part}/${id}`;
    if (map.schema_version !== joined.schema_version || !Array.isArray(map.screens) || !Array.isArray(map.handlers)
      || !Array.isArray(map.stylesheets) || !Array.isArray(map.routes) || !Object.hasOwn(map, 'initial_state') || !plain(map.state_schema)) badMap(`app/maps/${part}.json is not a complete v1 map.`);
    const ids = new Set();
    for (const screen of map.screens) {
      if (!plain(screen) || Object.keys(screen).sort().join(',') !== 'format,id,input,operation,prompt_path,result_pointer,source'
        || typeof screen.id !== 'string' || !screen.id || ids.has(screen.id)) badMap(`app/maps/${part}.json has an invalid or duplicate screen ID.`);
      ids.add(screen.id);
      joined.screens.push({ ...screen, id: screenId(screen.id), input: scopeTemplate(screen.input, part) });
      labels.push({ id: screenId(screen.id), title: `${part} · ${screen.id}` });
    }
    if (!ids.has(map.initial_screen)) badMap(`app/maps/${part}.json has an unknown initial screen.`);
    routers.push(map.router === null ? null : scopeTemplate(map.router, part));
    for (const route of map.routes) {
      const scoped = { ...route, screen: screenId(route.screen), input: scopeTemplate(route.input, part) };
      if (!ids.has(route.screen)) badMap(`app/maps/${part}.json has an unknown route screen.`);
      if (routes.has(route.name) && encode(routes.get(route.name)) !== encode(scoped)) fail('unsupported-product-router', `Route ${route.name} selects different part screens.`);
      routes.set(route.name, scoped);
    }
    for (const handler of map.handlers) if (handler.screen !== '*' && !ids.has(handler.screen)) badMap(`app/maps/${part}.json has an unknown handler screen.`);
    for (const target of ids) {
      for (const handler of scopedHandlers(map.handlers, target, encode)) {
        const next = { ...handler.next };
        if (next.screen !== null && next.screen !== undefined) {
          if (ids.has(next.screen)) next.screen = screenId(next.screen);
          else if (!globalIds.has(next.screen)) badMap(`app/maps/${part}.json: next screen ${next.screen} is neither local nor a screen in the selected product parts.`);
        }
        const after = (handler.after ?? []).map(operation => {
          if (typeof operation.bind !== 'string' || !operation.bind.startsWith('/')) badMap(`app/maps/${part}.json has an invalid after binding.`);
          return { ...operation, input: scopeTemplate(operation.input, part), bind: `/${escape(part)}${operation.bind}` };
        });
        if (handler.handler !== null && handler.handler !== undefined) {
          for (const [offset, operation] of chain.entries()) after.push({ handler: operation.handler, input: {}, bind: `/${escape(scratch)}/${offset}` });
          if (after.length > 8) badMap(`app/maps/${part}.json needs ${after.length} after operations; the Runtime limit is 8 (40 total calls per tap).`);
          tapOperations = Math.max(tapOperations, 1 + after.length);
        }
        const state = handler.state === null || handler.state === undefined ? null : Object.fromEntries(stateKeys.map(key => [key,
          key === part ? scopeTemplate(handler.state, part) : ref(`/state/${escape(key)}`)]));
        joined.handlers.push({ ...handler, screen: screenId(target), input: scopeTemplate(handler.input, part), next, state, ...(Object.hasOwn(handler, 'after') || after.length ? { after } : {}) });
      }
    }
    for (const stylesheet of map.stylesheets) if (!joined.stylesheets.includes(stylesheet)) joined.stylesheets.push(stylesheet);
  }
  if (routers.some(router => router !== null)) {
    if (routers.some(router => router === null) || routers.some(router => encode(router) !== encode(routers[0]))) fail('unsupported-product-router', 'Selected maps require incompatible routers; the Runtime has one router slot.');
    joined.router = routers[0];
  }
  joined.routes = [...routes.values()];
  return { map: joined, labels, tapOperations };
}

export function selectJourneys(tests, selector) {
  const candidates = tests.filter(test => /^user_stories\/journeys\/[^/]+\.md$/.test(test.storyPath));
  if (selector === undefined) return candidates.map(test => test.testPath);
  const records = candidates.map(test => ({ ...test, path: test.testPath }));
  const exactPaths = records.filter(test => test.testPath === selector || test.storyPath === selector).map(test => test.testPath);
  const exact = exactPaths.length ? selectTests({ tests: records }, exactPaths).selected : [];
  const matches = exact.length ? exact : records.filter(test => {
    const name = basename(test.storyPath, '.md');
    return name === selector || name.startsWith(`${selector}-`) || name.startsWith(`${selector}.`);
  });
  if (new Set(matches.map(test => test.storyPath)).size !== 1) {
    fail('invalid-journey', `${matches.length ? 'Ambiguous' : 'Unknown'} journey ${selector}. Candidates: ${[...new Set(candidates.map(test => test.storyPath))].join(', ') || 'none'}.`);
  }
  return matches.map(test => test.testPath);
}

export function composeProductTry({ root, parts, journey, testPath }, ports) {
  const cached = new Map();
  const read = (path, optional = false) => {
    if (cached.has(path)) return cached.get(path);
    const stat = ports.statFile(join(root, path));
    if (stat?.is_symlink) throw new PreflightError(4, `${path}: symbolic links are not allowed.`);
    if (!stat || typeof stat.exists !== 'boolean') throw new PreflightError(4, `${path}: source file could not be inspected.`);
    if (!stat.exists) { if (optional) return null; badMap(`${path}: required source file is missing.`); }
    const value = ports.readFile(join(root, path));
    const text = typeof value === 'string' ? value : Buffer.isBuffer(value) ? value.toString('utf8') : null;
    if (text === null) badMap(`${path}: the file reader did not return UTF-8 bytes.`);
    cached.set(path, text); return text;
  };
  const files = {
    stat({ path }) { return ports.statFile(join(root, path)); },
    read({ path }) { return { content: read(path) }; },
  };
  try {
    const mapText = read('product/map.md'), planText = read('product/plan.md', true) ?? '';
    const { product } = parseProductDocuments({ mapText, planText });
    const selected = parts === undefined ? product.parts.map(part => part.part) : [...parts];
    if (!selected.length || new Set(selected).size !== selected.length || selected.some(part => !product.parts.some(row => row.part === part))) {
      fail('invalid-product', `Choose distinct product parts from: ${product.parts.map(part => part.part).join(', ')}.`);
    }
    const writers = new Map();
    for (const { key, writer } of parseProductWorldWriters({ worldText: read('contracts/world.md') })) {
      if (writers.has(key) && writers.get(key) !== writer) fail('world-writer-conflict', `${key} is written by ${writers.get(key)} and ${writer}.`);
      writers.set(key, writer);
    }
    const parseWorld = path => {
      const expanded = expandSource({ path, text: JSON.stringify({ initial_world: { $seed: path } }), format: 'scenario' }, files);
      return parseJsonValue(expanded.text).initial_world;
    };
    let world = parseWorld('contracts/seed-world.json');
    const contributions = new Map();
    for (const part of selected) {
      const path = `prompts/${part}/seed.json`;
      if (read(path, true) === null) continue;
      const value = parseWorld(path);
      for (const key of Object.keys(value)) {
        if (contributions.has(key) && contributions.get(key) !== part) fail('world-writer-conflict', `${key} is seeded by ${contributions.get(key)} and ${part}.`);
        if (writers.has(key) && writers.get(key) !== part) fail('world-writer-conflict', `${key} is written by ${writers.get(key)}, not seed part ${part}.`);
        contributions.set(key, part);
      }
      world = Object.fromEntries([...Object.entries(world), ...Object.entries(value)]);
    }
    let appMapPath, seedPath;
    for (let suffix = 0; ; suffix++) {
      const tag = suffix ? `_${suffix}` : '';
      appMapPath = `app/maps/product${tag}.json`;
      seedPath = `contracts/product-seed${tag}.json`;
      const mapStat = ports.statFile(join(root, appMapPath)), seedStat = ports.statFile(join(root, seedPath));
      if (mapStat?.is_symlink || seedStat?.is_symlink) throw new PreflightError(4, 'Generated product paths must not be symbolic links.');
      if (!mapStat || !seedStat || typeof mapStat.exists !== 'boolean' || typeof seedStat.exists !== 'boolean') throw new PreflightError(4, 'Generated product paths could not be inspected.');
      if (!mapStat.exists && !seedStat.exists) break;
    }
    if (journey !== undefined) {
      if (typeof testPath !== 'string' || !testPath) fail('invalid-journey', 'Choose one journey test path for this Try.');
      const raw = read(testPath), scenario = parseJsonValue(raw);
      selectJourneys([{ testPath, storyPath: scenario.story_path }], journey);
      if (!plain(scenario.initial_world)) fail('invalid-journey', `${testPath}: initial_world must be an object.`);
      // Validate its ordinary standalone seed/reference before using only its set.
      expandSource({ path: testPath, text: raw, format: 'scenario' }, files);
      if (Object.hasOwn(scenario.initial_world, '$seed')) {
        const base = stringifyJsonValue(world), overlay = { ...files,
          stat: input => input.path === seedPath ? { exists: true, is_symlink: false, size: Buffer.byteLength(base) } : files.stat(input),
          read: input => input.path === seedPath ? { content: base } : files.read(input) };
        const initial_world = { $seed: seedPath, ...(Object.hasOwn(scenario.initial_world, 'set') ? { set: scenario.initial_world.set } : {}) };
        world = parseJsonValue(expandSource({ path: testPath, text: stringifyJsonValue({ initial_world }), format: 'scenario' }, overlay).text).initial_world;
      } else world = Object.fromEntries([...Object.entries(world), ...Object.entries(scenario.initial_world)]);
    }
    const afterSection = planText.split(/^##\s+/m).find(section => section.split(/\r?\n/, 1)[0].trim() === 'After every tap');
    const chain = [];
    for (const line of afterSection?.split(/\r?\n/).slice(1) ?? []) {
      const item = /^\s*\d+[.)]\s+`?(.+?\.prompt\.md)#([^\s`#]+)`?\s*$/.exec(line);
      if (!item) { if (/^\s*\d+[.)]/.test(line)) badMap(`Invalid After every tap operation: ${line.trim()}`); continue; }
      const handler = { prompt_path: item[1], operation: item[2] };
      const expanded = expandSource({ path: handler.prompt_path, text: read(handler.prompt_path), format: 'prompt' }, files);
      const blocks = interfaceBlocks(expanded.text);
      if (blocks.length !== 1) badMap(`${handler.prompt_path}: expected one Runtime interface for ${handler.operation}.`);
      const entry = parseJsonValue(blocks[0][1]).entries?.find(operation => operation.operation === handler.operation);
      if (!entry || !plain(entry.result_schema)) badMap(`${handler.prompt_path}: missing operation/result schema ${handler.operation}.`);
      chain.push({ handler, resultSchema: entry.result_schema });
    }
    const mapped = selected.flatMap(part => {
      const text = read(`app/maps/${part}.json`, true);
      return text === null ? [] : [{ part, map: parseJsonValue(text) }];
    });
    if (!mapped.length) badMap('No screen is available: the selected product parts have no app map; Runtime v1 requires an initial screen.');
    const joined = joinMaps(product, mapped.map(item => item.part), mapped.map(item => item.map), chain, stringifyJsonValue, selected);
    return { appMapPath, seedPath, files: [{ path: appMapPath, content: stringifyJsonValue(joined.map) }, { path: seedPath, content: stringifyJsonValue(world) }],
      parts: selected, journey: journey ?? null, tapOperations: joined.tapOperations, labels: joined.labels };
  } catch (error) {
    if (error.exitCode || ['invalid-product', 'invalid-journey', 'world-writer-conflict', 'invalid-product-map', 'unsupported-product-router'].includes(error.code) || /^(?:contract-|seed-)/.test(error.code ?? '')) throw error;
    badMap(`Cannot compose this product Try: ${error.message}`);
  }
}

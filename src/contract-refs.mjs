// Generated from prompts/cli/contract-refs.prompt.md (sha256: 4ecd985f99d99f7fbc9a9e45cb48846531dd82be070293559821caa42e01675e).
// Numbers remain tokens until serialization, including values outside binary64.
class JsonNumber { constructor(text) { this.text = text; Object.freeze(this); } }
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value) && !(value instanceof JsonNumber);
const parse = text => JSON.parse(text, (_key, value, context) => typeof value === 'number' ? new JsonNumber(context.source) : value);
const encode = value => value instanceof JsonNumber ? value.text : Array.isArray(value) ? `[${value.map(encode).join(',')}]`
  : object(value) ? `{${Object.keys(value).sort().map(key => `${JSON.stringify(key)}:${encode(value[key])}`).join(',')}}` : JSON.stringify(value);
const clone = value => parse(encode(value));
export { parse as parseJsonValue, encode as stringifyJsonValue };
export const isJsonNumber = value => value instanceof JsonNumber;
const put = (value, key, item) => Object.defineProperty(value, key, { value: item, enumerable: true, configurable: true, writable: true });
const escape = key => key.replace(/~/g, '~0').replace(/\//g, '~1');
const fragment = title => title.toLowerCase().replace(/[^\p{L}\p{N}\s_-]/gu, '').replace(/\s+/g, '-');
const INTERFACE = /<details\b[^>]*>\s*<summary\b[^>]*>\s*(?:<strong\b[^>]*>\s*)?Runtime\s+interface(?:\s*:\s*[^<]+?)?\s*(?:<\/strong\s*>\s*)?(?:\s*:\s*[^<]+?)?\s*<\/summary\s*>\s*```json\b\s*([\s\S]*?)\s*```\s*<\/details\s*>/gid;

function fail(code, consumer, target, detail, chain = []) {
  const message = `${consumer}: ${target}: ${detail}${chain.length ? ` (${chain.join(' -> ')})` : ''}`;
  throw Object.assign(new Error(message.slice(0, 4000)), { code });
}
function pointerTokens(pointer, invalid) {
  if (pointer === '') return [];
  if (typeof pointer !== 'string' || !pointer.startsWith('/') || /~(?:[^01]|$)/.test(pointer)) invalid();
  return pointer.slice(1).split('/').map(key => key.replace(/~1/g, '/').replace(/~0/g, '~'));
}
function member(value, key) {
  return (object(value) || Array.isArray(value)) && Object.hasOwn(value, key)
    && (!Array.isArray(value) || /^(?:0|[1-9][0-9]*)$/.test(key));
}

// Headings and fences are recognized together: headings inside a fence are data.
function sections(text) {
  const result = []; let section = null, fence = null;
  for (const line of text.split(/\r?\n/)) {
    const marker = /^ {0,3}(`{3,}|~{3,})(.*)$/.exec(line);
    if (fence) {
      if (marker && marker[1][0] === fence.char && marker[1].length >= fence.length && !marker[2].trim()) {
        if (fence.json && section) section.blocks.push(fence.lines.join('\n'));
        fence = null;
      } else if (fence.json) fence.lines.push(line);
      continue;
    }
    if (marker) { fence = { char: marker[1][0], length: marker[1].length, json: marker[2].trim() === 'json', lines: [] }; continue; }
    const heading = /^ {0,3}(#{1,3})\s+(.+?)\s*#*\s*$/.exec(line);
    if (heading) {
      section = heading[1].length === 3 ? { title: heading[2], blocks: [] } : null;
      if (section) result.push(section);
    }
  }
  return result;
}

function schemaSlots(document, visit) {
  if (!object(document)) return;
  const entries = Array.isArray(document.entries) ? document.entries : [];
  entries.forEach((entry, i) => { if (object(entry)) for (const key of ['input_schema','result_schema']) if (Object.hasOwn(entry, key)) put(entry, key, visit(entry[key], `/entries/${i}/${key}`)); });
  const resources = Array.isArray(document.resources) ? document.resources : [];
  resources.forEach((resource, i) => {
    (Array.isArray(resource?.operations) ? resource.operations : []).forEach((operation, j) => {
      if (object(operation)) for (const key of ['arguments_schema','result_schema']) if (Object.hasOwn(operation, key)) put(operation, key, visit(operation[key], `/resources/${i}/operations/${j}/${key}`));
    });
  });
}
function schemaChildren(value, pointer, visit) {
  if (!object(value)) return value;
  if (object(value.properties)) for (const key of Object.keys(value.properties)) put(value.properties, key, visit(value.properties[key], `${pointer}/properties/${escape(key)}`));
  if (Object.hasOwn(value, 'items')) put(value, 'items', visit(value.items, `${pointer}/items`));
  if (Array.isArray(value.oneOf)) value.oneOf = value.oneOf.map((child, i) => visit(child, `${pointer}/oneOf/${i}`));
  return value;
}

export function expandSource({ path: consumer, text, format }, files) {
  const references = new Map(), documents = new Map();
  const error = (code, target, detail, chain) => fail(code, consumer, target, detail, chain);
  function load(path, requested, chain) {
    if (documents.has(path)) return documents.get(path);
    let stat, content;
    try {
      stat = files.stat({ path });
      if (!stat?.exists) error('contract-missing', requested, `missing file ${path}`, chain);
      if (stat.is_symlink) error('contract-unsafe', requested, 'symbolic link', chain);
      content = files.read({ path }).content;
      if (typeof content !== 'string') throw new Error('Invalid content');
    } catch (cause) {
      if (typeof cause?.code==='string' && cause.code.startsWith('contract-')) throw cause;
      error('contract-unsafe', requested, `cannot safely read ${path}`, chain);
    }
    documents.set(path, content);
    return content;
  }
  function target(requested, kind, chain) {
    if (typeof requested !== 'string') error(kind === 'seed' ? 'seed-invalid' : 'contract-invalid', String(requested), 'reference must be a string', chain);
    const hash = requested.indexOf('#'), path = hash < 0 ? requested : requested.slice(0, hash), selection = hash < 0 ? '' : requested.slice(hash + 1);
    if (!path || /^[~/]|^[a-z][a-z0-9+.-]*:/i.test(path) || /[\\\x00-\x1f\x7f]/.test(path) || path.split('/').some(part => !part || part === '.' || part === '..')) error('contract-unsafe', requested, 'use a safe repository-root path', chain);
    if (kind === 'seed' && (hash >= 0 || !path.endsWith('.json'))) error('seed-invalid', requested, 'seed must name a JSON file without a fragment', chain);
    const content = load(path, requested, chain);
    let value, canonical;
    if (path.endsWith('.md') && kind === 'contract') {
      const matches = sections(content).filter(section => section.title === selection || fragment(section.title) === selection);
      if (!matches.length) error('contract-missing', requested, `no ### ${selection}`, chain);
      if (matches.length !== 1) error('contract-ambiguous', requested, `ambiguous heading ${selection}`, chain);
      if (!matches[0].blocks.length) error('contract-missing', requested, `no JSON record under ### ${selection}`, chain);
      if (matches[0].blocks.length !== 1) error('contract-invalid', requested, 'record needs exactly one JSON block', chain);
      try { value = parse(matches[0].blocks[0]); } catch { error('contract-invalid', requested, 'record contains invalid JSON', chain); }
      canonical = `${path}#${matches[0].title}`;
    } else if (path.endsWith('.json')) {
      try { value = parse(content); } catch { error('contract-invalid', requested, 'file contains invalid JSON', chain); }
      const tokens = pointerTokens(selection, () => error('contract-invalid', requested, 'invalid JSON Pointer', chain));
      for (const key of tokens) {
        if (!member(value, key)) error('contract-missing', requested, `missing JSON Pointer ${selection}`, chain);
        value = value[key];
      }
      canonical = `${path}#${tokens.length ? `/${tokens.map(escape).join('/')}` : ''}`;
    } else error('contract-invalid', requested, 'target must be Markdown or JSON', chain);
    if (!object(value)) error(kind === 'seed' ? 'seed-invalid' : 'contract-invalid', requested, 'selected value must be an object', chain);
    if (chain.includes(canonical)) error('contract-cycle', requested, 'reference cycle', [...chain, canonical]);
    return { value: clone(value), canonical };
  }
  function record(pointer, canonical, kind, value) {
    const ref = { consumer, source_pointer: pointer, target: canonical, kind, value_json: encode(value) };
    references.set(JSON.stringify([consumer,pointer,canonical,kind]), ref);
  }
  function schema(value, pointer, chain = [], originating = null) {
    if (!object(value)) return value;
    if (Object.hasOwn(value, '$contract')) {
      if (typeof value.$contract !== 'string' || Object.keys(value).some(key => !['$contract','title','description'].includes(key)) || ['title','description'].some(key => Object.hasOwn(value,key) && typeof value[key] !== 'string')) error('contract-invalid', String(value.$contract), 'only string title and description may accompany $contract', chain);
      const origin = originating ?? pointer, { value: selected, canonical } = target(value.$contract, 'contract', chain);
      const expanded = schema(selected, origin, [...chain, canonical], origin);
      record(origin, canonical, 'contract', expanded);
      const result = clone(expanded);
      for (const key of ['title','description']) if (Object.hasOwn(value,key)) put(result,key,value[key]);
      return result;
    }
    return schemaChildren(value, pointer, (child, childPointer) => schema(child, childPointer, chain, originating));
  }
  function seed(value, pointer, chain = []) {
    if (!object(value) || !Object.hasOwn(value, '$seed')) return value;
    if (typeof value.$seed !== 'string' || Object.keys(value).some(key => !['$seed','set'].includes(key)) || (Object.hasOwn(value,'set') && !object(value.set))) error('seed-invalid', String(value.$seed), 'invalid shared world or overrides', chain);
    const { value: selected, canonical } = target(value.$seed, 'seed', chain);
    let world = seed(selected, pointer, [...chain, canonical]);
    record(pointer, canonical, 'seed', world);
    world = clone(world);
    for (const [raw, replacement] of Object.entries(value.set ?? {})) {
      const invalid = () => error('seed-invalid', value.$seed, `invalid override pointer ${raw}`, chain);
      const tokens = pointerTokens(raw, invalid);
      if (!tokens.length) { if (!object(replacement)) invalid(); world = clone(replacement); continue; }
      let parent = world;
      for (const key of tokens.slice(0,-1)) { if (!member(parent,key)) invalid(); parent = parent[key]; }
      const key = tokens.at(-1);
      if (!object(parent) && !Array.isArray(parent)) invalid();
      if (Array.isArray(parent) && !member(parent,key)) invalid();
      put(parent, key, clone(replacement));
    }
    return world;
  }
  let document, block;
  if (format === 'prompt') {
    const blocks = [...text.matchAll(INTERFACE)];
    if (blocks.length !== 1) return { text, references: [] };
    block = blocks[0];
    try { document = parse(block[1]); } catch { return { text, references: [] }; }
    schemaSlots(document, (value,pointer) => schema(value,pointer));
  } else {
    try { document = parse(text); } catch { return { text, references: [] }; }
    if (format === 'json-schema') document = schema(document, '');
    else if (format === 'scenario' && object(document) && Object.hasOwn(document, 'initial_world')) put(document,'initial_world',seed(document.initial_world, '/initial_world'));
  }
  if (!references.size) return { text, references: [] };
  const result = encode(document);
  const effective = block ? `${text.slice(0,block.indices[1][0])}${result}${text.slice(block.indices[1][1])}` : result;
  return { text: effective, references: [...references.values()].sort((a,b) => {
    for (const key of ['consumer','source_pointer','target','kind']) { if (a[key] !== b[key]) return a[key] < b[key] ? -1 : 1; }
    return 0;
  }) };
}

export function catalogRecords(sources, targets = []) {
  const map = new Map(sources.map(source => [source.path, source.text])), records = [], warnings = [];
  const files = { stat: ({path}) => ({ exists: map.has(path), is_symlink: false, size: Buffer.byteLength(map.get(path) ?? '') }), read: ({path}) => ({ content: map.get(path) }) };
  const candidates = new Set(targets);
  for (const {path,text} of sources) {
    if (path.endsWith('.md')) for (const section of sections(text)) if (section.blocks.length) candidates.add(`${path}#${section.title}`);
    if (path.endsWith('.json')) {
      try {
        const root = parse(text);
        if (object(root)) candidates.add(`${path}#`);
        const walk = (value, pointer) => {
          if (object(value) && object(value.properties)) candidates.add(`${path}#${pointer}`);
          if (object(value) || Array.isArray(value)) for (const [key,child] of Object.entries(value)) walk(child, `${pointer}/${escape(key)}`);
        };
        walk(root,'');
      } catch { warnings.push(`${path}: invalid JSON contract`); }
    }
  }
  for (const target of [...candidates].sort()) {
    try {
      const path = target.split('#')[0];
      if (target === `${path}#` && path.endsWith('.json') && object(parse(map.get(path))) && Object.hasOwn(parse(map.get(path)), '$seed')) {
        const expanded = expandSource({ path, text: JSON.stringify({ initial_world: { $seed:path } }), format:'scenario' }, files);
        records.push({path,target,value_json:encode(parse(expanded.text).initial_world)});
        continue;
      }
      const expanded = expandSource({ path: target.split('#')[0], text: JSON.stringify({$contract:target}), format: 'json-schema' }, files);
      const own = expanded.references.find(ref => ref.target === target) ?? expanded.references.find(ref => ref.source_pointer === '' && ref.kind === 'contract');
      if (own && !records.some(record => record.target === own.target)) records.push({ path: own.target.split('#')[0], target: own.target, value_json: expanded.text });
    } catch (error) { warnings.push(error.message); }
  }
  return { records: records.sort((a,b) => a.target < b.target ? -1 : a.target > b.target ? 1 : 0), warnings };
}

function numericIdentity(text) {
  const [,sign,whole,fraction = '',exponent = '0'] = /^(-?)(\d+)(?:\.(\d+))?(?:[eE]([+-]?\d+))?$/.exec(text);
  let digits = `${whole}${fraction}`.replace(/^0+/, '');
  if (!digits) return '0';
  const trailing = /0*$/.exec(digits)[0].length;
  digits = digits.slice(0, digits.length - trailing);
  return `${sign}${digits}e${BigInt(exponent) - BigInt(fraction.length) + BigInt(trailing)}`;
}
function differences(a,b,pointer = '', root = true) {
  if (a instanceof JsonNumber && b instanceof JsonNumber) return numericIdentity(a.text) === numericIdentity(b.text) ? [] : [`${pointer}: ${a.text} -> ${b.text}`];
  if (object(a) && object(b)) return [...new Set([...Object.keys(a),...Object.keys(b)])].sort().flatMap(key => {
    if (root && ['title','description'].includes(key)) return [];
    const path = `${pointer}/${escape(key)}`;
    if (!Object.hasOwn(a,key)) return [`${path}: missing in copy`];
    if (!Object.hasOwn(b,key)) return [`${path}: extra in copy`];
    return differences(a[key],b[key],path,false);
  });
  if (Array.isArray(a) && Array.isArray(b)) return a.length !== b.length ? [`${pointer}: ${encode(a)} -> ${encode(b)}`] : a.flatMap((child,i) => differences(child,b[i],`${pointer}/${i}`,false));
  return encode(a) === encode(b) ? [] : [`${pointer}: ${encode(a)} -> ${encode(b)}`];
}
export function compareCopies(sources, records) {
  const matches = [], warnings = [], candidates = records.flatMap(record => {
    try { const value = parse(record.value_json); return object(value) && value.type==='object' && object(value.properties) ? [{...record,value}] : []; } catch { return []; }
  });
  for (const {path,text} of sources) {
    const blocks = [...text.matchAll(INTERFACE)];
    if (blocks.length !== 1) continue;
    let document; try { document = parse(blocks[0][1]); } catch { continue; }
    const visit = (value,pointer) => {
      if (!object(value) || Object.hasOwn(value,'$contract')) return value;
      if (value.type==='object' && object(value.properties)) {
        const keys = new Set(Object.keys(value.properties));
        const options = candidates.filter(record => {
          const other = new Set(Object.keys(record.value.properties));
          return [...keys].filter(key => !other.has(key)).length + [...other].filter(key => !keys.has(key)).length <= 1;
        }).map(record => ({ record, differences: differences(value,record.value) }));
        const exact = options.filter(option => !option.differences.length), chosen = exact.length ? exact : options;
        if (chosen.length === 1) matches.push({ path, source_pointer:pointer, target:chosen[0].record.target, kind:chosen[0].differences.length ? 'near' : 'exact', differences:chosen[0].differences });
        else if (chosen.length > 1) warnings.push(`${path} ${pointer}: ambiguous contract copies (${chosen.map(option => option.record.target).join(', ')})`);
      }
      return schemaChildren(value,pointer,visit);
    };
    schemaSlots(document,visit);
  }
  return { matches, warnings };
}
export function planSync(sources, matches) {
  const edits = [], warnings = [];
  for (const {path,text} of sources) {
    const selected = matches.filter(match => match.path === path).sort((a,b) => a.source_pointer.length - b.source_pointer.length);
    if (!selected.length) continue;
    const blocks = [...text.matchAll(INTERFACE)]; if (blocks.length !== 1) continue;
    const block = blocks[0]; let document;
    try { document = parse(block[1]); } catch { continue; }
    const replaced = [];
    for (const match of selected) {
      if (replaced.some(parent => match.source_pointer.startsWith(`${parent}/`))) continue;
      const tokens = pointerTokens(match.source_pointer, () => fail('contract-invalid',path,match.target,'invalid schema location'));
      let parent = document;
      for (const key of tokens.slice(0,-1)) { if (!member(parent,key)) { parent = null; break; } parent = parent[key]; }
      const key = tokens.at(-1), value = parent?.[key];
      if (!object(value) || Object.hasOwn(value,'$contract')) continue;
      const reference = { $contract: match.target };
      for (const annotation of ['title','description']) if (Object.hasOwn(value,annotation)) put(reference,annotation,clone(value[annotation]));
      put(parent,key,reference); replaced.push(match.source_pointer);
    }
    if (!replaced.length) continue;
    if (document.status === 'approved') document.status = 'draft';
    const after = `${text.slice(0,block.indices[1][0])}${encode(document)}${text.slice(block.indices[1][1])}`;
    if (after !== text) edits.push({path,before:text,after});
  }
  return { edits, warnings };
}

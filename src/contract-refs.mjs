// Generated from prompts/cli/contract-refs.prompt.md (sha256: cdb7b37258b1f16aef7a301bde2a1e0853924ed9f29df94880c5ed6f240eaa31).
// Numbers remain tokens until serialization, including values outside binary64.
class JsonNumber { constructor(text) { this.text = text; Object.freeze(this); } }
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value) && !(value instanceof JsonNumber);
const LIMIT = 10_485_760;
const layouts = new WeakMap();
const put = (value, key, item) => Object.defineProperty(value, key, { value: item, enumerable: true, configurable: true, writable: true });
const keysOf = value => {
  const layout=layouts.get(value);
  if (!layout) return Object.keys(value);
  const written=new Set(layout.keys);
  return [...layout.keys.filter(key=>Object.hasOwn(value,key)),...Object.keys(value).filter(key=>!written.has(key))];
};
// JSON.parse remains the value decoder. This lexical index records the source
// spans and written member order which JavaScript's object enumeration loses.
function parse(text) {
  const value = JSON.parse(text, (_key, item, context) => typeof item === 'number' ? new JsonNumber(context.source) : item);
  const tokens = [...text.matchAll(/"(?:[^"\\]+|\\[\s\S])*"|-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?|true|false|null|[{}\[\]:,]/g)];
  let index = 0;
  function locate(item) {
    const first = tokens[index++], start = first.index;
    const array = first[0] === '[';
    if (!array && first[0] !== '{') return {start,end:start+first[0].length,value:item};
    const entries = [], keys = [];
    while (tokens[index][0] !== (array ? ']' : '}')) {
      let key, keyStart, keyEnd;
      if (array) key = String(entries.length);
      else { const token = tokens[index++]; keyStart = token.index; keyEnd = token.index+token[0].length; key = JSON.parse(token[0]); index++; }
      const child = locate((object(item) || Array.isArray(item)) && Object.hasOwn(item,key) ? item[key] : undefined);
      entries.push({...child,key,keyStart,keyEnd}); keys.push(key);
      if (tokens[index][0] === ',') index++; else break;
    }
    const end = tokens[index++].index + 1;
    if ((array && Array.isArray(item)) || (!array && object(item))) {
      const last = new Map(entries.map((entry,i)=>[entry.key,i]));
      entries.forEach((entry,i)=>{entry.active=last.get(entry.key)===i;});
      layouts.set(item,{text,start,end,entries,keys:[...new Set(keys)]});
    }
    return {start,end,value:item};
  }
  locate(value);
  return value;
}
function shallow(value) {
  const result = Array.isArray(value) ? [] : {};
  for (const key of keysOf(value)) put(result,key,value[key]);
  if (layouts.has(value)) layouts.set(result,layouts.get(value));
  return result;
}
function clone(value) {
  if (!object(value) && !Array.isArray(value)) return value;
  const result = shallow(value);
  for (const key of keysOf(value)) put(result,key,clone(value[key]));
  return result;
}
function writeJson(value, {canonical = false, collect = true, tooBig = () => { throw new Error('JSON value is too big'); }} = {}) {
  let size = 0; const parts = [], measured = new WeakMap();
  const append = text => { size += Buffer.byteLength(text); if (size > LIMIT) tooBig(); if (collect) parts.push(text); };
  function visit(item) {
    if (item instanceof JsonNumber) { append(item.text); return; }
    if (!object(item) && !Array.isArray(item)) { append(JSON.stringify(item)); return; }
    if (!collect && measured.has(item)) { size += measured.get(item); if (size>LIMIT) tooBig(); return; }
    const initialSize = size;
    const layout = !canonical && layouts.get(item), keys = canonical && !Array.isArray(item) ? Object.keys(item).sort() : keysOf(item);
    if (layout && layout.keys.every(key => Object.hasOwn(item,key)) && keys.length >= layout.keys.length) {
      let offset = layout.start;
      for (const entry of layout.entries) {
        append(layout.text.slice(offset,entry.start));
        if (!entry.active || item[entry.key] === entry.value) append(layout.text.slice(entry.start,entry.end)); else visit(item[entry.key]);
        offset = entry.end;
      }
      const written=new Set(layout.keys), added = keys.filter(key => !written.has(key));
      if (added.length) {
        const first = layout.entries[0], last = layout.entries.at(-1);
        const prefix = first ? layout.text.slice(layout.start+1,first.keyStart) : '';
        const colon = first ? layout.text.slice(first.keyEnd,first.start) : ':';
        const separator = layout.entries.length > 1 ? layout.text.slice(layout.entries[0].end,layout.entries[1].keyStart) : `,${prefix}`;
        for (const key of added) { append(last || key !== added[0] ? separator : ''); append(JSON.stringify(key)); append(colon); visit(item[key]); }
      }
      append(layout.text.slice(offset,layout.end)); if (!collect) measured.set(item,size-initialSize); return;
    }
    const array = Array.isArray(item);
    append(array ? '[' : '{');
    keys.forEach((key,i) => { if (i) append(','); if (!array) { append(JSON.stringify(key)); append(':'); } visit(item[key]); });
    append(array ? ']' : '}');
    if (!collect) measured.set(item,size-initialSize);
  }
  visit(value);
  return collect ? parts.join('') : size;
}
const encode = value => writeJson(value,{canonical:true});
const render = (value,tooBig) => writeJson(value,{tooBig});
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
    const heading = /^ {0,3}(#{1,3})[ \t]+(.+?)[ \t]*$/.exec(line);
    if (heading) heading[2] = heading[2].replace(/[ \t]+#+[ \t]*$/, '');
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
  if (Array.isArray(value.oneOf)) {
    const variants=shallow(value.oneOf);
    value.oneOf.forEach((child,i)=>put(variants,String(i),visit(child,`${pointer}/oneOf/${i}`)));
    put(value,'oneOf',variants);
  }
  return value;
}

export function expandSource(input, files) {
  return expand(input, files, new Map());
}
function expand({ path: consumer, text, format }, files, documents) {
  const references = new Map(), expandedTargets = new Map(), collectors = [];
  const error = (code, target, detail, chain) => fail(code, consumer, target, detail, chain);
  const tooBig = (target,chain = []) => error('contract-invalid',target,'expanded source is too big (limit 10485760 bytes)',chain);
  const bounded = (value,target,chain = []) => writeJson(value,{collect:false,tooBig:()=>tooBig(target,chain)});
  function load(path, requested, chain) {
    if (documents.has(path)) return documents.get(path);
    let stat, content;
    try {
      stat = files.stat({ path });
      if (!stat?.exists) error('contract-missing', requested, `missing file ${path}`, chain);
      if (stat.is_symlink) error('contract-unsafe', requested, 'symbolic link', chain);
      if (stat.size > LIMIT) tooBig(requested,chain);
      content = files.read({ path }).content;
      if (typeof content !== 'string') throw new Error('Invalid content');
    } catch (cause) {
      if (typeof cause?.code==='string' && cause.code.startsWith('contract-')) throw cause;
      error('contract-unsafe', requested, `cannot safely read ${path}`, chain);
    }
    const document = {content};
    documents.set(path, document);
    return document;
  }
  function target(requested, kind, chain) {
    if (typeof requested !== 'string') error(kind === 'seed' ? 'seed-invalid' : 'contract-invalid', String(requested), 'reference must be a string', chain);
    const hash = requested.indexOf('#'), path = hash < 0 ? requested : requested.slice(0, hash), selection = hash < 0 ? '' : requested.slice(hash + 1);
    if (!path || /^[~/]|^[a-z][a-z0-9+.-]*:/i.test(path) || /[\\\x00-\x1f\x7f]/.test(path) || path.split('/').some(part => !part || part === '.' || part === '..')) error('contract-unsafe', requested, 'use a safe repository-root path', chain);
    if (kind === 'seed' && (hash >= 0 || !path.endsWith('.json'))) error('seed-invalid', requested, 'seed must name a JSON file without a fragment', chain);
    const loaded = load(path, requested, chain), {content} = loaded;
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
      if (!loaded.parsed) { loaded.parsed = true; try { loaded.value = parse(content); } catch { loaded.invalid = true; } }
      if (loaded.invalid) error('contract-invalid', requested, 'file contains invalid JSON', chain);
      value = loaded.value;
      const tokens = pointerTokens(selection, () => error('contract-invalid', requested, 'invalid JSON Pointer', chain));
      for (const key of tokens) {
        if (!member(value, key)) error('contract-missing', requested, `missing JSON Pointer ${selection}`, chain);
        value = value[key];
      }
      canonical = `${path}#${tokens.length ? `/${tokens.map(escape).join('/')}` : ''}`;
    } else error('contract-invalid', requested, 'target must be Markdown or JSON', chain);
    if (!object(value)) error(kind === 'seed' ? 'seed-invalid' : 'contract-invalid', requested, 'selected value must be an object', chain);
    if (chain.includes(canonical)) error('contract-cycle', requested, 'reference cycle', [...chain, canonical]);
    return { value, canonical };
  }
  function record(pointer, canonical, kind, value) {
    for (const collector of collectors) collector.set(`${kind}:${canonical}`,{canonical,kind,value});
    if (references.has(JSON.stringify([consumer,pointer,canonical,kind]))) return;
    const ref = { consumer, source_pointer: pointer, target: canonical, kind, value_json: writeJson(value,{canonical:true,tooBig:()=>tooBig(canonical)}) };
    references.set(JSON.stringify([consumer,pointer,canonical,kind]), ref);
  }
  function schema(value, pointer, chain = [], originating = null) {
    if (!object(value)) return value;
    if (Object.hasOwn(value, '$contract')) {
      if (typeof value.$contract !== 'string' || Object.keys(value).some(key => !['$contract','title','description'].includes(key)) || ['title','description'].some(key => Object.hasOwn(value,key) && typeof value[key] !== 'string')) error('contract-invalid', String(value.$contract), 'only string title and description may accompany $contract', chain);
      const origin = originating ?? pointer, { value: selected, canonical } = target(value.$contract, 'contract', chain);
      let cached = expandedTargets.get(canonical);
      if (!cached) {
        const dependencies = new Map(); collectors.push(dependencies);
        let expanded;
        try { expanded = schema(selected, origin, [...chain, canonical], origin); } finally { collectors.pop(); }
        bounded(expanded,canonical,chain);
        cached = {expanded, dependencies:[...dependencies.values()]};
        expandedTargets.set(canonical,cached);
      } else for (const ref of cached.dependencies) record(origin,ref.canonical,ref.kind,ref.value);
      record(origin, canonical, 'contract', cached.expanded);
      const result = shallow(cached.expanded);
      for (const key of keysOf(value)) if (['title','description'].includes(key)) put(result,key,value[key]);
      bounded(result,canonical,chain);
      return result;
    }
    const result = shallow(value);
    if (object(value.properties)) put(result,'properties',shallow(value.properties));
    schemaChildren(result, pointer, (child, childPointer) => schema(child, childPointer, chain, originating));
    if (chain.length || references.size) bounded(result,chain.at(-1) ?? consumer,chain);
    return result;
  }
  function seed(value, pointer, chain = []) {
    if (!object(value) || !Object.hasOwn(value, '$seed')) return value;
    if (typeof value.$seed !== 'string' || Object.keys(value).some(key => !['$seed','set'].includes(key)) || (Object.hasOwn(value,'set') && !object(value.set))) error('seed-invalid', String(value.$seed), 'invalid shared world or overrides', chain);
    const { value: selected, canonical } = target(value.$seed, 'seed', chain);
    let world = seed(selected, pointer, [...chain, canonical]);
    record(pointer, canonical, 'seed', world);
    bounded(world,canonical,chain);
    world = clone(world);
    for (const raw of keysOf(value.set ?? {})) {
      const replacement = value.set[raw];
      const invalid = () => error('seed-invalid', value.$seed, `invalid override pointer ${raw}`, chain);
      const tokens = pointerTokens(raw, invalid);
      if (!tokens.length) { if (!object(replacement)) invalid(); world = clone(replacement); continue; }
      let parent = world;
      for (const key of tokens.slice(0,-1)) { if (!member(parent,key)) invalid(); parent = parent[key]; }
      const key = tokens.at(-1);
      if (!object(parent) && !Array.isArray(parent)) invalid();
      if (Array.isArray(parent) && !member(parent,key)) invalid();
      put(parent, key, clone(replacement));
      bounded(world,canonical,chain);
    }
    return world;
  }
  let document, block;
  if (format === 'prompt') {
    const blocks = [...text.matchAll(INTERFACE)];
    if (blocks.length !== 1) return { text, references: [] };
    block = blocks[0];
    try { document = clone(parse(block[1])); } catch { return { text, references: [] }; }
    schemaSlots(document, (value,pointer) => schema(value,pointer));
  } else {
    try { document = clone(parse(text)); } catch { return { text, references: [] }; }
    if (format === 'json-schema') document = schema(document, '');
    else if (format === 'scenario' && object(document) && Object.hasOwn(document, 'initial_world')) put(document,'initial_world',seed(document.initial_world, '/initial_world'));
  }
  if (!references.size) return { text, references: [] };
  const result = render(document,()=>tooBig([...references.values()].at(-1).target));
  const outsideSize = block ? Buffer.byteLength(text.slice(0,block.indices[1][0])) + Buffer.byteLength(text.slice(block.indices[1][1])) : Buffer.byteLength(text) - Buffer.byteLength(text.trim());
  if (outsideSize + Buffer.byteLength(result) > LIMIT) tooBig([...references.values()].at(-1).target);
  const effective = block ? `${text.slice(0,block.indices[1][0])}${result}${text.slice(block.indices[1][1])}` : `${text.slice(0,text.search(/\S/))}${result}${text.slice(text.trimEnd().length)}`;
  if (Buffer.byteLength(effective) > LIMIT) tooBig([...references.values()].at(-1).target);
  return { text: effective, references: [...references.values()].sort((a,b) => {
    for (const key of ['consumer','source_pointer','target','kind']) { if (a[key] !== b[key]) return a[key] < b[key] ? -1 : 1; }
    return 0;
  }) };
}

export function catalogRecords(sources, targets = []) {
  const map = new Map(sources.map(source => [source.path, source.text])), records = [], warnings = [], documents = new Map();
  const files = { stat: ({path}) => ({ exists: map.has(path), is_symlink: false, size: Buffer.byteLength(map.get(path) ?? '') }), read: ({path}) => ({ content: map.get(path) }) };
  const candidates = new Set(targets);
  for (const {path,text} of sources) {
    if (path.endsWith('.md')) for (const section of sections(text)) if (section.blocks.length) candidates.add(`${path}#${section.title}`);
    if (path.endsWith('.json')) {
      try {
        const root = parse(text);
        documents.set(path,{content:text,value:root,parsed:true});
        if (object(root)) candidates.add(`${path}#`);
        const walk = (value, pointer) => {
          if (object(value) && object(value.properties)) candidates.add(`${path}#${pointer}`);
          if (object(value) || Array.isArray(value)) for (const [key,child] of Object.entries(value)) walk(child, `${pointer}/${escape(key)}`);
        };
        walk(root,'');
      } catch { documents.set(path,{content:text,parsed:true,invalid:true}); warnings.push(`${path}: invalid JSON contract`); }
    }
  }
  for (const target of [...candidates].sort()) {
    try {
      const path = target.split('#')[0];
      if (target === `${path}#` && path.endsWith('.json') && object(documents.get(path)?.value) && Object.hasOwn(documents.get(path).value, '$seed')) {
        const expanded = expand({ path, text: JSON.stringify({ initial_world: { $seed:path } }), format:'scenario' }, files, documents);
        records.push({path,target,value_json:encode(parse(expanded.text).initial_world)});
        continue;
      }
      const expanded = expand({ path: target.split('#')[0], text: JSON.stringify({$contract:target}), format: 'json-schema' }, files, documents);
      const own = expanded.references.find(ref => ref.target === target) ?? expanded.references.find(ref => ref.source_pointer === '' && ref.kind === 'contract');
      if (own && !records.some(record => record.target === own.target)) records.push({ path: own.target.split('#')[0], target: own.target, value_json: own.value_json });
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
function identity(value) {
  if (value instanceof JsonNumber) return `n:${numericIdentity(value.text)}`;
  if (Array.isArray(value)) return `[${value.map(identity).join(',')}]`;
  if (object(value)) return `{${Object.keys(value).sort().map(key=>`${JSON.stringify(key)}:${identity(value[key])}`).join(',')}}`;
  return JSON.stringify(value);
}
function differences(a,b,pointer = '', root = true, schema = true, unordered = false) {
  if (a instanceof JsonNumber && b instanceof JsonNumber) return numericIdentity(a.text) === numericIdentity(b.text) ? [] : [`${pointer}: ${a.text} -> ${b.text}`];
  if (object(a) && object(b)) return [...new Set([...Object.keys(a),...Object.keys(b)])].sort().flatMap(key => {
    if (root && ['title','description'].includes(key)) return [];
    const path = `${pointer}/${escape(key)}`;
    if (!Object.hasOwn(a,key)) return [`${path}: missing in copy`];
    if (!Object.hasOwn(b,key)) return [`${path}: extra in copy`];
    if (schema && key === 'properties' && object(a[key]) && object(b[key])) {
      return [...new Set([...Object.keys(a[key]),...Object.keys(b[key])])].sort().flatMap(name => {
        const nested = `${path}/${escape(name)}`;
        if (!Object.hasOwn(a[key],name)) return [`${nested}: missing in copy`];
        if (!Object.hasOwn(b[key],name)) return [`${nested}: extra in copy`];
        return differences(a[key][name],b[key][name],nested,false,true);
      });
    }
    return differences(a[key],b[key],path,false,schema && ['items','oneOf'].includes(key),schema && ['required','enum'].includes(key));
  });
  if (Array.isArray(a) && Array.isArray(b)) {
    if (unordered) return a.map(identity).sort().join('\n') === b.map(identity).sort().join('\n') ? [] : [`${pointer}: ${encode(a)} -> ${encode(b)}`];
    return a.length !== b.length ? [`${pointer}: ${encode(a)} -> ${encode(b)}`] : a.flatMap((child,i) => differences(child,b[i],`${pointer}/${i}`,false,schema));
  }
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
      if (value.type==='object' && object(value.properties) && Object.keys(value.properties).length >= 3) {
        const keys = new Set(Object.keys(value.properties));
        const options = candidates.filter(record => {
          const other = new Set(Object.keys(record.value.properties));
          return [...keys].filter(key => !other.has(key)).length + [...other].filter(key => !keys.has(key)).length <= 1;
        }).map(record => ({ record, differences: differences(value,record.value) })).filter(option => !option.differences.length || Object.keys(option.record.value.properties).length >= 4);
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
    try { document = clone(parse(block[1])); } catch { continue; }
    const replaced = [];
    for (const match of selected) {
      if (replaced.some(parent => match.source_pointer.startsWith(`${parent}/`))) continue;
      const tokens = pointerTokens(match.source_pointer, () => fail('contract-invalid',path,match.target,'invalid schema location'));
      let parent = document;
      for (const key of tokens.slice(0,-1)) { if (!member(parent,key)) { parent = null; break; } parent = parent[key]; }
      const key = tokens.at(-1), value = parent?.[key];
      if (!object(value) || Object.hasOwn(value,'$contract')) continue;
      const reference = { $contract: match.target };
      for (const annotation of keysOf(value).filter(key=>['title','description'].includes(key))) put(reference,annotation,clone(value[annotation]));
      const layout = layouts.get(value);
      if (layout) {
        const entries = layout.entries, first = entries[0];
        const prefix = first ? layout.text.slice(layout.start+1,first.keyStart) : '';
        const colon = first ? layout.text.slice(first.keyEnd,first.start) : ':';
        const separator = entries.length>1 ? layout.text.slice(entries[0].end,entries[1].keyStart) : `,${prefix}`;
        const suffix = entries.length ? layout.text.slice(entries.at(-1).end,layout.end-1) : '';
        const rendered = `{${prefix}${keysOf(reference).map(key=>`${JSON.stringify(key)}${colon}${render(reference[key])}`).join(separator)}${suffix}}`;
        put(parent,key,parse(rendered));
      } else put(parent,key,reference); replaced.push(match.source_pointer);
    }
    if (!replaced.length) continue;
    if (document.status === 'approved') document.status = 'draft';
    const after = `${text.slice(0,block.indices[1][0])}${render(document)}${text.slice(block.indices[1][1])}`;
    if (after !== text) edits.push({path,before:text,after});
  }
  return { edits, warnings };
}

export { parse as parseJsonValue, encode as stringifyJsonValue };
export const isJsonNumber = value => value instanceof JsonNumber;
export function jsonNumberIdentity(value) {
  if (value instanceof JsonNumber) return numericIdentity(value.text);
  if (typeof value === "number" && Number.isFinite(value)) return numericIdentity(JSON.stringify(value));
  throw new TypeError("Expected a JSON numeric atom or finite number.");
}

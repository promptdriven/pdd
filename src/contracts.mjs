// Generated from prompts/cli/contracts.prompt.md (sha256: c1d30d6f033aa932d601d661b68ef610d1302882d2315149d6445636c4a13d54).
import { randomUUID } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { closeSync, constants, fchmodSync, fstatSync, lstatSync, openSync, renameSync, unlinkSync, writeSync } from 'node:fs';
import { basename, dirname, join, posix } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { catalogRecords, compareCopies, expandSource, planSync, parseJsonValue, stringifyJsonValue, jsonNumberText, schemaValuesEqual } from './contract-refs.mjs';
import { captureSource, findTests, gitFiles, sourceFilePort, LIMITS, TEST_SCHEMA, validateContract, schemaKeywordNames } from './runtime-preflight.mjs';
import { readContractHistory } from './runtime-client.mjs';

const line = (stream,text) => stream.write(`${text}\n`);
const finite = error => String(error.message ?? error).replace(/[\r\n\x00-\x1f\x7f]/g,' ').slice(0,4000);
const snapshotMap = references => new Map(references.map(ref=>[`${ref.kind}:${ref.target}`,ref.value_json]));

export function runContracts({words = [],options = {},cwd = process.cwd()} = {}, {env = process.env,stdout = process.stdout,stderr = process.stderr} = {}) {
  if (options['--json']!==undefined && (options['--json']!==true || options['--check']!==true) || words.length>1 || words.length===1 && words[0]!=='sync' || Object.keys(options).some(key=>!['--write','--check','--json'].includes(key)) || options['--check']!==undefined && (options['--check']!==true || words.length>0 || options['--write']!==undefined) || options['--write']!==undefined && (words[0]!=='sync' || options['--write']!==true)) {
    line(stderr,'Use pdd contracts or pdd contracts sync [--write].'); return 2;
  }
  const git=spawnSync('git',['rev-parse','--show-toplevel'],{cwd,encoding:'utf8'});
  if (git.status!==0 || !git.stdout.trim()) { line(stderr,'pdd contracts works in a Git repository.'); return 2; }
  const root=git.stdout.trim();
  if (options['--check'] === true) return checkContracts(root,{stdout,stderr,json:options['--json']===true});
  try {
    const visible=new Set(gitFiles(root)), files=sourceFilePort(root,visible);
    const warnings = [];
    const readDiscovered = path => {
      if (files.stat({path}).size > LIMITS.bytes) { warnings.push(`${path}: discovery/catalog unavailable (too big; limit 10 MB).`); return []; }
      return [{path,text:files.read({path}).content}];
    };
    const sources=[...visible].sort().filter(path=>path.startsWith('contracts/') && /\.(?:md|json)$/.test(path)).flatMap(readDiscovered);
    const promptPaths=[...visible].sort().filter(path=>path.endsWith('.prompt.md'));
    const prompts=promptPaths.flatMap(readDiscovered);
    const found=findTests({root,files:[...visible]});
    warnings.push(...found.warnings.map(warning=>warning.replace(/^Warning: /,'')));
    const prepared=[];
    for (const source of prompts) {
      try { prepared.push({...source,...expandSource({...source,format:'prompt'},files)}); }
      catch (error) { warnings.push(`${source.path}: current uses unavailable: ${finite(error)}`); }
    }
    // Listing has no selected runtime program. Isolate unavailable consumers so
    // one unfinished sibling cannot hide every independent record and Story.
    const stories=new Map(), selectedReferences=[];
    for (const test of found.tests) {
      if (stories.has(test.doc?.story_path) && !stories.get(test.doc.story_path).selectedUnavailable) continue;
      try {
        const captured=captureSource(root,{tests:[test.path]});
        selectedReferences.push(...captured.references);
        for (const story of captured.stories) stories.set(story.story_path,story);
      } catch (error) {
        const cause=finite(error); warnings.push(`${test.path}: footprint unavailable: ${cause}`);
        if (typeof test.doc?.story_path==='string') stories.set(test.doc.story_path,{story_path:test.doc.story_path,tests:[test.path],selectedUnavailable:true,unavailable:[{path:test.path,cause}]});
      }
    }
    const capture={stories:[...stories.values()]};
    const references=[...prepared.flatMap(source=>source.references),...selectedReferences,...capture.stories.flatMap(story=>story.references ?? [])];
    for (const warning of warnings) line(stderr,`Warning: ${warning}`);
    const catalog=catalogRecords(sources,references.map(ref=>ref.target));
    for (const warning of catalog.warnings) line(stderr,`Warning: ${warning}`);
    if (words[0]==='sync') {
      const compared=compareCopies(prompts,catalog.records), plan=planSync(prompts,compared.matches);
      for (const warning of [...compared.warnings,...plan.warnings]) line(stderr,`Warning: ${warning}`);
      for (const match of compared.matches) line(stdout,`${match.path} ${match.source_pointer} -> ${match.target}${match.differences.length ? `; adopts ${match.differences.join('; ')}` : '; exact copy'}`);
      if (options['--write']!==true) { line(stdout,`Preview: ${plan.edits.length} files. Use --write to apply.`); return 0; }
      let failures=0,changed=0;
      for (const edit of plan.edits) {
        let fd, temporary, owned;
        try {
          const path=join(root,edit.path), before=lstatSync(path,{bigint:true});
          const ancestors = () => {
            const parts = edit.path.split('/'), result = [];
            for (let i=1;i<parts.length;i++) {
              const parent = lstatSync(join(root,...parts.slice(0,i)),{bigint:true});
              if (!parent.isDirectory() || parent.isSymbolicLink()) throw new Error('destination ancestor changed since preview');
              result.push([parent.dev,parent.ino]);
            }
            return result;
          };
          const parents = ancestors();
          const current=sourceFilePort(root,new Set(gitFiles(root)));
          if (current.read({path:edit.path}).content!==edit.before) throw new Error('source changed since preview');
          const sameIdentity = stat => stat.isFile() && stat.dev===before.dev && stat.ino===before.ino && stat.size===before.size && stat.mtimeNs===before.mtimeNs && stat.ctimeNs===before.ctimeNs;
          // Exclusive preparation leaves the complete destination visible until
          // the final rename; no destination descriptor is ever truncated.
          for (let attempt=0;attempt<100;attempt++) {
            const candidate=join(dirname(path),`.pdd-sync-${randomUUID()}.tmp`);
            try { fd=openSync(candidate,constants.O_WRONLY|constants.O_CREAT|constants.O_EXCL|constants.O_NOFOLLOW,Number(before.mode & 0o777n)); temporary=candidate; break; }
            catch (error) { if (error.code!=='EEXIST') throw error; }
          }
          if (fd===undefined) throw new Error('cannot prepare exclusive temporary file');
          owned=fstatSync(fd,{bigint:true});
          fchmodSync(fd,Number(before.mode & 0o777n));
          const bytes=Buffer.from(edit.after,'utf8');
          let offset=0;
          while (offset<bytes.length) { const written=writeSync(fd,bytes,offset,bytes.length-offset,offset); if (!written) throw new Error('temporary write made no progress'); offset+=written; }
          const prepared=fstatSync(fd,{bigint:true});
          if (!prepared.isFile() || prepared.size!==BigInt(bytes.length) || prepared.dev!==owned.dev || prepared.ino!==owned.ino) throw new Error('temporary file changed');
          closeSync(fd); fd=undefined;
          if (!sameIdentity(lstatSync(path,{bigint:true})) || !isDeepStrictEqual(parents,ancestors())) throw new Error('destination changed since preview');
          if (sourceFilePort(root,new Set(gitFiles(root))).read({path:edit.path}).content!==edit.before) throw new Error('source changed since preview');
          const tempNow=lstatSync(temporary,{bigint:true});
          if (tempNow.isSymbolicLink() || tempNow.dev!==owned.dev || tempNow.ino!==owned.ino || !sameIdentity(lstatSync(path,{bigint:true})) || !isDeepStrictEqual(parents,ancestors())) throw new Error('destination or temporary file changed since preview');
          renameSync(temporary,path); temporary=undefined;
          changed++; line(stdout,`Updated ${edit.path}`);
        } catch (error) { failures++; line(stderr,`Refused ${edit.path}: ${finite(error)}`); }
        finally { if (fd!==undefined) closeSync(fd); if (temporary!==undefined) { try { const remaining=lstatSync(temporary,{bigint:true}); if (owned && remaining.dev===owned.dev && remaining.ino===owned.ino) unlinkSync(temporary); } catch {} } }
      }
      line(stdout,`Sync: ${changed} files updated, ${failures} refused.`);
      return failures ? 4 : 0;
    }
    const history=readContractHistory({root,env});
    for (const warning of history.warnings) line(stderr,`Warning: ${warning}`);
    const unknownStories=capture.stories.some(story=>story.unavailable?.length);
    const unknownUses=prepared.length<promptPaths.length || unknownStories;
    for (const record of catalog.records) {
      const users=[...new Set(references.filter(ref=>ref.target===record.target).map(ref=>ref.consumer))].sort();
      const stories=capture.stories.filter(story=>story.references?.some(ref=>ref.target===record.target)).map(story=>story.story_path).sort();
      const userEvidence=users.length ? `${users.join(', ')}${unknownUses?' (incomplete)':''}` : unknownUses?'unavailable':'none';
      line(stdout,`${record.target}  owner: ${record.path}  users: ${userEvidence}  Stories: ${stories.join(', ')||(unknownStories?'unavailable':'none')}`);
    }
    for (const story of capture.stories) {
      if (story.unavailable?.length) { line(stdout,`${story.story_path}: footprint unavailable (${story.unavailable.map(item=>item.cause).join('; ')})`); continue; }
      const baseline=history.stories.find(row=>row.story_path===story.story_path);
      if (history.warnings.length) { line(stdout,`${story.story_path}: baseline unavailable`); continue; }
      if (!baseline || baseline.baseline==='not-checked') { line(stdout,`${story.story_path}: not checked`); continue; }
      if (baseline.baseline==='unavailable' || history.warnings.length) { line(stdout,`${story.story_path}: baseline unavailable`); continue; }
      const before=snapshotMap(baseline.references), current=snapshotMap(story.references);
      const changed=[...new Set([...before.keys(),...current.keys()])].filter(key=>before.get(key)!==current.get(key));
      for (const identity of changed) line(stdout,`${identity.slice(identity.indexOf(':')+1)}: changed since the last check (${story.story_path})`);
      const stale=changed.length || !isDeepStrictEqual(baseline.files,story.files);
      line(stdout,`${story.story_path}: ${stale?'stale: needs a new check':'current'} (last check ${baseline.result_state}, ${baseline.checked_at})`);
    }
    if (!catalog.records.length) line(stdout,'No shared contract records found.');
    return 0;
  } catch (error) { line(stderr,finite(error)); return error.exitCode ?? (error.code?.startsWith('contract-') || error.code==='seed-invalid' ? 4 : 5); }
}

// --check has no dependency on saved Check history or capture/upload state.
function checkContracts(root,{stdout,stderr,json = false}) {
  const diagnostics = [], warnings = [], skipped = new Set();
  const report = (file,record,field,message,unknown = false,provenance = {}) => diagnostics.push({file,record,field,kind:unknown?'unavailable':'problem',message,...provenance});
  const isUnavailable = error => error.localContractUnavailable === true || error.exitCode === 5 || typeof error.code === 'string' && !error.code.startsWith('contract-') && error.code !== 'seed-invalid';
  let checkedRecords = 0, checkedValues = 0;
  try {
    const visible = new Set(gitFiles(root)), nativePort = sourceFilePort(root,visible);
    let ioFailure = false;
    const port = Object.fromEntries(['stat','read'].map(operation => [operation,args => {
      try { return nativePort[operation](args); }
      catch (error) { if (isUnavailable(error)) ioFailure = true; throw error; }
    }]));
    const expand = input => {
      ioFailure = false;
      try { return expandSource(input,port); }
      catch (error) { if (ioFailure) error.localContractUnavailable = true; throw error; }
    };
    const sources = [], prompts = [], uses = [], seeds = new Set(['contracts/seed-world.json']);
    const read = path => {
      const stat = port.stat({path});
      if (stat.size > LIMITS.bytes) { report(path,path,'','source exceeds the local validation size limit',true); return null; }
      return {path,text:port.read({path}).content};
    };
    for (const path of [...visible].sort()) {
      if (path.startsWith('contracts/') && /\.(?:md|json)$/.test(path)) {
        try { const source = read(path); if (source) sources.push(source); }
        catch (error) { report(path,path==='contracts/world.md'?'world':path,'',finite(error),isUnavailable(error)); }
      }
      if (path.endsWith('.prompt.md')) {
        try { const source = read(path); if (source) prompts.push(source); }
        catch (error) { report(path,path,'',finite(error),isUnavailable(error)); }
      }
    }
    const consume = (source,format) => {
      try {
        const expanded = expand({...source,format});
        uses.push(...expanded.references);
        for (const ref of expanded.references) if (ref.kind === 'seed') seeds.add(ref.target.split('#')[0]);
      } catch (error) { report(source.path,source.path,'',finite(error),isUnavailable(error)); }
    };
    for (const source of prompts) consume(source,'prompt');
    // Scenario discovery uses the same version family and size admission as
    // preflight, but every body read here goes through its safe snapshot port.
    const scenarioFamily = TEST_SCHEMA.slice(0,TEST_SCHEMA.lastIndexOf('.'));
    for (const path of [...visible].sort().filter(path => path.endsWith('.json'))) {
      try {
        const stat = port.stat({path});
        if (stat.size > LIMITS.test) continue;
        const source = read(path);
        if (!source || !source.text.includes(scenarioFamily)) continue;
        let document;
        try { document = parseJsonValue(source.text); }
        catch { report(path,'scenario discovery','','cannot establish uses from malformed scenario JSON',true); continue; }
        if (typeof document?.schema_version === 'string' && document.schema_version.startsWith(scenarioFamily)) consume(source,'scenario');
      } catch (error) { report(path,'scenario discovery','',finite(error),true); }
    }
    const worldPath = 'contracts/world.md', seedPath = 'contracts/seed-world.json';
    const hasWorld = visible.has(worldPath), hasSeed = visible.has(seedPath);
    if (hasWorld !== hasSeed) report(hasWorld ? seedPath : worldPath,'world','','missing world/seed partner');
    let seedWorld;
    if (hasSeed) {
      try {
        const expanded = expand({path:seedPath,text:JSON.stringify({initial_world:{$seed:seedPath}}),format:'scenario'});
        seedWorld = parseJsonValue(expanded.text).initial_world;
        for (const ref of expanded.references) if (ref.kind === 'seed') seeds.add(ref.target.split('#')[0]);
      } catch (error) { report(seedPath,'world','',finite(error),isUnavailable(error)); }
    }
    const selected = new Map(), rows = new Map(), authorities = new Set();
    const escape = key => key.replace(/~/g,'~0').replace(/\//g,'~1');
    let tableKind;
    const select = (target,file,field,record = target, authority = true) => {
      try {
        const expanded = expand({path:file,text:JSON.stringify({$contract:target}),format:'json-schema'});
        const references = expanded.references.filter(ref => ref.kind === 'contract');
        // Literal/JSON identities are already canonical. For a Markdown alias,
        // let the same resolver identify the outer record by its full dependency
        // closure, rather than reproducing heading/fragment resolution here.
        const identities = new Set(references.map(ref => ref.target));
        const outer = references.find(ref => ref.target === target) ?? references.find(ref => {
          if (ref.target.split('#')[0] !== target.split('#')[0]) return false;
          const probe = expand({path:file,text:JSON.stringify({$contract:ref.target}),format:'json-schema'});
          return probe.references.length === identities.size && probe.references.every(item => identities.has(item.target));
        });
        const canonical = outer?.target;
        if (!canonical) throw new Error('selected schema could not be resolved');
        selected.set(canonical,{file:canonical.split('#')[0],field,record:canonical,expanded:expanded.text});
        if (authority) authorities.add(canonical);
        uses.push(...expanded.references);
        return canonical;
      } catch (error) { report(file,record,field,finite(error),isUnavailable(error)); return null; }
    };
    const world = sources.find(source => source.path === worldPath);
    if (hasWorld && hasSeed && world) {
      const unquote = text => text.trim().replace(/^`([^`]*)`$/, '$1');
      let fence = null, table = null;
      const lines = world.text.split(/\r?\n/);
      for (let i=0;i<lines.length;i++) {
        const marker = /^ {0,3}(`{3,}|~{3,})/.exec(lines[i]);
        if (marker) { if (!fence) fence=marker[1][0]; else if (fence===marker[1][0]) fence=null; continue; }
        if (fence || !lines[i].includes('|')) continue;
        const cells = line => line.trim().replace(/^\|/,'').replace(/\|$/,'').split('|').map(cell => cell.trim());
        const headings = cells(lines[i]);
        if ((!headings.includes('Key') && !headings.includes('Path')) || !headings.includes('Writer') || !/^\s*\|?\s*:?-+/.test(lines[i+1] ?? '')) continue;
        table = {headings,values:[]};
        for (i+=2;i<lines.length && lines[i].trim().includes('|');i++) table.values.push(cells(lines[i]));
        break;
      }
      if (!table) report(worldPath,'world','','missing Key/Writer ownership table');
      else {
        tableKind = table.headings.includes('Key') ? 'Key' : 'Path';
        for (const cells of table.values) {
          const get = name => cells[table.headings.indexOf(name)] ?? '';
          const raw = get(tableKind), actors = unquote(get('Writer')).split(/,|\band\b|\//).map(unquote).filter(Boolean), target = unquote(get('Schema'));
          const quoted = [...raw.matchAll(/`([^`]*)`/g)].map(match => match[1]);
          const keys = tableKind === 'Path' && quoted.length ? quoted : [unquote(raw)];
          for (const key of keys) {
            if (!key) { report(worldPath,'world',tableKind,'missing key/path'); continue; }
            if (tableKind === 'Path' && !key.startsWith('/') || key.startsWith('/') && /~(?![01])/.test(key)) {
              report(worldPath,key,tableKind,'use a valid absolute JSON Pointer'); continue;
            }
            const pointer = key.startsWith('/') ? key : `/${escape(key)}`;
            const tokens = pointer.slice(1).split('/').map(token => token.replace(/~1/g,'/').replace(/~0/g,'~'));
            const canonical = target ? select(target,worldPath,'Schema',target) : null;
            const old = rows.get(pointer);
            if (old?.canonical && canonical && old.canonical !== canonical) report(worldPath,key,'Schema','conflicting schema mappings');
            if (!old) rows.set(pointer,{key,tokens,actors:new Set(actors),canonical,explicit:!!target,evidence:[cells.join(' ')]});
            else {
              for (const actor of actors) old.actors.add(actor);
              old.evidence.push(cells.join(' '));
              old.explicit ||= !!target;
              if (!old.canonical && canonical) old.canonical = canonical;
            }
          }
        }
      }
    }
    // Explicit consumer selections establish schema roles, including empty leaves.
    for (const ref of uses) if (ref.kind === 'contract') {
      authorities.add(ref.target);
      if (!selected.has(ref.target)) selected.set(ref.target,{file:ref.target.split('#')[0],field:'',record:ref.target,expanded:ref.value_json});
    }
    for (const row of rows.values()) if (row.actors.size !== 1) report(worldPath,row.key,'Writer','declare exactly one unique writer');
    const annotations = new Set(['enum','const','default','examples','title','description','format']);
    const markers = new Set([...schemaKeywordNames(),'$contract'].filter(key => !annotations.has(key)));
    const object = value => value !== null && typeof value === 'object' && !Array.isArray(value) && jsonNumberText(value) === null;
    for (const source of sources) if (source.path.endsWith('.json') && !seeds.has(source.path)) {
      let document;
      try { document=parseJsonValue(source.text); } catch { report(source.path,`${source.path}#`,'','invalid JSON'); continue; }
      const leaves = [];
      const discover = (value,pointer) => {
        if (!object(value)) return;
        if (Object.keys(value).some(key => markers.has(key))) { leaves.push(pointer); return; }
        for (const [key,child] of Object.entries(value)) if (!annotations.has(key) && !['resources','simulation'].includes(key)) discover(child,`${pointer}/${escape(key)}`);
      };
      discover(document,'');
      for (const pointer of leaves) {
        const target = `${source.path}#${pointer}`;
        if (!selected.has(target)) select(target,source.path,'',target,pointer === '');
        else if (pointer === '') authorities.add(target);
      }
      if (!leaves.length && ![...selected.keys()].some(target => target.split('#')[0] === source.path)) skipped.add(source.path);
    }
    const catalogSources = new Map(sources.filter(source => !seeds.has(source.path) && !skipped.has(source.path)).map(source => [source.path,source]));
    for (const target of new Set([...selected.keys(),...uses.filter(ref => ref.kind === 'contract').map(ref => ref.target)])) {
      const path = target.split('#')[0];
      if (catalogSources.has(path) || seeds.has(path)) continue;
      try { const source = read(path); if (source) catalogSources.set(path,source); }
      catch (error) { report(path,target,'',finite(error),isUnavailable(error)); }
    }
    const catalog = catalogRecords([...catalogSources.values()],[...selected.keys()].filter(target => !seeds.has(target.split('#')[0])));
    // JSON schema roles have already been selected and expanded above. The
    // advisory catalog also explores literal business objects in those files;
    // only Markdown record discovery supplies additional required diagnostics.
    const markdownSources = [...catalogSources.keys()].filter(path => path.endsWith('.md'));
    for (const warning of catalog.warnings) if (markdownSources.some(path => warning.startsWith(`${path}: `))) {
      report(warning.split(':')[0],warning.split(':')[0],'',warning);
    }
    for (const record of catalog.records) {
      if (seeds.has(record.path)) continue;
      if (record.path.endsWith('.md')) {
        authorities.add(record.target);
        if (!selected.has(record.target)) select(record.target,record.path,'');
      }
    }
    const schemas = new Map();
    for (const [target,source] of selected) {
      if (seeds.has(target.split('#')[0])) continue;
      try {
        const result = validateContract({schema_json:source.expanded});
        checkedRecords++;
        if (!result.schema_problems.length && !result.unproved.length) schemas.set(target,source.expanded);
        for (const item of result.schema_problems) report(source.file,source.record,item.pointer,item.rule);
        for (const item of result.unproved) report(source.file,source.record,item.pointer,item.rule,true);
      } catch (error) { report(source.file,source.record,source.field,finite(error)); }
    }
    // Row inference uses only known valid records. Resolution supplies canonical
    // identities; incidental JSON members gain authority only when a row selects them.
    const names = new Map();
    for (const target of schemas.keys()) {
      const [path,fragment] = target.split('#');
      const name = fragment?.startsWith('/') ? fragment.split('/').at(-1).replace(/~1/g,'/').replace(/~0/g,'~') : fragment || basename(path,'.json');
      if (!names.has(name)) names.set(name,new Set());
      names.get(name).add(target);
    }
    for (const row of rows.values()) {
      if (row.explicit) continue;
      const candidates = new Set();
      for (const evidence of row.evidence) {
        for (const [name,targets] of names) {
          // Boundaries are exact record tokens, not substring/plural aliases.
          const escaped = name.replace(/[.*+?^${}()|[\]\\]/g,'\\$&');
          if (name && new RegExp(`(?<![\\p{L}\\p{N}_-])${escaped}(?![\\p{L}\\p{N}_-])`,'u').test(evidence.replace(/\[[^\]]*\]\([^)]*\)/g,''))) for (const target of targets) candidates.add(target);
        }
        for (const link of evidence.matchAll(/\[[^\]]*\]\(([^\s)]+)\)/g)) {
          const [path,fragment = ''] = link[1].split('#');
          if (/^[a-z][a-z0-9+.-]*:/i.test(path) || path.startsWith('/')) continue;
          const target = `${path ? posix.normalize(posix.join(dirname(worldPath),path)) : worldPath}#${fragment}`;
          try {
            const expanded = expand({path:worldPath,text:JSON.stringify({$contract:target}),format:'json-schema'});
            // The outer reference is last; transitive dependencies are not row choices.
            const canonical = expanded.references.filter(ref => ref.kind === 'contract').at(-1)?.target;
            if (schemas.has(canonical)) candidates.add(canonical);
          } catch { /* Unknown non-Schema links are only inference evidence. */ }
        }
      }
      if (candidates.size === 1) { row.canonical = [...candidates][0]; authorities.add(row.canonical); }
    }
    const validDeclared = [...schemas].filter(([target]) => authorities.has(target)).map(([target,text]) => ({target,value:parseJsonValue(text)}));
    for (let i=0;i<validDeclared.length;i++) for (let j=i+1;j<validDeclared.length;j++) {
      const a=validDeclared[i],b=validDeclared[j];
      if (a.value.type !== 'object' || b.value.type !== 'object' || !object(a.value.properties) || !object(b.value.properties)) continue;
      if (!isDeepStrictEqual(Object.keys(a.value.properties).sort(),Object.keys(b.value.properties).sort()) || schemaValuesEqual(a.value,b.value)) continue;
      const records=[a.target,b.target].sort();
      warnings.push({kind:'declared-record-disagreement',records,message:`Declared records ${records.join(' and ')} have the same fields but different shapes`});
    }
    const unknownKeys=[...rows].filter(([,row]) => !row.canonical && !row.explicit).map(([pointer]) => pointer).sort();
    if (unknownKeys.length) warnings.push({kind:'world-schema-missing',file:worldPath,world_keys:unknownKeys,message:`${unknownKeys.length} world keys have no schema; their seed values were not checked`});
    const compared = compareCopies(prompts,catalog.records.filter(record => authorities.has(record.target)));
    for (const match of compared.matches) if (match.kind === 'near') for (const difference of match.differences) report(match.path,match.target,difference.split(':')[0],difference,false,{source_pointer:match.source_pointer,target:match.target});
    for (const warning of compared.warnings) report(warning.split(' ')[0],warning,'',warning,true);
    if (hasWorld && hasSeed) {
      try {
        if (tableKind === 'Key') for (const key of Object.keys(seedWorld ?? {})) {
          if (![...rows.values()].some(row => row.tokens[0] === key)) report(seedPath,key,`/${escape(key)}`,'present seed key has no writer declaration');
        }
        for (const [pointer,row] of rows) {
          const {key,tokens} = row;
          let value = seedWorld, present = true;
          for (const token of tokens) {
            if (value === null || typeof value !== 'object' || !Object.hasOwn(value,token)) { present = false; break; }
            value = value[token];
          }
          const schema_json = schemas.get(row.canonical);
          if (!present || !schema_json) continue;
          const result = validateContract({schema_json,value_json:stringifyJsonValue(value)}); checkedValues++;
          for (const item of result.value_problems) report(seedPath,key,`${pointer}${item.pointer}`,item.rule);
          for (const item of result.unproved) report(seedPath,key,`${pointer}${item.pointer}`,item.rule,true);
        }
      } catch (error) { report(seedPath,'world','',finite(error)); }
    }
  } catch (error) { report('contracts/','local contracts','',finite(error),true); }
  const fields = ['file','record','field','kind','source_pointer','target','message'];
  const grouped = new Map();
  for (const item of diagnostics) {
    const identity=JSON.stringify(fields.filter(key=>key!=='message').map(key=>item[key] ?? ''));
    const old=grouped.get(identity);
    if (!old) grouped.set(identity,{...item});
    else if (!old.message.includes(item.message)) old.message=finite(`${old.message}; ${item.message}`);
  }
  const unique=[...grouped.values()];
  unique.sort((a,b) => { for (const key of fields) { const left=a[key] ?? '', right=b[key] ?? ''; if (left!==right) return left<right?-1:1; } return 0; });
  const exit_code = unique.some(item => item.kind==='problem') ? 4 : unique.length ? 5 : 0;
  const skipped_files = [...skipped].sort();
  warnings.sort((a,b) => { const left=[a.kind,a.file ?? '',...(a.records ?? [])].join('\n'),right=[b.kind,b.file ?? '',...(b.records ?? [])].join('\n'); return left<right?-1:left>right?1:0; });
  if (json) line(stdout,JSON.stringify({exit_code,checked_records:checkedRecords,checked_world_values:checkedValues,skipped_files,diagnostics:unique,warnings}));
  else {
    const presentations = new Map();
    for (const item of unique) {
      const identity=JSON.stringify([item.file,item.record,item.field,item.kind,item.target,item.message]);
      if (!presentations.has(identity)) presentations.set(identity,{...item,pointers:[]});
      if (item.source_pointer!==undefined) presentations.get(identity).pointers.push(item.source_pointer);
    }
    for (const item of presentations.values()) line(stderr,`${item.file}: ${item.record} ${item.field}: ${item.kind==='unavailable'?'validation unavailable: ':''}${item.message}${item.pointers.length?` [sources ${item.pointers.join(', ')}]`:''}${item.target!==undefined?` [target ${item.target}]`:''}`);
    for (const warning of warnings) line(stdout,`Warning: ${warning.message}`);
    if (skipped_files.length) line(stdout,`Skipped ${skipped_files.length} files that are not schemas: ${skipped_files.join(', ')}`);
    line(stdout,`Checked ${checkedRecords} records and ${checkedValues} world values.`);
  }
  return exit_code;
}

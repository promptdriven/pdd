// Generated from prompts/cli/contracts.prompt.md (sha256: c1d30d6f033aa932d601d661b68ef610d1302882d2315149d6445636c4a13d54).
import { randomUUID } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { closeSync, constants, fchmodSync, fstatSync, lstatSync, openSync, renameSync, unlinkSync, writeSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { catalogRecords, compareCopies, expandSource, planSync } from './contract-refs.mjs';
import { captureSource, findTests, gitFiles, sourceFilePort, LIMITS } from './runtime-preflight.mjs';
import { readContractHistory } from './runtime-client.mjs';

const line = (stream,text) => stream.write(`${text}\n`);
const finite = error => String(error.message ?? error).replace(/[\r\n\x00-\x1f\x7f]/g,' ').slice(0,4000);
const snapshotMap = references => new Map(references.map(ref=>[`${ref.kind}:${ref.target}`,ref.value_json]));

export function runContracts({words = [],options = {},cwd = process.cwd()} = {}, {env = process.env,stdout = process.stdout,stderr = process.stderr} = {}) {
  if (words.length>1 || words.length===1 && words[0]!=='sync' || Object.keys(options).some(key=>key!=='--write') || options['--write']!==undefined && (words[0]!=='sync' || options['--write']!==true)) {
    line(stderr,'Use pdd contracts or pdd contracts sync [--write].'); return 2;
  }
  const git=spawnSync('git',['rev-parse','--show-toplevel'],{cwd,encoding:'utf8'});
  if (git.status!==0 || !git.stdout.trim()) { line(stderr,'pdd contracts works in a Git repository.'); return 2; }
  const root=git.stdout.trim();
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

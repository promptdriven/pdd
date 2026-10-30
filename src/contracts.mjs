// Generated from prompts/cli/contracts.prompt.md (sha256: 07d4ee96a1bdbfa178ca14eeb9c3e0bcb399e129fc5ff1ff4dec0e3fa4f79690).
import { randomUUID } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { closeSync, constants, fchmodSync, fstatSync, lstatSync, openSync, renameSync, unlinkSync, writeSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { catalogRecords, compareCopies, expandSource, planSync } from './contract-refs.mjs';
import { captureSource, findTests, gitFiles, sourceFilePort } from './runtime-preflight.mjs';
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
    const sources=[...visible].sort().filter(path=>path.startsWith('contracts/') && /\.(?:md|json)$/.test(path)).map(path=>({path,text:files.read({path}).content}));
    const prompts=[...visible].sort().filter(path=>path.endsWith('.prompt.md')).map(path=>({path,text:files.read({path}).content}));
    const found=findTests({root,files:[...visible]});
    const prepared=prompts.map(source=>({...source,...expandSource({...source,format:'prompt'},files)}));
    const capture=captureSource(root,{tests:found.tests.map(test=>test.path)});
    const references=[...prepared.flatMap(source=>source.references),...capture.references];
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
    for (const record of catalog.records) {
      const users=[...new Set(references.filter(ref=>ref.target===record.target).map(ref=>ref.consumer))].sort();
      const stories=capture.stories.filter(story=>story.references.some(ref=>ref.target===record.target)).map(story=>story.story_path).sort();
      line(stdout,`${record.target}  owner: ${record.path}  users: ${users.join(', ')||'none'}  Stories: ${stories.join(', ')||'none'}`);
    }
    for (const story of capture.stories) {
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

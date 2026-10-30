// Generated from prompts/cli/contracts.prompt.md (sha256: a36838188503eced7a1ff5af79f211cc2f194e57a1dbe8e890b1745ed1111a84).
import { spawnSync } from 'node:child_process';
import { closeSync, constants, fstatSync, ftruncateSync, lstatSync, openSync, readFileSync, writeSync } from 'node:fs';
import { join } from 'node:path';
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
        let fd;
        try {
          const path=join(root,edit.path), before=lstatSync(path,{bigint:true});
          const current=sourceFilePort(root,new Set(gitFiles(root)));
          if (current.read({path:edit.path}).content!==edit.before) throw new Error('source changed since preview');
          fd=openSync(path,constants.O_RDWR|constants.O_NOFOLLOW);
          const opened=fstatSync(fd,{bigint:true});
          if (!opened.isFile() || before.ino!==opened.ino || before.dev!==opened.dev || readFileSync(fd,'utf8')!==edit.before) throw new Error('destination changed since preview');
          const after=fstatSync(fd,{bigint:true}), now=lstatSync(path,{bigint:true});
          if (after.ino!==now.ino || after.dev!==now.dev || after.size!==opened.size || after.mtimeNs!==opened.mtimeNs || after.ctimeNs!==opened.ctimeNs) throw new Error('destination changed since preview');
          sourceFilePort(root,new Set(gitFiles(root))).stat({path:edit.path});
          const bytes=Buffer.from(edit.after,'utf8');
          let offset=0;
          while (offset<bytes.length) offset+=writeSync(fd,bytes,offset,bytes.length-offset,offset);
          ftruncateSync(fd,bytes.length);
          changed++; line(stdout,`Updated ${edit.path}`);
        } catch (error) { failures++; line(stderr,`Refused ${edit.path}: ${finite(error)}`); }
        finally { if (fd!==undefined) closeSync(fd); }
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

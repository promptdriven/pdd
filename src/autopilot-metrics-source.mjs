// Generated from prompts/cli/autopilot-metrics-source.prompt.md.
import * as nativeFs from 'node:fs';
import {homedir} from 'node:os';
import {join} from 'node:path';
import {execFile} from 'node:child_process';
import {promisify} from 'node:util';
import {nativeGithubCounter} from './github-calls.mjs';
import {calculateAutopilotMetrics,normalizeAutopilotMetric,parseAutopilotEvidence} from './autopilot-metrics.mjs';

const execute = nativeGithubCounter(promisify(execFile),{purpose:'other'});
const validRepo = repo => typeof repo === 'string' && /^[\w.-]+\/[\w.-]+$/.test(repo) && !repo.split('/').some(part=>part === '.' || part === '..');
const validPr = pr => Number.isSafeInteger(pr) && pr > 0;
const validHead = head => typeof head === 'string' && /^[a-f0-9]{40}$/i.test(head);
function stat(fs,path) {
  try { const entry=fs.lstatSync(path); return entry.isSymbolicLink() ? null : entry; }
  catch(error) { if (['ENOENT','ENOTDIR'].includes(error.code)) return null; throw error; }
}
function text(fs,path) {
  if (!stat(fs,path)?.isFile()) return null;
  try { return fs.readFileSync(path,'utf8'); }
  catch(error) { if (['ENOENT','ENOTDIR'].includes(error.code)) return null; throw error; }
}
function names(fs,path) {
  if (!stat(fs,path)?.isDirectory()) return [];
  try { return fs.readdirSync(path); }
  catch(error) { if (['ENOENT','ENOTDIR'].includes(error.code)) return []; throw error; }
}
function json(raw) { try { return JSON.parse(raw); } catch { return null; } }

async function nativeGithub(repo,path,run=execute) {
  const {stdout}=await run('gh',['api','--paginate','--slurp',`repos/${repo}/${path}?per_page=100`],{maxBuffer:16*1024*1024});
  const pages=JSON.parse(stdout);
  if (path.endsWith('/comments')) return pages.flat();
  if (path.endsWith('/check-runs')) return {check_runs:pages.flatMap(page=>page.check_runs ?? [])};
  return pages[0];
}

export function recordAutopilotMetric({root,...input},ports={}) {
  const event=normalizeAutopilotMetric(input), fs=ports.fs ?? nativeFs;
  if (!event || typeof root !== 'string' || !root) throw Error('Invalid Autopilot metric');
  fs.mkdirSync(root,{recursive:true,mode:0o700});
  const file=join(root,'history.jsonl');
  let prefix='';
  try { const old=fs.readFileSync(file,'utf8'); if (old && !old.endsWith('\n')) prefix='\n'; }
  catch(error) { if (error.code !== 'ENOENT') throw error; }
  fs.appendFileSync(file,prefix+JSON.stringify({metric:event})+'\n',{mode:0o600});
  fs.chmodSync(file,0o600);
}

export async function readAutopilotMetrics({timezone,observedAt},ports={}) {
  const fs=ports.fs ?? nativeFs, env=ports.env ?? process.env;
  const root=ports.stateRoot ?? join(env.HOME || (ports.homedir ?? homedir)(),'.local','state','pdd','autopilot');
  const github=ports.github ?? ((repo,path)=>nativeGithub(repo,path,ports.execFile ?? execute)), events=[], mappings=new Map();
  const add = input => { const event=normalizeAutopilotMetric(input); if (event) events.push(event); };
  const associate = (repo,issue,pr) => {
    if (!validPr(pr)) return;
    const key=`${repo}#${pr}`, mapping=mappings.get(key) ?? {repo,pr,issues:new Set()};
    mapping.issues.add(issue); mappings.set(key,mapping);
  };
  for (const name of names(fs,root).filter(name=>/^[a-f0-9]{20}\.json$/.test(name)).sort()) {
    const state=json(text(fs,join(root,name)));
    if (!validRepo(state?.repo)) continue;
    const repo=state.repo.toLowerCase(), core=join(root,`${name.slice(0,-5)}-core`);
    if (!stat(fs,core)?.isDirectory()) continue;
    for (const line of (text(fs,join(core,'history.jsonl')) ?? '').split('\n')) {
      const row=json(line);
      if (row?.metric) {
        const event=normalizeAutopilotMetric(row.metric);
        if (event?.repo !== repo) continue;
        events.push(event); associate(repo,event.issue,event.pr);
      } else if (['merged','ended','released','handed-over','abandoned','stopped'].includes(row?.outcome)) {
        if (row.outcome === 'merged') add({repo,issue:row.issue,at:row.at,kind:'worked'});
        add({repo,issue:row.issue,at:row.at,kind:row.outcome === 'merged' ? 'merged' : 'worked',...(validPr(row.pr) ? {pr:row.pr} : {})});
        if (Number.isSafeInteger(row.issue) && row.issue > 0) associate(repo,row.issue,row.pr);
      }
    }
    const dir=join(core,'jobs');
    for (const file of names(fs,dir).filter(name=>/^[1-9]\d*\.json$/.test(name))) {
      const job=json(text(fs,join(dir,file)));
      if (job?.schema !== 'pdd.core-job.v1' || job.issue !== Number(file.slice(0,-5))) continue;
      add({repo,issue:job.issue,kind:'started',at:job.started});
      for (const at of [job.prAt,job.agent?.started,job.review?.agent?.started,job.suite?.agent?.started]) add({repo,issue:job.issue,kind:'worked',at});
      if (typeof job.evidence === 'string') add({repo,issue:job.issue,kind:'evidence',at:job.prAt,evidence:job.evidence});
      associate(repo,job.issue,job.pr);
    }
  }
  for (const {repo,pr,issues} of mappings.values()) {
    let pull;
    try { pull=await github(repo,`pulls/${pr}`); } catch { continue; }
    if (!validHead(pull?.head?.sha)) continue;
    const head=pull.head.sha.toLowerCase();
    const actualMerge=normalizeAutopilotMetric({repo,issue:1,kind:'merged',at:pull.merged_at});
    if (actualMerge) for (const event of events) if (event.repo === repo && event.pr === pr && event.kind === 'merged') event.at=actualMerge.at;
    const each = event => { for (const issue of issues) add({repo,issue,pr,...event}); };
    if (typeof pull.body === 'string' && /^\s*Evidence:/m.test(pull.body)) each({kind:'evidence',at:pull.updated_at,head,evidence:pull.body});
    let comments=[];
    try { const rows=await github(repo,`issues/${pr}/comments`); if (Array.isArray(rows)) comments=rows; } catch { /* Missing observations are not success. */ }
    for (const comment of comments) {
      if (typeof comment?.body !== 'string') continue;
      const lines=comment.body.split(/\r?\n/).map(line=>line.trim());
      if (!lines.includes(`<!-- pdd:autopilot-core:merge:${head} -->`) || !lines.includes(`Autopilot merge check passed for head ${head}.`)) continue;
      each({kind:'evidence',at:comment.created_at,head,evidence:comment.body});
      if (parseAutopilotEvidence(comment.body).tests && lines.includes('- Full test suite: pass') && lines.includes('- Review: PASS from a fresh reviewer') && lines.some(line=>/^- CI: green \([1-9]\d* check\(s\)\)$/.test(line))) each({kind:'validated',at:comment.created_at,head,validation:{review:{head,verdict:'PASS',fresh:true},tests:{head,state:'pass'},ci:{head,state:'pass'}}});
    }
    if (!validHead(pull.merge_commit_sha)) continue;
    // A red merge commit is a regression only after our own merge is recorded.
    let checks;
    try { checks=await github(repo,`commits/${pull.merge_commit_sha}/check-runs`); } catch { continue; }
    for (const check of checks?.check_runs ?? []) if (check.head_sha === pull.merge_commit_sha && check.status === 'completed' && ['failure','timed_out','action_required'].includes(check.conclusion)) each({kind:'regression',at:check.completed_at,reason:'merge-ci-red'});
  }
  return calculateAutopilotMetrics({events,timezone,observedAt});
}

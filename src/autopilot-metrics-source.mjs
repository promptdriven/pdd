// Generated from prompts/cli/autopilot-metrics-source.prompt.md.
import * as nativeFs from 'node:fs';
import {homedir} from 'node:os';
import {join,dirname} from 'node:path';
import {createHash} from 'node:crypto';
import {execFile} from 'node:child_process';
import {promisify} from 'node:util';
import {nativeGithubCounter} from './github-calls.mjs';
import {calculateAutopilotMetrics,normalizeAutopilotMetric,autopilotEvidenceIdentity} from './autopilot-metrics.mjs';
import {isRecordedAutopilotAudit} from './autopilot-audit.mjs';

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
  const {stdout}=await run('gh',['api','--paginate','--slurp',`repos/${repo}/${path}${path.includes('?') ? '&' : '?'}per_page=100`],{maxBuffer:16*1024*1024,timeout:15000});
  const pages=JSON.parse(stdout);
  if (Array.isArray(pages[0])) return pages.flat();
  if (path.endsWith('/check-runs')) return {check_runs:pages.flatMap(page=>page.check_runs ?? [])};
  return pages[0];
}

export function recordAutopilotMetric({root,...input},ports={}) {
  const event=normalizeAutopilotMetric(input), fs=ports.fs ?? nativeFs;
  if (!event || typeof root !== 'string' || !root) throw Error('Invalid Autopilot metric');
  fs.mkdirSync(root,{recursive:true,mode:0o700});
  const file=join(root,'history.jsonl');
  let prefix='';
  try {
    const old=fs.readFileSync(file,'utf8'), identity=autopilotEvidenceIdentity(event);
    if (identity && old.split('\n').some(line=>autopilotEvidenceIdentity(json(line)?.metric) === identity)) return;
    if (old && !old.endsWith('\n')) prefix='\n';
  }
  catch(error) { if (error.code !== 'ENOENT') throw error; }
  fs.appendFileSync(file,prefix+JSON.stringify({metric:event})+'\n',{mode:0o600});
  fs.chmodSync(file,0o600);
}

// Read only the audit owner's shared authority, never its mutable public summary.
function badAudits(fs, root, repo) {
  const hash=createHash('sha256').update(repo).digest('hex').slice(0,20);
  if (!stat(fs,root)?.isDirectory() || !stat(fs,join(root,hash))?.isDirectory()) return [];
  const dir=join(root,hash,'records'), records=[];
  for (const name of names(fs,dir).filter(name=>/^[a-f0-9]{64}\.json$/.test(name))) {
    const audit=json(text(fs,join(dir,name)));
    if (!isRecordedAutopilotAudit(audit) || audit.repository !== repo || !validHead(audit.merge) || audit.result.verdict !== 'BAD') continue;
    const identity=createHash('sha256').update(JSON.stringify([audit.runId,audit.pr,audit.merge])).digest('hex');
    if (name === `${identity}.json`) records.push({pr:audit.pr,merge:audit.merge.toLowerCase(),at:audit.completedAt});
  }
  return records.sort((a,b)=>a.at-b.at);
}
const findingKey=event=>JSON.stringify([event.repo,event.issue,event.pr,event.mergeCommit,event.reason]);

export async function readAutopilotMetrics({timezone,observedAt},ports={}) {
  const fs=ports.fs ?? nativeFs, env=ports.env ?? process.env;
  const root=ports.stateRoot ?? join(env.HOME || (ports.homedir ?? homedir)(),'.local','state','pdd','autopilot');
  const now=(ports.now ?? Date.now)(), auditRoot=ports.auditRoot ?? join(dirname(root),'autopilot-audits');
  const github=ports.github ?? ((repo,path)=>nativeGithub(repo,path,ports.execFile ?? execute)), events=[], mappings=new Map();
  const add = input => { const event=normalizeAutopilotMetric(input); if (event) events.push(event); };
  const associate = (repo,issue,pr,core) => {
    if (!validPr(pr)) return;
    const key=`${repo}#${pr}`, mapping=mappings.get(key) ?? {repo,pr,issues:new Map()};
    mapping.issues.set(issue,core); mappings.set(key,mapping);
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
        events.push(event); associate(repo,event.issue,event.pr,core);
      } else if (['merged','ended','released','handed-over','abandoned','stopped'].includes(row?.outcome)) {
        add({repo,issue:row.issue,at:row.at,kind:'worked',...(validPr(row.pr) ? {pr:row.pr} : {})});
        if (Number.isSafeInteger(row.issue) && row.issue > 0) associate(repo,row.issue,row.pr,core);
      }
    }
    const dir=join(core,'jobs');
    for (const file of names(fs,dir).filter(name=>/^[1-9]\d*\.json$/.test(name))) {
      const job=json(text(fs,join(dir,file)));
      if (job?.schema !== 'pdd.core-job.v1' || job.issue !== Number(file.slice(0,-5))) continue;
      add({repo,issue:job.issue,kind:'started',at:job.started});
      for (const at of [job.prAt,job.agent?.started,job.review?.agent?.started,job.suite?.agent?.started]) add({repo,issue:job.issue,kind:'worked',at});
      associate(repo,job.issue,job.pr,core);
    }
  }
  const findings=new Set(events.filter(event=>event.kind === 'regression').map(findingKey)), bases=new Map(), audits=new Map();
  const discover=(owner, event)=>{
    const normalized=normalizeAutopilotMetric(event);
    if (!normalized || Date.parse(normalized.at) > now || findings.has(findingKey(normalized))) return;
    findings.add(findingKey(normalized)); events.push(normalized);
    try { recordAutopilotMetric({root:owner,...normalized},{fs}); }
    catch { ports.warn?.('Autopilot regression observation could not be saved'); }
  };
  const recordedAudits=repo=>{
    if (!audits.has(repo)) {
      try { audits.set(repo,badAudits(fs,auditRoot,repo)); } catch { audits.set(repo,[]); }
    }
    return audits.get(repo);
  };
  for (const merge of events.filter(event=>event.kind === 'merged' && validHead(event.mergeCommit) && validPr(event.pr))) {
    const owner=mappings.get(`${merge.repo}#${merge.pr}`)?.issues.get(merge.issue);
    for (const audit of recordedAudits(merge.repo)) if (audit.pr === merge.pr && audit.merge === merge.mergeCommit && audit.at > Date.parse(merge.at))
      discover(owner,{repo:merge.repo,issue:merge.issue,pr:merge.pr,kind:'regression',mergeCommit:merge.mergeCommit,reason:'bad-audit',at:audit.at});
  }
  for (const {repo,pr,issues} of mappings.values()) {
    let pull;
    try { pull=await github(repo,`pulls/${pr}`); } catch { continue; }
    if (!validHead(pull?.head?.sha)) continue;
    const each = event => { for (const issue of issues.keys()) add({repo,issue,pr,...event}); };
    if (!validHead(pull.merge_commit_sha)) continue;
    // Each independent CI read can fail without hiding the other source.
    const sha=pull.merge_commit_sha.toLowerCase();
    const owned=events.filter(event=>event.repo === repo && event.pr === pr && event.kind === 'merged' && Date.parse(event.at) <= now && (!event.mergeCommit || event.mergeCommit === sha));
    if (!owned.length) continue;
    for (const merge of owned) {
      for (const audit of recordedAudits(repo)) if (audit.pr === pr && audit.merge === sha && audit.at > Date.parse(merge.at))
        discover(issues.get(merge.issue),{repo,issue:merge.issue,pr,kind:'regression',mergeCommit:sha,reason:'bad-audit',at:audit.at});
    }
    if (typeof pull.base?.ref === 'string' && pull.base.ref) {
      const key=JSON.stringify([repo,pull.base.ref]), base=bases.get(key) ?? {repo,branch:pull.base.ref,merges:[]};
      for (const merge of owned) base.merges.push({event:merge,sha,root:issues.get(merge.issue)});
      bases.set(key,base);
    }
    let checks, statuses;
    try { checks=await github(repo,`commits/${sha}/check-runs`); } catch { /* Not recorded. */ }
    try { statuses=await github(repo,`commits/${sha}/statuses`); } catch { /* Not recorded. */ }
    for (const check of checks?.check_runs ?? []) if (check.head_sha?.toLowerCase() === sha && check.status === 'completed' && ['failure','timed_out','action_required','startup_failure','cancelled','stale'].includes(check.conclusion)) each({kind:'regression',at:check.completed_at,reason:'merge-ci-red'});
    for (const status of Array.isArray(statuses) ? statuses : []) if ((status.sha === undefined || validHead(status.sha) && status.sha.toLowerCase() === sha) && ['failure','error'].includes(status.state)) each({kind:'regression',at:status.created_at,reason:'merge-ci-red'});
  }
  for (const {repo,branch,merges} of bases.values()) {
    const since=new Date(Math.min(...merges.map(({event})=>Date.parse(event.at)))).toISOString();
    let commits;
    try { commits=await github(repo,`commits?sha=${encodeURIComponent(branch)}&since=${encodeURIComponent(since)}`); } catch { continue; }
    for (const commit of Array.isArray(commits) ? commits : []) {
      if (!validHead(commit?.sha) || typeof commit.commit?.message !== 'string') continue;
      const targets=[...commit.commit.message.matchAll(/^This reverts commit ([a-f0-9]{40})(?:\.|, reversing)\r?$/gmi)].map(match=>match[1].toLowerCase());
      for (const {event,sha,root:owner} of merges) if (targets.includes(sha) && commit.sha.toLowerCase() !== sha && now > Date.parse(event.at))
        discover(owner,{repo,issue:event.issue,pr:event.pr,kind:'regression',mergeCommit:sha,reason:'reverted',at:now});
    }
  }
  return calculateAutopilotMetrics({events,timezone,observedAt});
}

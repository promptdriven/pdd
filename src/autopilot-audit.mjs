// Generated from prompts/cli/autopilot-audit.prompt.md.
import * as nativeFs from 'node:fs';
import {join, dirname} from 'node:path';
import {createHash, randomUUID} from 'node:crypto';
import {fileURLToPath} from 'node:url';
import {runAgentProcess} from './agent-adapters.mjs';
import {loadAgentDefinitions} from './agent-config.mjs';
import {readCodexLimits} from './codex-limits.mjs';
import {runAutopilotAlerts} from './autopilot-alerts.mjs';
import {recordCostGithub, costReport} from './cost-ledger.mjs';
import {allRuns, stateDirFor, updateRunCosts} from './workflow-runs.mjs';
import {launchProfile} from './workflow-launch-profile.mjs';
import {expandHome} from './workflow-chat.mjs';
import {acquireRunLock} from './workflow-runner.mjs';

const sha = v => typeof v === 'string' && /^[0-9a-f]{40,64}$/i.test(v);
const named = v => typeof v === 'string' && v.trim().length > 0;
const read = (fs, path, fallback = null) => {
  try {return JSON.parse(fs.readFileSync(path, 'utf8'));}
  catch (e) {if(e.code === 'ENOENT') return fallback; throw e;}
};
const repositoryFolder=(run,ports)=>ports.auditStateRoot ?? join(stateDirFor(ports),'autopilot-audits',createHash('sha256').update(run.repo.toLowerCase()).digest('hex').slice(0,20));
const fileFor = (run, pr) => join(run.runDir, 'audits', `${pr}.json`);
const finished = a => a?.result && a.comment && (a.result.verdict !== 'BAD' || a.revert && a.alert)
  && (a.result.verdict !== 'CONCERN' || a.concern);
export function pendingAudits({run}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  if (!run?.automaticOrigin || !run.runDir) return [];
  return (run.pr ?? []).filter(pr => pr.state === 'merged').filter(pr => {
    const a = read(fs, fileFor(run, pr.number));
    return !a || a.runId === run.runId && a.result && !finished(a);
  }).map(pr => pr.number);
}
function save(fs, file, value) {
  const tmp = `${file}.${randomUUID()}.tmp`;
  try {fs.writeFileSync(tmp, JSON.stringify(value, null, 2)+'\n', {mode:0o600});fs.renameSync(tmp,file);}
  finally {try {fs.unlinkSync(tmp);} catch {}}
}
function parseAnswer(answer, kind, sessionId) {
  if(kind === 'claude') {
    const envelope = JSON.parse(answer.stdout);
    return {sessionId: envelope.session_id ?? sessionId, result: envelope.is_error ? null : JSON.parse(envelope.result)};
  }
  const rows = answer.stdout.trim().split('\n').map(line => JSON.parse(line));
  return {sessionId: rows.find(r => r.type === 'thread.started')?.thread_id,
    result: JSON.parse(rows.filter(r => r.type === 'item.completed' && r.item?.type === 'agent_message').at(-1)?.item.text ?? 'null')};
}
function validResult(r) {
  return r && ['OK','CONCERN','BAD'].includes(r.verdict) && named(r.summary) && named(r.evidence)
    && typeof r.revert === 'boolean' && typeof r.kind === 'string'
    && (r.verdict !== 'CONCERN' || /^[a-z][a-z0-9-]{0,79}$/.test(r.kind));
}
export async function auditMerge(input, ports = {}) {
  const fs=ports.fs ?? nativeFs, run=input?.run;
  if(!run?.commonDir || !run?.runDir) return {exitCode:1,message:'Post-merge audit: saved run is unavailable.'};
  const folder=repositoryFolder(run,ports);
  let release;
  try {
    fs.mkdirSync(folder,{recursive:true,mode:0o700});
    release=(ports.acquireAuditLock ?? acquireRunLock)(folder,'operation.lock');
  } catch {return {exitCode:1,message:'Post-merge audit: audit custody is busy or unavailable; retry later.'};}
  try {return await auditMergeOwned(input,ports);}
  catch {return {exitCode:1,message:'Post-merge audit: saved settings or evidence are unavailable; inspect before retry.'};}
  finally {release();}
}
async function auditMergeOwned({run, pr}, ports = {}) {
  const fs = ports.fs ?? nativeFs, now = ports.now ?? Date.now, env = {...(ports.env ?? process.env)};
  const fail = message => ({exitCode:1,message:`Post-merge audit: ${message}`});
  if(!run?.automaticOrigin || !/^[\w.-]+\/[\w.-]+$/.test(run.repo ?? '') || !/^[1-9]\d*$/.test(String(pr))
    || !(run.pr ?? []).some(p => p.number === Number(pr)) || !named(run.baseBranch)
    || run.baseBranch.startsWith('-') || run.baseBranch.startsWith('refs/')) return fail('saved automatic run or PR is unavailable.');
  const cwd = run.sourceRoot ?? run.root, file = fileFor(run,pr), profile=launchProfile(run);
  profile.configDir=expandHome(profile.configDir,env);
  const config = await (ports.readConfig ?? (root => read(fs,join(root,'pdd.json'),{})))(cwd);
  if(config.autopilot?.audit === false) return {exitCode:0,message:'Post-merge audit disabled for this repository.'};
  if(config.autopilot?.mode !== 'auto') return fail('repository is not in auto mode.');
  const execute = ports.execFile ?? runAgentProcess;
  const command = async (program,args,options={}) => {
    if(program === 'gh') recordCostGithub(run.runDir,{at:now()},{fs});
    const result = await execute(program,args,{cwd,env,timeoutMs:120000,maxBytes:8*1024*1024,...options});
    if(result.code !== undefined && result.code !== 0) throw Error('External operation did not confirm success.');
    return result.stdout;
  };
  let audit = read(fs,file);
  if(audit && audit.runId !== run.runId) return fail('audit belongs to another run attempt.');
  if(audit && !audit.result) return fail('auditor outcome is unknown; inspect saved evidence before any retry.');
  const persist = () => save(fs,file,audit);
  // Each effect owns an exclusive reservation. An uncertain external reply is never retried.
  const effect = async (key, action) => {
    audit=read(fs,file);
    if(audit[key]) return;
    try {fs.writeFileSync(`${file}.${key}`, '', {flag:'wx',mode:0o600});}
    catch(e) {if(e.code === 'EEXIST') {audit=read(fs,file);if(!audit[key]) {audit[key]={state:'unknown',at:now()};persist();}return;}throw e;}
    audit[key] = {state:'sending',at:now()};persist();
    try {const value=await action();audit=read(fs,file);audit[key] = {state:'sent',at:now(),value};}
    catch {audit=read(fs,file);audit[key] = {state:'unknown',at:now()};}
    persist();
  };
  try {
    if(!audit) {
      const pull = JSON.parse(await command('gh',['api',`repos/${run.repo}/pulls/${pr}`]));
      if(pull.number !== Number(pr) || pull.merged !== true || pull.base?.ref !== run.baseBranch
        || pull.base?.repo?.full_name?.toLowerCase() !== run.repo.toLowerCase() || !sha(pull.merge_commit_sha)) return fail('the merged PR and saved base could not be verified.');
      const merge = pull.merge_commit_sha;
      const saved=run.pr.find(p=>p.number===Number(pr));
      const savedMerge=saved.mergeCommit?.oid ?? saved.mergeCommit ?? saved.mergeSha;
      if(savedMerge && savedMerge!==merge) return fail('saved merge identity differs from GitHub.');
      const commit = JSON.parse(await command('gh',['api',`repos/${run.repo}/commits/${merge}`]));
      const parent = commit.parents?.[0]?.sha;
      if(commit.sha !== merge || !sha(parent)) return fail('first parent is unavailable.');
      const definitions = await (ports.agentDefinitions ?? loadAgentDefinitions)({cwd,env});
      const definition = definitions.find(d => d.kind === run.agent && (!run.agentDefinition?.name || d.name === run.agentDefinition.name));
      if(!definition || !['codex','claude'].includes(definition.kind)) return fail('configured auditor agent is unavailable; audit remains pending.');
      Object.assign(env,definition.env);
      if(profile.configDir) env[definition.kind === 'codex' ? 'CODEX_HOME' : 'CLAUDE_CONFIG_DIR'] = profile.configDir;
      if(definition.kind === 'codex' && (await (ports.codexLimits ?? readCodexLimits)({command:definition.command,cwd,env})).state !== 'healthy') return fail('account limits hold the audit; no paid call was made.');
      if(config.autopilot.auditTokenLimit !== undefined) {
        const limit = config.autopilot.auditTokenLimit;
        if(!Number.isFinite(limit) || limit < 0) return fail('invalid auditTokenLimit.');
        const usage = await (ports.dailyUsage ?? (async () => {
          const unknown={known:false,total:0};
          let index;
          try {index=read(fs,join(stateDirFor(ports),'runs.json'));} catch {return unknown;}
          if(!Array.isArray(index?.runs) || index.runs.length>=200
            || !index.runs.some(row=>row?.runDir===run.runDir)) return unknown;
          for(const row of index.runs.filter(r=>r?.repo?.toLowerCase()===run.repo.toLowerCase())) {
            if(!named(row.runDir)) return unknown;
            let record;try {record=read(fs,join(row.runDir,'status.json'));} catch {return unknown;}
            if(!record || record.repo?.toLowerCase()!==run.repo.toLowerCase()) return unknown;
          }
          const runs = (await allRuns({cancelled:true},ports)).filter(r=>r.repo?.toLowerCase()===run.repo.toLowerCase());
          let refreshFailed=false;
          const measured = runs.map(r => {try {return (ports.refreshCosts ?? updateRunCosts)(r.runDir,latest => {
            if(latest.runId!==r.runId || latest.startedAt!==r.startedAt) throw Error('Cost attempt changed');
            return latest;
          },{...ports,env});} catch {refreshFailed=true;return r;}});
          const report = costReport(measured,now());
          return {total:report.day.totals.totalTokens ?? 0,known:!refreshFailed && !report.day.coverage.some(c => ['session-unavailable','audit-session-unavailable','usage-unavailable','session-capture-deferred','session-backlog','session-truncated','usage-identity-missing','capture-failed','not-captured'].includes(c))};
        }))();
        if(!usage.known || usage.total >= limit) return fail('daily cost limit holds the audit; no paid call was made.');
      }
      fs.mkdirSync(dirname(file),{recursive:true,mode:0o700});
      audit = {schema:'pdd.audit.v1',runId:run.runId,pr:Number(pr),merge,parent,at:now(),state:'starting',chat:{agent:definition.kind,configDir:profile.configDir ?? env[definition.kind==='codex'?'CODEX_HOME':'CLAUDE_CONFIG_DIR'] ?? null,startedAt:now()}};
      try {fs.writeFileSync(file,JSON.stringify(audit),{flag:'wx',mode:0o600});}
      catch(e) {if(e.code==='EEXIST') return fail('audit already reserved.');throw e;}
      const scratch = join(run.runDir,'audits',`scratch-${pr}`), checkout = join(scratch,'repo');
      fs.mkdirSync(scratch,{recursive:true,mode:0o700});
      await command('git',['clone','--no-checkout','--',`https://github.com/${run.repo}.git`,checkout]);
      await command('git',['checkout','--detach',merge],{cwd:checkout});
      audit.chat.root=checkout;persist();
      const brief = fs.readFileSync(fileURLToPath(new URL('../docs/autopilot-audit.md',import.meta.url)),'utf8');
      const input = brief+'\n\nTask input:\n'+JSON.stringify({repository:run.repo,issue:run.number,prs:run.pr,merge,parent,runDir:run.runDir,scratch,checkout});
      let args;
      if(definition.kind === 'codex') args=['exec','--json','--dangerously-bypass-approvals-and-sandbox','-c','features.multi_agent=false',...(profile.model?['--model',profile.model]:[]),'-'];
      else {const id=randomUUID();audit.chat.session={id};persist();args=['-p','--session-id',id,'--output-format','json','--permission-mode','bypassPermissions',...(profile.model?['--model',profile.model]:[])];}
      // No resume flag and no prior chat context. This invocation owns a new native session.
      const childEnv=Object.fromEntries(Object.entries(env).filter(([key])=>!/^(?:CLAUDECODE$|CLAUDE_CODE_|CLAUDE_PID$|CODEX_THREAD_ID$|CODEX_SANDBOX|HERDR_|PDD_AGENT_SESSION$|PDD_AUTOPILOT_CONTEXT$)/.test(key)));
      const answer = await (ports.runAuditor ?? execute)(definition.command,args,{cwd:checkout,env:childEnv,input,timeoutMs:30*60*1000,maxBytes:8*1024*1024});
      let parsed;
      try {parsed=parseAnswer(answer,definition.kind,audit.chat.session?.id);}
      catch { // Still retain Codex's session identity if its final answer was invalid.
        for(const line of String(answer.stdout??'').split('\n')) {try {const r=JSON.parse(line);if(r.type==='thread.started') audit.chat.session={id:r.thread_id};}catch {}}
        audit.state='unknown';persist();return fail('auditor returned no valid verdict.');
      }
      audit.chat.session = {id:parsed.sessionId};
      const previous = [...(run.chats??[]),...(run.abandonedChats??[]),run.chatReplacement?.original,run.chatReplacement?.replacement].filter(Boolean).map(c=>c.session?.id);
      for(const name of fs.readdirSync(dirname(file)).filter(n=>n.endsWith('.json') && n!==`${pr}.json`)) previous.push(read(fs,join(dirname(file),name))?.chat?.session?.id);
      if(answer.code !== 0 || !/^[0-9a-f]{8}-(?:[0-9a-f]{4}-){3}[0-9a-f]{12}$/i.test(parsed.sessionId??'') || previous.includes(parsed.sessionId) || !validResult(parsed.result)) {
        audit.state='unknown';persist();return fail('auditor session or verdict is invalid.');
      }
      audit.result=parsed.result;audit.state='recorded';audit.completedAt=now();persist();
    }
    await effect('comment',()=>command('gh',['api','--method','POST',`repos/${run.repo}/issues/${run.number}/comments`,'-f',`body=Audit: ${audit.result.verdict}\n\nPR #${pr}, merge ${audit.merge}\n\n${audit.result.summary}\n\n${audit.result.evidence}\n\n<!-- pdd:audit:${run.runId}:${pr} -->`]));
    if(audit.result.verdict === 'BAD') {
      await effect('revert',async()=>{
        const checkout=join(run.runDir,'audits',`revert-${pr}`), branch=`pdd/revert-${pr}-${randomUUID()}`;
        await command('git',['clone','--single-branch','--branch',run.baseBranch,'--',`https://github.com/${run.repo}.git`,checkout]);
        await command('git',['switch','-c',branch],{cwd:checkout});
        const parents=(await command('git',['rev-list','--parents','-n','1',audit.merge],{cwd:checkout})).trim().split(/\s+/);
        await command('git',['-c','core.hooksPath=/dev/null','-c','commit.gpgsign=false','-c','user.name=PDD Autopilot','-c','user.email=pdd@noreply.invalid','revert','--no-edit',...(parents.length>2?['-m','1']:[]),audit.merge],{cwd:checkout});
        await command('git',['push','origin',`HEAD:refs/heads/${branch}`],{cwd:checkout});
        return (await command('gh',['pr','create','--repo',run.repo,'--base',run.baseBranch,'--head',branch,'--title',`Revert #${pr}: post-merge audit BAD`,'--body',`${audit.result.summary}\n\nReverts ${audit.merge}. Audit for issue #${run.number}.\n\n<!-- pdd:audit-revert:${run.runId}:${pr} -->`],{cwd:checkout})).trim();
      });
      await effect('alert',async()=>{
        const input={action:'alert',cwd,env,issue:String(run.number),kind:'decision',text:JSON.stringify({cause:`Post-merge audit BAD for PR #${pr} (${audit.merge})`,tried:`Saved audit. Revert PR: ${audit.revert?.value ?? audit.revert?.state ?? 'unknown'}.`,need:'Review the revert PR or resolve the saved revert failure.'})};
        const result=await (ports.sendAlert ?? (i=>runAutopilotAlerts(i,{...ports.alertPorts,repository:async()=>({nameWithOwner:run.repo})})))(input);
        if(result?.exitCode !== 0) throw Error('Alert unconfirmed');
        return 'recorded';
      });
    }
    if(audit.result.verdict === 'CONCERN' && !audit.concern) {
      const folder=join(repositoryFolder(run,ports),'concerns');fs.mkdirSync(folder,{recursive:true,mode:0o700});
      const kind=audit.result.kind, groupFile=join(folder,`${kind}.json`);
      { // Repository audit custody also serializes concern bookkeeping.
        const group=read(fs,groupFile,{repository:run.repo,kind,records:[]});
        if(group.repository.toLowerCase()!==run.repo.toLowerCase()) throw Error('Concern repository mismatch');
        const identity=`${run.runId}:${pr}`;
        if(!group.records.some(r=>r.identity===identity)) group.records.push({identity,pr:Number(pr),issue:run.number,summary:audit.result.summary});
        if(group.issue?.state==='sending') group.issue.state='unknown';
        save(fs,groupFile,group);
        if(new Set(group.records.map(r=>r.pr)).size>=2 && !group.issue) {
          group.issue={state:'sending',at:now()};save(fs,groupFile,group);
          try {
            const value=await command('gh',['api','--method','POST',`repos/${run.repo}/issues`,'-f',`title=Autopilot audit process concern: ${kind}`,'-f',`body=${group.records.map(r=>`PR #${r.pr}, issue #${r.issue}: ${r.summary}`).join('\n')}\n\n<!-- pdd:audit-concern:${run.repo.toLowerCase()}:${kind} -->`]);
            const url=JSON.parse(value).html_url;if(!named(url)) throw Error('Issue unconfirmed');group.issue={state:'sent',url};
          } catch {group.issue={state:'unknown'};}
          save(fs,groupFile,group);
        }
        audit=read(fs,file);audit.concern={state:group.issue?.state==='unknown'?'unknown':'sent',kind};persist();
      }
    }
    const uncertain = ['comment','revert','alert','concern'].some(k=>audit[k] && audit[k].state!=='sent');
    return {exitCode:uncertain?1:0,message:`Audit: ${audit.result.verdict}; PR #${pr}; saved ${file}${uncertain?'; follow-up outcome unknown, inspect before retry':''}.`};
  } catch {if(audit && !audit.result) {audit.state='unknown';persist();}return fail('operation failed; retained evidence needs inspection.');}
}

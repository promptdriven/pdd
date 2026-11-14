// Generated from prompts/cli/autopilot-audit.prompt.md (sha256: 0a984bc134c03efc496357862e6fba57a886e808e604e2164a62b577d9c0f842).
import * as nativeFs from 'node:fs';
import {join, dirname} from 'node:path';
import {createHash, randomUUID} from 'node:crypto';
import {fileURLToPath} from 'node:url';
import {runAgentProcess} from './agent-adapters.mjs';
import {loadAgentDefinitions} from './agent-config.mjs';
import {readCodexLimits} from './codex-limits.mjs';
import {runAutopilotAlerts} from './autopilot-alerts.mjs';
import {recordCostGithub, costReport, isUuid, shortHash} from './cost-ledger.mjs';
import {allRuns, readRun, stateDirFor, updateRunCosts} from './workflow-runs.mjs';
import {launchProfile} from './workflow-launch-profile.mjs';
import {expandHome} from './workflow-chat.mjs';
import {acquireRunLock} from './workflow-runner.mjs';

const sha = v => typeof v === 'string' && /^[0-9a-f]{40,64}$/i.test(v);
const named = v => typeof v === 'string' && v.trim().length > 0;
const read = (fs, path, fallback = null) => {
  try {return JSON.parse(fs.readFileSync(path, 'utf8'));}
  catch (e) {if(e.code === 'ENOENT') return fallback; throw e;}
};
const repositoryFolder=(run,ports)=>ports.auditStateRoot ?? join(stateDirFor(ports),'autopilot-audits',shortHash(run.repo.toLowerCase()));
const fileFor = (run, pr) => join(run.runDir, 'audits', `${pr}.json`);
const auditIdentity = audit => createHash('sha256').update(JSON.stringify([audit.runId,audit.pr,audit.merge])).digest('hex');
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const time = value => Number.isFinite(value) && value >= 0;
const invalidEvidence = () => Object.assign(Error('audit-evidence-invalid'), {code:'audit-evidence-invalid'});
const savedMergeOf = pr => pr?.mergeCommit?.oid ?? pr?.mergeCommit ?? pr?.mergeSha;
const evidenceCause = error => error instanceof SyntaxError || error.code === 'audit-evidence-invalid' ? 'audit-evidence-invalid' : 'audit-evidence-unreadable';
const repoMismatch = (local, shared, repo) => shared.some(a => a.repository !== repo.toLowerCase())
  || local.some(a => a.repository !== undefined && a.repository.toLowerCase() !== repo.toLowerCase());
const sendAuditAlert = (run, ports, input) => (ports.sendAlert ?? (i => runAutopilotAlerts(i, {...ports, ...ports.alertPorts, repository: async () => ({nameWithOwner: run.repo})})))(input);
function validAudit(audit) {
  if (!object(audit) || audit.schema !== 'pdd.audit.v1' || !named(audit.runId)
    || !Number.isSafeInteger(audit.pr) || audit.pr <= 0 || !sha(audit.merge) || !sha(audit.parent)
    || !time(audit.at) || !['starting','recorded','unknown'].includes(audit.state)
    || !object(audit.chat) || !['codex','claude'].includes(audit.chat.agent)
    || !(audit.chat.configDir === null || named(audit.chat.configDir)) || !time(audit.chat.startedAt)
    || Object.hasOwn(audit.chat,'root') && !named(audit.chat.root)
    || Object.hasOwn(audit.chat,'session') && (!object(audit.chat.session) || !named(audit.chat.session.id))
    || Object.hasOwn(audit,'repository') && !/^[\w.-]+\/[\w.-]+$/.test(audit.repository)) return false;
  if (audit.state === 'recorded') {
    if (!validResult(audit.result) || !time(audit.completedAt) || !isUuid(audit.chat.session?.id)) return false;
  } else if (['result','completedAt','comment','reopen','revert','alert','concern'].some(key => Object.hasOwn(audit,key))) return false;
  for (const key of ['comment','reopen','revert','alert']) if (Object.hasOwn(audit,key)) {
    const effect = audit[key];
    if (!object(effect) || !['sending','sent','unknown'].includes(effect.state) || !time(effect.at)
      || effect.state === 'sent' && typeof effect.value !== 'string'
      || Object.hasOwn(effect,'value') && typeof effect.value !== 'string'
      || key !== 'comment' && audit.result?.verdict !== 'BAD'
      || key === 'reopen' && audit.result?.revert !== false) return false;
  }
  if (Object.hasOwn(audit,'concern') && (!object(audit.concern)
    || !['sent','unknown'].includes(audit.concern.state) || audit.result?.verdict !== 'CONCERN'
    || audit.concern.kind !== audit.result.kind)) return false;
  return true;
}
// This predicate permits a diagnostic alert only. It never admits damaged authority.
function unavailableRecommendation(audit) {
  return object(audit?.result) && audit.result.verdict==='BAD' && typeof audit.result.revert!=='boolean'
    && validAudit({...audit,result:{...audit.result,revert:false}});
}
function auditRecords(fs, folder, local = false) {
  let names;
  try {names=fs.readdirSync(folder);} catch(e) {if(e.code==='ENOENT') return [];throw e;}
  const records=[],recommendationHolds=[];let failure;
  for(const name of names.filter(n=>local ? /^\d+\.json$/.test(n) : n.endsWith('.json'))) {
    try {
      const audit=read(fs,join(folder,name));
      const identityValid=object(audit) && (local ? audit.pr===Number(name.slice(0,-5))
        : named(audit.repository) && name===`${auditIdentity(audit)}.json`);
      if(!validAudit(audit) || !identityValid) {
        if(identityValid && unavailableRecommendation(audit)) recommendationHolds.push(audit);
        throw invalidEvidence();
      }
      records.push(audit);
    } catch(error) {failure??=error;}
  }
  if(failure) throw Object.assign(failure,{recommendationHolds});
  return records;
}
function auditInventory(fs,run,ports) {
  const inventory={},recommendationHolds=[];let failure;
  for(const [key,folder,local] of [['local',join(run.runDir,'audits'),true],['shared',join(repositoryFolder(run,ports),'records'),false]]) {
    try {inventory[key]=auditRecords(fs,folder,local);}
    catch(error) {failure??=error;recommendationHolds.push(...error.recommendationHolds??[]);}
  }
  if(failure) throw Object.assign(failure,{recommendationHolds});
  return inventory;
}
const finished = a => a?.result && a.comment && (a.result.verdict !== 'BAD' || (a.result.revert ? a.revert : a.reopen) && a.alert)
  && (a.result.verdict !== 'CONCERN' || a.concern);
export function pendingAudits({run}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  if (!run?.automaticOrigin || !run.runDir) return [];
  const merged = (run.pr ?? []).filter(pr => pr.state === 'merged');
  const hold = (pr, cause) => ports.onAuditHold?.({pr: pr.number, cause});
  let local, shared;
  try { fs.readdirSync(join(run.runDir, 'audits')); }
  catch (error) {
    if (error.code !== 'ENOENT') {
      for (const pr of merged) hold(pr, 'audit-folder-unreadable');
      return [];
    }
  }
  try {
    ({local,shared}=auditInventory(fs,run,ports));
    if(repoMismatch(local,shared,run.repo)) throw invalidEvidence();
  } catch (error) {
    const cause=evidenceCause(error);
    for(const pr of merged) hold(pr,cause);
    return [];
  }
  return merged.filter(pr => {
    const copy=local.find(a=>a.pr===pr.number);
    if(copy && copy.runId!==run.runId) {hold(pr,'audit-attempt-mismatch');return false;}
    const authority=shared.filter(a=>a.runId===run.runId && a.pr===pr.number);
    const savedMerge=savedMergeOf(pr);
    const a=authority[0] ?? copy;
    if(authority.length>1 || savedMerge && a && a.merge!==savedMerge
      || copy && a && copy.merge!==a.merge) {hold(pr,'audit-evidence-invalid');return false;}
    return !a || a.state==='recorded' && !finished(a);
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
// The alert command reports recording success separately from delivery in its message.
function alertDeliveryState(result) {
  if(result?.exitCode!==0 || typeof result.message!=='string') return 'unknown';
  if(/^(Alert|Update) sent for .*; (the webhook|the Discord bot readback) confirmed it\.$/.test(result.message)) return 'sent';
  if(/^(Alert|Update) recorded for .*; delivery failed \(/.test(result.message)
    || /^(Alert|Update) recorded on this machine for .*; no alert destination is set /.test(result.message)) return 'failed';
  return 'unknown';
}
// Separate custody lets us ask for a decision without importing or repairing authority.
async function alertUnavailableRecommendation(run, pr, audit, ports) {
  const saved=run.pr.find(p=>p.number===Number(pr));
  const savedMerge=savedMergeOf(saved);
  if(!audit || audit.runId!==run.runId || audit.pr!==Number(pr) || saved?.state!=='merged'
    || savedMerge && savedMerge!==audit.merge
    || audit.repository!==undefined && audit.repository.toLowerCase()!==run.repo.toLowerCase()) return;
  const fs=ports.fs ?? nativeFs, now=ports.now ?? Date.now;
  const folder=join(repositoryFolder(run,ports),'decisions'),file=join(folder,`${auditIdentity(audit)}.json`);
  fs.mkdirSync(folder,{recursive:true,mode:0o700});
  const previous=read(fs,file);
  if(previous) {
    if(previous.schema!=='pdd.audit-decision.v1' || previous.repository!==run.repo.toLowerCase()
      || previous.runId!==run.runId || previous.pr!==Number(pr) || previous.merge!==audit.merge
      || !time(previous.at) || !['sending','sent','failed','unknown'].includes(previous.state)) throw invalidEvidence();
    if(previous.state!=='failed') return;
  }
  const reservation={schema:'pdd.audit-decision.v1',repository:run.repo.toLowerCase(),runId:run.runId,
    pr:Number(pr),merge:audit.merge,state:'sending',at:now()};
  if(previous) save(fs,file,reservation);
  else fs.writeFileSync(file,JSON.stringify(reservation),{flag:'wx',mode:0o600});
  try {
    const input={action:'alert',update:true,cwd:run.sourceRoot ?? run.root,env:ports.env ?? process.env,
      issue:String(run.number),kind:'decision',text:JSON.stringify({
        cause:`Post-merge audit BAD for PR #${pr} (${audit.merge}). Revert recommendation is missing or unavailable.`,
        tried:'Held the audit without a revert or another auditor. Saved evidence and effect reservations are unchanged.',
        need:`Inspect the saved audit evidence and decide: keep the merge and finish the rest on issue #${run.number}, or revert on a review branch with git revert -m 1 ${audit.merge}, then open a PR against ${run.baseBranch}.`,
      })};
    reservation.state=alertDeliveryState(await sendAuditAlert(run,ports,input));
  } catch {reservation.state='unknown';}
  reservation.at=now();save(fs,file,reservation);
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
  const cwd = run.sourceRoot ?? run.root, localFile = fileFor(run,pr), profile=launchProfile(run);
  const recordsFolder=join(repositoryFolder(run,ports),'records');
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
  // Validate all earlier evidence before a launch, including the session-reuse inventory.
  let localRecords, sharedRecords;
  try {
    ({local:localRecords,shared:sharedRecords}=auditInventory(fs,run,ports));
  } catch(error) {
    const candidates=(error.recommendationHolds??[]).filter(a=>a.runId===run.runId && a.pr===Number(pr));
    try {if(new Set(candidates.map(a=>a.merge)).size===1)
      await alertUnavailableRecommendation(run,pr,candidates[0],ports);}
    catch { /* An unavailable alert journal cannot release the evidence hold. */ }
    return fail(`${evidenceCause(error)}; saved authority needs inspection.`);
  }
  if(ports.auditHoldOnly) return fail('saved evidence needs an ordinary audit scan before follow-up.');
  if(repoMismatch(localRecords,sharedRecords,run.repo))
    return fail('audit-evidence-invalid; saved audit repository differs.');
  if(sharedRecords.filter(a=>a.runId===run.runId && a.pr===Number(pr)).length>1)
    return fail('audit-evidence-invalid; conflicting saved merge identities.');
  let audit=read(fs,localFile);
  if(audit && audit.runId !== run.runId) return fail('audit-attempt-mismatch; audit belongs to another run attempt.');
  const saved=run.pr.find(p=>p.number===Number(pr));
  const savedMerge=savedMergeOf(saved);
  let merge=audit?.merge;
  if(!audit) {
    const pull = JSON.parse(await command('gh',['api',`repos/${run.repo}/pulls/${pr}`]));
    if(pull.number !== Number(pr) || pull.merged !== true || pull.base?.ref !== run.baseBranch
      || pull.base?.repo?.full_name?.toLowerCase() !== run.repo.toLowerCase() || !sha(pull.merge_commit_sha)) return fail('the merged PR and saved base could not be verified.');
    merge=pull.merge_commit_sha;
  }
  if(savedMerge && savedMerge!==merge) return fail('audit-evidence-invalid; saved merge identity differs from GitHub.');
  const file=join(recordsFolder,`${auditIdentity({runId:run.runId,pr:Number(pr),merge})}.json`);
  const shared=read(fs,file);
  if(shared) audit=shared;
  const persist = () => {
    // Shared authority is committed first. Local copies cannot authorize effects.
    save(fs,file,audit);
    fs.mkdirSync(dirname(localFile),{recursive:true,mode:0o700});save(fs,localFile,audit);
  };
  if(audit) {
    if(!validAudit(audit) || audit.runId!==run.runId || audit.pr!==Number(pr) || audit.merge!==merge) return fail('audit-evidence-invalid; audit identity differs.');
    fs.mkdirSync(recordsFolder,{recursive:true,mode:0o700});
    audit.repository=run.repo.toLowerCase();
    if(!shared) for(const key of ['comment','reopen','revert','alert']) {
      try {fs.statSync(`${localFile}.${key}`);if(!audit[key])audit[key]={state:'unknown',at:now()};}
      catch(e) {if(e.code!=='ENOENT')throw e;}
    }
    persist();
    if(!audit.result) return fail('auditor outcome is unknown; inspect saved evidence before any retry.');
  }
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
          if(index.runs.some(row=>!named(row?.repo) || !named(row?.runDir) || !Number.isSafeInteger(row?.number))) return unknown;
          for(const row of index.runs.filter(r=>r?.repo?.toLowerCase()===run.repo.toLowerCase())) {
            if(!named(row.runDir)) return unknown;
            const record=readRun(row.runDir);
            if(!record || record.repo?.toLowerCase()!==run.repo.toLowerCase() || record.number!==row.number
              || record.runDir!==row.runDir || !named(record.runId) || !Number.isFinite(record.startedAt)) return unknown;
          }
          const runs = (await allRuns({cancelled:true},ports)).filter(r=>r.repo?.toLowerCase()===run.repo.toLowerCase());
          for(const row of index.runs.filter(r=>r?.repo?.toLowerCase()===run.repo.toLowerCase())) {
            const record=readRun(row.runDir);
            if(!runs.some(r=>r.runDir===row.runDir && r.number===row.number && r.runId===record?.runId && r.startedAt===record?.startedAt)) return unknown;
          }
          if(sharedRecords.some(a=>!runs.some(r=>r.runId===a.runId))) return unknown;
          let refreshFailed=false;
          const measured = runs.map(r => {try {return (ports.refreshCosts ?? updateRunCosts)(r.runDir,latest => {
            if(latest.runId!==r.runId || latest.startedAt!==r.startedAt) throw Error('Cost attempt changed');
            return latest;
          },{...ports,env,auditRecords:sharedRecords.filter(a=>a.runId===r.runId)});} catch {refreshFailed=true;return r;}});
          const report = costReport(measured,now());
          return {total:report.day.totals.totalTokens ?? 0,known:!refreshFailed && !report.day.coverage.some(c => ['session-unavailable','audit-session-unavailable','usage-unavailable','session-capture-deferred','session-backlog','session-truncated','usage-identity-missing','capture-failed','not-captured'].includes(c))};
        }))();
        if(!usage.known || usage.total >= limit) return fail('daily cost limit holds the audit; no paid call was made.');
      }
      fs.mkdirSync(recordsFolder,{recursive:true,mode:0o700});
      fs.mkdirSync(dirname(localFile),{recursive:true,mode:0o700});
      audit = {schema:'pdd.audit.v1',repository:run.repo.toLowerCase(),runId:run.runId,pr:Number(pr),merge,parent,at:now(),state:'starting',chat:{agent:definition.kind,configDir:profile.configDir ?? env[definition.kind==='codex'?'CODEX_HOME':'CLAUDE_CONFIG_DIR'] ?? null,startedAt:now()}};
      try {fs.writeFileSync(file,JSON.stringify(audit),{flag:'wx',mode:0o600});}
      catch(e) {if(e.code==='EEXIST') return fail('audit already reserved.');throw e;}
      persist();
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
      if(named(parsed.sessionId)) audit.chat.session = {id:parsed.sessionId};
      else delete audit.chat.session;
      const previous = [...(run.chats??[]),...(run.abandonedChats??[]),run.chatReplacement?.original,run.chatReplacement?.replacement].filter(Boolean).map(c=>c.session?.id);
      for(const earlier of [...localRecords,...sharedRecords]) previous.push(earlier.chat?.session?.id);
      if(answer.code !== 0 || !isUuid(parsed.sessionId) || previous.includes(parsed.sessionId) || !validResult(parsed.result)) {
        audit.state='unknown';persist();return fail('auditor session or verdict is invalid.');
      }
      audit.result=parsed.result;audit.state='recorded';audit.completedAt=now();persist();
    }
    const keepMerge=audit.result.verdict==='BAD' && !audit.result.revert;
    if(keepMerge) await effect('reopen',()=>command('gh',['api','--method','PATCH',`repos/${run.repo}/issues/${run.number}`,'-f','state=open']));
    await effect('comment',()=>command('gh',['api','--method','POST',`repos/${run.repo}/issues/${run.number}/comments`,'-f',`body=Audit: ${audit.result.verdict}\n\nPR #${pr}, merge ${audit.merge}\n\nRevert recommendation: ${audit.result.revert}\n\n${keepMerge?'Keep the merge and finish the rest. Missing parts and audit evidence:\n\n':''}${audit.result.summary}\n\n${audit.result.evidence}\n\n<!-- pdd:audit:${run.runId}:${pr} -->`]));
    if(audit.result.verdict === 'BAD') {
      if(audit.result.revert) await effect('revert',async()=>{
        const checkout=join(run.runDir,'audits',`revert-${pr}`), branch=`pdd/revert-${pr}-${randomUUID()}`;
        await command('git',['clone','--single-branch','--branch',run.baseBranch,'--',`https://github.com/${run.repo}.git`,checkout]);
        await command('git',['switch','-c',branch],{cwd:checkout});
        const parents=(await command('git',['rev-list','--parents','-n','1',audit.merge],{cwd:checkout})).trim().split(/\s+/);
        await command('git',['-c','core.hooksPath=/dev/null','-c','commit.gpgsign=false','-c','user.name=PDD Autopilot','-c','user.email=pdd@noreply.invalid','revert','--no-edit',...(parents.length>2?['-m','1']:[]),audit.merge],{cwd:checkout});
        await command('git',['push','origin',`HEAD:refs/heads/${branch}`],{cwd:checkout});
        return (await command('gh',['pr','create','--repo',run.repo,'--base',run.baseBranch,'--head',branch,'--title',`Revert #${pr}: post-merge audit BAD`,'--body',`${audit.result.summary}\n\nReverts ${audit.merge}. Audit for issue #${run.number}.\n\n<!-- pdd:audit-revert:${run.runId}:${pr} -->`],{cwd:checkout})).trim();
      });
      await effect('alert',async()=>{
        const input={action:'alert',update:true,cwd,env,issue:String(run.number),kind:'decision',text:JSON.stringify({
          cause:`Post-merge audit BAD for PR #${pr} (${audit.merge}). Auditor revert recommendation: ${audit.result.revert}.`,
          tried:keepMerge
            ? `Saved audit and missing parts on issue #${run.number}. Issue reopen: ${audit.reopen?.state ?? 'unknown'}. Audit comment: ${audit.comment?.state ?? 'unknown'}.`
            : `Saved audit. Revert PR: ${audit.revert?.value ?? audit.revert?.state ?? 'unknown'}.`,
          need:keepMerge
            ? `Default: keep the merge and finish the rest on issue #${run.number}. Other option: revert on a review branch with git revert -m 1 ${audit.merge}, then open a PR against ${run.baseBranch}.`
            : 'Review the revert PR or resolve the saved revert failure.',
        })};
        if(alertDeliveryState(await sendAuditAlert(run,ports,input))!=='sent') throw Error('Alert unconfirmed');
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
    const uncertain = ['comment','reopen','revert','alert','concern'].some(k=>audit[k] && audit[k].state!=='sent');
    return {exitCode:uncertain?1:0,message:`Audit: ${audit.result.verdict}; PR #${pr}; saved ${file}${uncertain?'; follow-up outcome unknown, inspect before retry':''}.`};
  } catch {if(audit && !audit.result) {audit.state='unknown';persist();}return fail('operation failed; retained evidence needs inspection.');}
}

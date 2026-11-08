// Generated from prompts/cli/autopilot-merge.prompt.md.
import {execFile as callback} from 'node:child_process';
import {promisify} from 'node:util';
import {resolveWorkflowRepository} from './workflow-github.mjs';
import {nativeGithubCounter} from './github-calls.mjs';

const object = v => v !== null && typeof v === 'object' && !Array.isArray(v);
const named = v => typeof v === 'string' && v.trim().length > 0;
const count = v => Number.isSafeInteger(v) && v >= 0;
export const DEFAULT_MERGE_RULES = Object.freeze({fresh_review:true, full_suite:true,
  required_ci:true, max_repairs:2, autonomy:'merge', areas:Object.freeze({}), post_merge_audit:true});
const levels = ['manual','observe','merge'];
const refusal = (rule, detail) => ({allowed:false, rule, message:`${rule}: ${detail}`, action:null});

export function evaluateMergeRules({config, evidence:e = {}, pull:p = {}, ci, trusted, equivalent = {}} = {}) {
  if (!object(e) || !object(p)) return refusal('exact_head','head or base proof unavailable');
  const setting = config?.autopilot?.merge;
  if (setting !== undefined && !object(setting)) return refusal('policy','autopilot.merge must be an object');
  const r = {...DEFAULT_MERGE_RULES,...setting};
  if (Object.keys(setting ?? {}).some(k => !Object.hasOwn(DEFAULT_MERGE_RULES,k))
    || ['fresh_review','full_suite','required_ci','post_merge_audit'].some(k => r[k] !== true)
    || !count(r.max_repairs) || r.max_repairs > DEFAULT_MERGE_RULES.max_repairs
    || !levels.includes(r.autonomy) || !object(r.areas) || Object.values(r.areas).some(v => !levels.includes(v)))
    return refusal('policy','invalid merge rule');
  if (!named(e.head) || e.head !== p.head || !named(e.base) || e.base !== p.base) return refusal('exact_head','head or base differs');
  if (!named(e.authorization) || e.gatesSatisfied !== true) return refusal('authorization','attributed authority and completed gates required');
  const mode = config?.autopilot?.mode, level = Object.hasOwn(r.areas,e.area) ? r.areas[e.area] : r.autonomy;
  if (!['auto','observe'].includes(mode) || trusted !== true || !named(e.area) || level === 'manual') return refusal('autonomy','area or repository does not allow this action');
  const reviews = e.reviews;
  if (typeof e.splitVerdict !== 'boolean' || typeof e.sensitive !== 'boolean'
    || !Array.isArray(reviews) || !reviews.length || reviews.some(v => !object(v) || v.fresh !== true || v.verdict !== 'PASS'
    || v.mustFix !== 0 || !named(v.session) || !named(v.head) || !(v.head === p.head || equivalent[v.head] === true)
    || !Number.isInteger(v.risk) || v.risk < 1 || v.risk > 5)
    || new Set(reviews.map(v => v.session)).size !== reviews.length
    || ((reviews.some(v => v.risk >= 4) || e.splitVerdict === true || e.sensitive === true) && reviews.length < 2))
    return refusal('fresh_review','fresh agreeing review with no must-fix required');
  if (e.fullSuite?.head !== p.head || e.fullSuite?.passed !== true || e.fullSuite?.noNewSkips !== true) return refusal('full_suite','green full suite required on exact head');
  if (ci?.head !== p.head || ci?.complete !== true || !Array.isArray(ci.checks) || !ci.checks.length
    || ci.checks.some(v => !object(v) || !named(v.name)
      || (v.skipped !== undefined && typeof v.skipped !== 'boolean')
      || (v.passed !== true && !(v.passed === false && v.skipped === true)))
    || !ci.checks.some(v => v.passed === true)
    || !Array.isArray(ci.required) || ci.required.some(name => !named(name)
      || !ci.checks.some(v => v.name === name) || ci.checks.some(v => v.name === name && v.passed !== true))
    || !['CLEAN','HAS_HOOKS','BEHIND'].includes(p.mergeStateStatus)) return refusal('required_ci','required checks missing, pending, failed or unknown');
  if (![null,'APPROVED'].includes(p.reviewDecision) || p.pendingReviews !== 0) return refusal('human_review','required or requested review not satisfied');
  if (!count(e.repairs) || e.repairs > r.max_repairs) return refusal('repairs','repair allowance exceeded or unknown');
  if (e.questionOpen !== false) return refusal('question','open question or unknown question status');
  if (e.audit?.planned !== true) return refusal('post_merge_audit','post-merge audit required');
  return {allowed:true, rule:null, message:'Merge rules passed.', action: mode === 'observe' || level === 'observe' ? 'observe' : 'merge'};
}

const execute = nativeGithubCounter(promisify(callback), {purpose:'pulls'});
function nativePorts(cwd, p) {
  const exec = p.execFile ?? execute;
  let repo;
  const repositoryInfo = async () => repo ??= await resolveWorkflowRepository({cwd},{execFile:exec});
  const repository = async () => (await repositoryInfo()).repository;
  const gh = async args => (await exec('gh',args,{cwd,encoding:'utf8',timeout:30000,maxBuffer:8*1024*1024})).stdout;
  const api = async path => JSON.parse(await gh(['api',path]));
  const readConfig = async ref => {
    try {
      const row = await api(`repos/${await repository()}/contents/pdd.json?ref=${encodeURIComponent(ref)}`);
      if (row.encoding !== 'base64' || typeof row.content !== 'string') throw Error('Config unavailable');
      const config = JSON.parse(Buffer.from(row.content,'base64').toString('utf8'));
      if (!object(config)) throw Error('Invalid config');
      return config;
    } catch (error) { if (/\(HTTP 404\)/.test(error.stderr ?? '')) return {}; throw error; }
  };
  const graphql = async (query, variables) => {
    const args = ['api','graphql','-f',`query=${query}`];
    for (const [key,value] of Object.entries(variables)) args.push(typeof value === 'number' ? '-F' : '-f',`${key}=${value}`);
    const out = JSON.parse(await gh(args));
    if (out.errors?.length || !out.data) throw Error('GitHub GraphQL observation failed');
    return out.data;
  };
  const github = {
    async pull(pr) {
      const [owner,name] = (await repository()).split('/');
      const data = await graphql(`query($owner:String!,$name:String!,$pr:Int!){repository(owner:$owner,name:$name){pullRequest(number:$pr){id headRefOid baseRefName baseRefOid state isDraft reviewDecision reviewRequests{totalCount} mergeStateStatus mergeCommit{oid} mergeQueueEntry{id state}}}}`,{owner,name,pr});
      const row = data.repository?.pullRequest;
      if (!row) throw Error('PR missing');
      const queueData = await graphql(`query($owner:String!,$name:String!,$branch:String!){repository(owner:$owner,name:$name){mergeQueue(branch:$branch){id}}}`,{owner,name,branch:row.baseRefName});
      if (!object(queueData.repository) || !Object.hasOwn(queueData.repository,'mergeQueue')) throw Error('Queue unknown');
      return {id:row.id,head:row.headRefOid,base:row.baseRefName,baseOid:row.baseRefOid,
        state:row.state,draft:row.isDraft,reviewDecision:row.reviewDecision,pendingReviews:row.reviewRequests?.totalCount,mergeStateStatus:row.mergeStateStatus,
        mergeCommit:row.mergeCommit?.oid ?? null,queue:queueData.repository.mergeQueue !== null,entry:row.mergeQueueEntry};
    },
    config:pull => readConfig(pull.baseOid),
    async authority() {
      const {defaultBranch} = await repositoryInfo();
      if (!named(defaultBranch)) throw Error('Default branch unavailable');
      return readConfig(defaultBranch);
    },
    async trusted(issue,config) {
      const repositoryName = await repository();
      const author = (await api(`repos/${repositoryName}/issues/${issue}`)).user?.login;
      if (!named(author)) return false;
      if ([repositoryName.split('/')[0],...(Array.isArray(config?.autopilot?.trust) ? config.autopilot.trust : [])]
        .some(v => named(v) && v.toLowerCase() === author.toLowerCase())) return true;
      const permission = (await api(`repos/${repositoryName}/collaborators/${encodeURIComponent(author)}/permission`)).permission;
      return ['admin','maintain','write'].includes(permission);
    },
    async ci(pr,head) {
      const args = ['pr','checks',String(pr),'--repo',await repository(),'--json','name,bucket'];
      const read = async extra => {
        try { return {rows:JSON.parse(await gh([...args,...extra])),complete:true}; }
        catch (error) {
          if ([1,8].includes(error.code) && error.stdout?.trim().startsWith('[')) return {rows:JSON.parse(error.stdout),complete:false};
          if (extra.length && /no required checks reported/i.test(error.stderr ?? '')) return {rows:[],complete:true};
          throw error;
        }
      };
      const checks = await read([]), required = await read(['--required']);
      if (!Array.isArray(checks.rows) || !Array.isArray(required.rows)) throw Error('Checks unknown');
      return {head,complete:checks.complete && required.complete,
        checks:checks.rows.map(v => ({name:v.name,passed:v.bucket === 'pass',skipped:v.bucket === 'skipping'})),required:required.rows.map(v => v.name)};
    },
    async comment(pr,body) {
      // gh owns JSON encoding; body is an argv value, never shell text.
      await gh(['api',`repos/${await repository()}/issues/${pr}/comments`,'-f',`body=${body}`]);
    },
    async enqueue(id,head) {
      return graphql('mutation($id:ID!,$head:GitObjectID!){enqueuePullRequest(input:{pullRequestId:$id,expectedHeadOid:$head}){mergeQueueEntry{id state}}}',{id,head});
    },
    async merge(pr,head) { await gh(['pr','merge',String(pr),'--repo',await repository(),'--merge','--match-head-commit',head]); },
  };
  return {github, async patchEquivalent(oldHead,head) {
    if (![oldHead,head].every(ref => /^[a-f0-9]{40}$/.test(ref))) return false;
    const patch = async ref => {
      const {stdout} = await exec('git',['show','--pretty=format:','--no-ext-diff',ref,'--'],{cwd,encoding:'utf8',maxBuffer:8*1024*1024});
      return stdout;
    };
    const [a,b] = await Promise.all([patch(oldHead),patch(head)]);
    return named(a) && named(b) && await patchIdsEqual(a,b);
  }};
}

// Stream git patch-id without a shell or a temporary file.
function patchIdsEqual(a,b) {
  const id = input => new Promise((resolve,reject) => {
    const child = callback('git',['patch-id','--stable'],{encoding:'utf8',timeout:30000,maxBuffer:8*1024*1024},(err,stdout) => err ? reject(err) : resolve(stdout.trim().split(/\s+/)[0]));
    child.stdin.on('error',reject); child.stdin.end(input);
  });
  return Promise.all([id(a),id(b)]).then(([x,y]) => named(x) && x === y);
}

export async function runAutopilotMerge({pr,cwd=process.cwd(),stdin,observe=false} = {}, ports = {}) {
  let head = null, mergeCommit = null;
  const result = (exitCode,outcome,rule,message) => ({exitCode,outcome,rule,message:rule ? `${rule}: ${message}` : message,head,mergeCommit});
  let e;
  try { e = typeof stdin === 'string' ? JSON.parse(stdin) : stdin; } catch {}
  if (!/^[1-9]\d*$/.test(String(pr)) || !Number.isSafeInteger(Number(pr)) || !object(e) || !Number.isSafeInteger(e.issue) || e.issue < 1)
    return result(2,'refused','input','positive PR, issue and JSON evidence required');
  pr = Number(pr);
  const native = ports.github ? null : nativePorts(cwd,ports), github = ports.github ?? native.github;
  const read = async () => github.pull(pr);
  const reconcile = p => {
    head = p.head ?? head; mergeCommit = p.mergeCommit ?? null;
    if (p.state === 'MERGED') {
      if (!named(mergeCommit)) return result(3,'unknown','merge_result','merged commit unknown');
      if (e.audit?.head === mergeCommit && e.audit?.passed === true && e.audit?.independent === true && named(e.audit?.evidence)) return result(0,'audited',null,'Merged and independently audited.');
      return result(3,'merged_pending_audit','post_merge_audit','audit required on merged commit');
    }
    if (p.state === 'CLOSED') return result(1,'queue_failed','merge_queue','closed without merge');
    if (p.entry?.state === 'UNMERGEABLE') return result(1,'queue_failed','merge_queue','queue checks failed');
    if (p.entry) return result(3,'queued',null,'Waiting for GitHub merge queue result.');
    return null;
  };
  let p;
  try { p = await read(); head = p.head; } catch { return result(1,'refused','merge_queue','PR or queue discovery unavailable'); }
  const settled = reconcile(p);
  if (settled) return settled;
  if (observe) return result(1,'queue_failed','merge_queue','PR has no queue entry and is not merged');
  if (p.state !== 'OPEN' || p.draft !== false) return result(1,'refused','pull_state','open ready PR required');
  if (typeof p.queue !== 'boolean') return result(1,'refused','merge_queue','queue status unknown');
  let baseConfig, config, trusted, ci;
  try { baseConfig = await github.config(p); } catch { return result(1,'refused','policy','base configuration unavailable'); }
  const refreshAuthority = async () => {
    const authority = await github.authority();
    if (!object(authority)) throw Error('Authority unavailable');
    config = {...authority,autopilot:{...authority.autopilot,merge:baseConfig?.autopilot?.merge}};
    trusted = await github.trusted(e.issue,config);
  };
  try { await refreshAuthority(); } catch { return result(1,'refused','autonomy','current repository authority or issue trust unavailable'); }
  try { ci = await github.ci(pr,p.head); } catch { return result(1,'refused','required_ci','checks unavailable'); }
  const equivalent = {};
  for (const review of Array.isArray(e.reviews) ? e.reviews : []) {
    if (named(review?.head) && review.head !== p.head) {
      try { equivalent[review.head] = await (ports.patchEquivalent ?? native?.patchEquivalent)?.(review.head,p.head) === true; } catch { equivalent[review.head] = false; }
    }
  }
  const evaluate = pull => evaluateMergeRules({config,evidence:e,pull,ci,trusted,equivalent});
  let decision = evaluate(p);
  if (!decision.allowed) return result(1,'refused',decision.rule,decision.message.slice(decision.rule.length+2));
  if (!named(e.comment)) return result(1,'refused','comment','authorization and evidence comment required');
  try { await github.comment(pr,e.comment); } catch { return result(1,'refused','comment','comment failed'); }
  if (decision.action === 'observe') return result(0,'would_merge',null,'Would merge.');
  let current;
  try { current = await read(); } catch { return result(1,'refused','exact_head','final PR observation unavailable'); }
  if (current.head !== p.head || current.base !== p.base || current.baseOid !== p.baseOid)
    return result(1,'refused','exact_head','head or base changed before submission');
  if (current.state !== 'OPEN' || current.draft !== false) return reconcile(current) ?? result(1,'refused','pull_state','PR no longer ready');
  if (typeof current.queue !== 'boolean') return result(1,'refused','merge_queue','queue status unknown');
  if (current.entry) return reconcile(current);
  try { ci = await github.ci(pr,p.head); } catch { return result(1,'refused','required_ci','final checks unavailable'); }
  try { await refreshAuthority(); } catch { return result(1,'refused','autonomy','final repository authority or issue trust unavailable'); }
  decision = evaluate(current);
  if (!decision.allowed) return result(1,'refused',decision.rule,decision.message.slice(decision.rule.length+2));
  if (decision.action === 'observe') return result(0,'would_merge',null,'Would merge.');
  let writeFailed = false;
  try {
    if (current.queue) await github.enqueue(current.id,p.head);
    else await github.merge(pr,p.head);
  } catch { writeFailed = true; }
  let after;
  try { after = await read(); } catch { return result(3,'unknown','merge_result','write result unknown; read back before any retry'); }
  if (after.head !== p.head || after.base !== p.base) return result(3,'unknown','exact_head','PR changed during submission');
  const outcome = reconcile(after);
  if (outcome) return outcome;
  if (writeFailed) return result(3,'unknown','merge_result','write result unknown; do not retry automatically');
  return current.queue ? result(1,'queue_failed','merge_queue','queue entry removed without merge')
    : result(3,'unknown','merge_result','direct merge not confirmed');
}

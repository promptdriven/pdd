// Generated from prompts/cli/metrics-command.prompt.md (sha256: 91fee8d3f0656b7e8c9b1bbbdd260b9b563029c85a85e2273cb47d6cb0736d3b).
import {execFile as callback, spawnSync} from 'node:child_process';
import {promisify} from 'node:util';
import {readFile, writeFile, readdir} from 'node:fs/promises';
import {join, resolve} from 'node:path';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
const packageVersion = createRequire(import.meta.url)('../package.json').version;
import {gitContext, readRun} from './workflow-runs.mjs';
import {backfillRun} from './metrics-capture.mjs';
import {calculateMetrics} from './metrics-model.mjs';
import * as ledger from './metrics-store.mjs';
import {nativeGithubCounter} from './github-calls.mjs';

// gh calls go to the GitHub call ledger of their repository; other programs run unchanged.
const execFile = nativeGithubCounter(promisify(callback), {purpose:'other'});
const iso = d => new Date(d).toISOString();
const output = (stream, text) => typeof stream === 'function' ? stream(text) : stream.write(text);
function options(argv) {
  const out = {timezone:'UTC'}, args = [...argv];
  if (['export','import','record'].includes(args[0])) {
    out.action = args.shift(); out.file = args.shift();
    if (!out.file || out.file.startsWith('-')) throw Error(`${out.action} requires a file path`);
  }
  while (args.length) {
    const arg = args.shift();
    if (arg === '--json' && !out.json) out.json = true;
    else if (arg === '--expected-source') { const values = []; while (args[0] && !args[0].startsWith('-')) values.push(args.shift()); if (!values.length || values.some(value => !/^[A-Za-z0-9_.:@+-]+(?:\/[A-Za-z0-9_.:@+-]+)*$/.test(value))) throw Error('Invalid expected source'); (out.expectedSources ??= []).push(...values); }
    else if (['--date','--snapshot','--timezone','--at'].includes(arg)) {
      const key = arg.slice(2), value = args.shift();
      if (!value || value.startsWith('-') || out[key] && key !== 'timezone') throw Error(`Invalid ${arg}`);
      out[key] = value;
    } else throw Error(`Unknown option: ${arg}`);
  }
  if (out.date && out.snapshot || out.action && (out.date || out.snapshot || out.json || out.at || out.expectedSources)) throw Error('Options cannot be combined');
  if (out.date && (!/^\d{4}-\d\d-\d\d$/.test(out.date) || !Number.isFinite(Date.parse(`${out.date}T00:00:00Z`)) || iso(`${out.date}T00:00:00Z`).slice(0,10) !== out.date)) throw Error('Invalid date');
  if (out.at && !out.date && !out.snapshot) throw Error('--at requires --date or --snapshot');
  if (out.at && (!/^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d(?:\.\d{1,3})?Z$/.test(out.at) || !Number.isFinite(Date.parse(out.at)))) throw Error('Invalid cutoff');
  try { new Intl.DateTimeFormat('en', {timeZone:out.timezone}); } catch { throw Error('Invalid timezone'); }
  return out;
}
async function repository(cwd) {
  const ctx = await gitContext(cwd);
  if (!ctx) throw Error('Current directory is not in a Git repository');
  let stdout; try { ({stdout} = await execFile('git',['remote','get-url','origin'],{cwd})); } catch {
    const local = await ledger.readEvents({root:ctx.toplevel ?? cwd});
    const repos = [...new Set(local.events.map(e => e.repo))];
    if (repos.length !== 1) throw Error('Repository identity unavailable or ambiguous in local metrics');
    return {...ctx,repo:repos[0]};
  }
  const remote = stdout.trim().replace(/^git@github\.com:/,'https://github.com/');
  let url; try {url = new URL(remote);} catch {throw Error('Origin must identify a GitHub repository');}
  const match = url.hostname === 'github.com' && /^\/([^/]+)\/([^/]+?)(?:\.git)?\/?$/.exec(url.pathname);
  if (!match) throw Error('Origin must identify a GitHub repository');
  return {...ctx, repo:`${match[1]}/${match[2]}`.toLowerCase()};
}
async function historical({commonDir,repo}, observedAt) {
  const events = [];
  const gapDir=join(commonDir,'pdd','metrics-gaps');
  let gapNames; try {gapNames=await readdir(gapDir);} catch(e) {if(e.code!=='ENOENT') throw e;gapNames=[];}
  for (const name of gapNames.filter(n=>/^[0-9a-f-]{36}\.json$/i.test(n))) { try {const event=JSON.parse(await readFile(join(gapDir,name),'utf8')); if(event.repo===repo && event.type==='coverage' && event.data?.complete===false) events.push(event);} catch {} }
  const snapshotsDir=join(commonDir,'pdd','metrics','snapshots'), committedSnapshots=new Set();
  let snapshotNames; try {snapshotNames=await readdir(snapshotsDir);} catch(e) {if(e.code!=='ENOENT') throw e;snapshotNames=[];}
  for (const name of snapshotNames.filter(n=>/^[0-9a-f-]{36}\.json$/i.test(n))) {
    try {const snapshot=JSON.parse(await readFile(join(snapshotsDir,name),'utf8'));
      if(snapshot.repo!==repo || snapshot.snapshotId!==`snapshot:${name.slice(0,-5)}` || !Array.isArray(snapshot.events) || snapshot.events.some(e=>e.repo!==repo || e.type!=='selection' || e.data?.snapshotId!==snapshot.snapshotId)) continue;
      committedSnapshots.add(snapshot.snapshotId); events.push(...snapshot.events);
    } catch {}
  }
  const decisionsDir = join(commonDir,'pdd','metrics','decisions');
  let decisionNames; try { decisionNames = await readdir(decisionsDir); } catch (e) { if (!['ENOENT','ENOTDIR'].includes(e.code)) throw e; decisionNames = []; }
  for (const name of decisionNames.filter(n => /^[0-9a-f-]{36}\.json$/i.test(n))) {
    let decision; try { decision = JSON.parse(await readFile(join(decisionsDir,name),'utf8')); } catch { continue; }
    if (decision.pendingSnapshot && !committedSnapshots.has(decision.snapshotId)) continue;
    if (`${decision.id}.json` !== name || decision.repo !== repo || !Number.isSafeInteger(decision.issue) || decision.issue < 1 || !Array.isArray(decision.events)) continue;
    if (decision.events.some(e => e.schema !== 'pdd.metrics.event.v1' || e.repo !== repo || e.issue !== decision.issue || !['selection','launch'].includes(e.type))) continue;
    events.push(...decision.events);
  }
  let names; try { names = await readdir(join(commonDir,'pdd','runs')); } catch (e) {if (e.code === 'ENOENT') return events; throw e;}
  for (const name of names.filter(n => /^[1-9]\d*(?:-cancelled-[0-9a-f]+)?$/.test(n))) {
    const run = readRun(join(commonDir,'pdd','runs',name));
    if (!run || run.repo?.toLowerCase() !== repo || !run.runId) continue;
    if (Array.isArray(run.metrics?.events)) events.push(...run.metrics.events);
    for (const pr of run.pr ?? []) {
      if (!Number.isSafeInteger(pr.number) || pr.number < 1 || !observedAt) continue;
      const area = (run.areas ?? []).find(a => a.name === pr.stage);
      const stage = area?.then === 'ask-code' ? 'prompt-pr' : (area?.name === 'code' || run.workflow === 'small-change') ? 'code-pr' : 'pr-mapped';
      events.push({schema:'pdd.metrics.event.v1',id:`run:${run.runId}:pr:${pr.number}`,repo,issue:run.number,type:'milestone',at:observedAt,observedAt,source:`legacy:${repo}`,attempt:run.runId,data:{stage,pr:pr.number}});
    }
    if (run.metrics?.coverageGap && Number.isFinite(run.metrics.coverageGapAt)) {
      const at = iso(run.metrics.coverageGapAt);
      events.push({schema:'pdd.metrics.event.v1',id:`run:${run.runId}:capture-gap`,repo,issue:run.number,type:'coverage',at,observedAt:at,source:`gap:${run.runId}`,attempt:run.runId,data:{complete:false}});
    }
    // Preserve only facts with saved event times.
    for (const [step, item] of Object.entries(run.done ?? {})) {
      if (!item?.at || !Number.isFinite(new Date(item.at).getTime())) continue;
      const observedAt = iso(item.at);
      const fallback = backfillRun({run:{...run,done:{[step]:item}},source:`legacy:${repo}`,observedAt,idPrefix:`run:${run.runId}`});
      events.push(...fallback.filter(fact => !(Array.isArray(run.metrics?.events) ? run.metrics.events : []).some(e => e?.schema === fact.schema && e.repo?.toLowerCase() === fact.repo && e.issue === fact.issue && e.attempt === fact.attempt && e.type === 'step' && e.data?.step === fact.data.step && e.data?.status === fact.data.status && Number.isFinite(Date.parse(e.at)) && Date.parse(e.at) === Date.parse(fact.at) && (!e.data.area || !fact.data.area || e.data.area === fact.data.area))));
    }
  }
  return events;
}
async function selectorSnapshots({repo, commonDir, snapshots = []}) {
  const result = snapshots.filter(s => s.repo === repo);
  try {
    const dir = join(commonDir,'pdd','metrics','snapshots');
    for (const name of await readdir(dir)) {
      if (!/^[0-9a-f-]{36}\.json$/i.test(name)) continue;
      try {
        const value = JSON.parse(await readFile(join(dir,name),'utf8'));
        if (value.repo === repo && value.snapshotId === `snapshot:${name.slice(0,-5)}` && Array.isArray(value.events) && Number.isFinite(Date.parse(value.observedAt)) && value.events.every(e => e.repo === repo && e.type === 'selection' && e.data?.snapshotId === value.snapshotId)) result.push(value);
      } catch { /* Ignore incomplete snapshots. */ }
    }
  } catch (e) { if (e.code !== 'ENOENT') throw e; }
  return result.sort((a,b) => Date.parse(b.observedAt)-Date.parse(a.observedAt));
}
async function githubQueue({repo, observedAt, commonDir, snapshots = []}) {
  const {stdout} = await execFile('gh',['api','--paginate',`repos/${repo}/issues?state=open&per_page=100`,'--jq','.[] | select(.pull_request == null) | {number}'],{maxBuffer:16*1024*1024});
  const rows = stdout.trim() ? stdout.trim().split('\n').map(line=>JSON.parse(line)) : [];
  const snapshotId = `queue:${observedAt}`;
  const latest = (await selectorSnapshots({repo,commonDir,snapshots}))[0];
  return {snapshotId,selectorSnapshot:latest,events:rows.map(({number})=>({schema:'pdd.metrics.event.v1',id:`${snapshotId}:${number}`,repo,issue:number,type:'selection',at:observedAt,observedAt,source:`github:${repo}`,data:{snapshotId,inScope:true,state:'unknown',reasons:['Selector observation unavailable']}}))};
}
// Public checker comments carry evidence in prose, lists, or named fields.
function substantiveEvidence(value) {
  if (typeof value === 'string') return /[a-z]{3,}.*[\s:/].*[a-z0-9]{2,}/i.test(value.trim());
  if (Array.isArray(value)) return value.some(substantiveEvidence);
  if (value && typeof value === 'object') return Object.values(value).some(substantiveEvidence);
  return false;
}
function checkerSession(value) {
  return typeof value === 'string' && value.length <= 200 && /^\/?[a-z0-9_.:-]+(?:\/[a-z0-9_.:-]+)*$/i.test(value) && !value.split('/').some(part => part === '.' || part === '..');
}
function reviewer(check) {
  return `${check.family}:session-${Buffer.from(check.session).toString('base64url')}`;
}
async function githubFacts({repo, observedAt, events, cwd}) {
  let trusted = [];
  try { const config = JSON.parse(await readFile(join(cwd,'pdd.json'),'utf8')); trusted = Array.isArray(config.autopilot?.trust) ? config.autopilot.trust.filter(x => typeof x === 'string').map(x => x.toLowerCase()) : []; } catch { /* No explicit trusted people. */ }
  const mappings = new Map(), codeMappings = new Set();
  for (const e of events) if (e.type === 'milestone' && e.data?.pr) {
    if (e.data.stage === 'code-pr' || e.data.stage === 'implementation-ready') codeMappings.add(`${e.data.pr}:${e.issue}`);
    const issues = mappings.get(e.data.pr) ?? new Set(); issues.add(e.issue); mappings.set(e.data.pr,issues);
  }
  const facts = [];
  for (const [pr,issues] of mappings) {
    try {
    const read = async path => (await execFile('gh',['api','--paginate',path],{maxBuffer:16*1024*1024})).stdout;
    const pull = JSON.parse(await read(`repos/${repo}/pulls/${pr}`));
    if (pull.merged_at && pull.html_url && pull.head?.sha) for (const issue of issues) if (codeMappings.has(`${pr}:${issue}`)) facts.push({schema:'pdd.metrics.event.v1',id:`merge:${pr}:${issue}`,repo,issue,type:'delivery',at:iso(pull.merged_at),observedAt,source:`github:${repo}`,data:{pr,head:pull.head.sha,explicit:true,evidence:pull.html_url}});
    if (pull.head?.sha && /^[a-f0-9]{40}$/i.test(pull.head.sha)) for (const issue of issues) if (codeMappings.has(`${pr}:${issue}`)) facts.push({schema:'pdd.metrics.event.v1',id:`head:${pr}:${pull.head.sha}:${observedAt}:${issue}`,repo,issue,type:'milestone',at:observedAt,observedAt,source:`github:${repo}`,data:{stage:'candidate-head',pr,head:pull.head.sha}});
    const {stdout: text} = await execFile('gh',['api','--paginate',`repos/${repo}/issues/${pr}/comments?per_page=100`,'--jq','.[] | {id,body,html_url,created_at,author_association,user}'],{maxBuffer:16*1024*1024});
    const comments = text.trim() ? text.trim().split('\n').map(line => JSON.parse(line)) : [];
    const checks = [], allowed = new Set();
    for (const comment of comments) {
      const login = comment.user?.login;
      if (comment.author_association === 'OWNER' || (typeof login === 'string' && trusted.includes(login.toLowerCase()))) { allowed.add(comment); continue; }
      if (!['MEMBER','COLLABORATOR'].includes(comment.author_association) || typeof login !== 'string' || !/^[a-z0-9](?:[a-z0-9-]{0,37}[a-z0-9])?$/i.test(login)) continue;
      try { const permission = JSON.parse(await read(`repos/${repo}/collaborators/${login}/permission`)); if (['write','maintain','admin'].includes(permission.permission)) allowed.add(comment); } catch { /* Unknown trust cannot establish acceptance. */ }
    }
    for (const comment of comments.filter(comment => allowed.has(comment))) for (const block of String(comment.body ?? '').matchAll(/```(?:json)?\s*([\s\S]*?)```/g)) {
      let check; try {check = JSON.parse(block[1]);} catch {continue;}
      if (!['PASS','FAIL','NOT SURE'].includes(check.verdict) || !/^[a-f0-9]{40}$/i.test(check.head ?? '') || !Number.isInteger(check.risk) || check.risk < 1 || check.risk > 5 || !/^[a-z0-9_-]+$/i.test(check.family ?? '') || !checkerSession(check.session) || !['same-family','different-family'].includes(check.checker_mode) || !substantiveEvidence(check.evidence) || !comment.html_url || !comment.created_at) continue;
      checks.push({check,comment,isTrusted:true});
    }
    let sensitive = null;
    if (checks.length) try {
      const {stdout: files} = await execFile('gh',['api','--paginate',`repos/${repo}/pulls/${pr}/files?per_page=100`,'--jq','.[] | .filename'],{maxBuffer:16*1024*1024});
      sensitive = files.split('\n').some(name => /(?:^|\/)(?:pdd-check|pdd-merge|approval)(?:\/|[.-])/.test(name));
    } catch { /* Unknown changed files cannot prove whether a second check is needed. */ }
    const current = checks.filter(x => x.isTrusted && x.check.head === pull.head?.sha);
    const split = new Set(current.map(x => x.check.verdict)).size > 1;
    let suiteGreen = false;
    if (pull.head?.sha) {
      let runs;
      try { const result = JSON.parse(await read(`repos/${repo}/commits/${pull.head.sha}/check-runs?per_page=100`)); runs = Array.isArray(result.check_runs) ? result.check_runs.filter(run => run.head_sha === pull.head.sha) : null; } catch { runs = null; }
      suiteGreen = Boolean(runs?.some(run => /^(?:full suite|full test suite)$/i.test(run.name ?? '') && run.status === 'completed' && run.conclusion === 'success'));
      const observations = runs?.length ? runs.map(run => ({key:String(run.id ?? createHash('sha256').update(String(run.name ?? '') + '\0' + String(run.html_url ?? '')).digest('hex')), status: run.status === 'completed' ? (run.conclusion === 'success' ? 'passed' : ['failure','timed_out','action_required','startup_failure'].includes(run.conclusion) ? 'failed' : 'unknown') : 'unknown', evidence: run.html_url, reason: run.name})) : [{key:'none',status: runs ? 'missing' : 'unknown'}];
      for (const [index, observation] of observations.entries()) for (const issue of issues) facts.push({schema:'pdd.metrics.event.v1',id:`ci:${pr}:${pull.head.sha}:${observation.key}:${issue}:${observation.status}`,repo,issue,type:'ci',at:observedAt,observedAt,source:`github:${repo}`,data:{pr,head:pull.head.sha,...Object.fromEntries(Object.entries(observation).filter(([k,v]) => k !== 'key' && v !== undefined))}});
    }
    const patchId = head => {
      const diff = spawnSync('git',['show','--format=','--binary',head],{cwd,maxBuffer:32*1024*1024});
      if (diff.status !== 0 || !diff.stdout.length) return null;
      const patch = spawnSync('git',['patch-id','--stable'],{cwd,input:diff.stdout});
      return patch.status === 0 ? String(patch.stdout).trim().split(/\s+/)[0] || null : null;
    };
    for (const {check,comment,isTrusted} of checks) {
      const secondNeeded = check.risk >= 4 || split || sensitive === true;
      const second = current.some(x => x !== undefined && x.check !== check && x.check.verdict === check.verdict && x.check.session !== check.session && (x.check.family.toLowerCase() !== check.family.toLowerCase() || (x.check.checker_mode === 'same-family' && check.checker_mode === 'same-family')));
      const accepted = isTrusted && check.head === pull.head?.sha && sensitive !== null && (!secondNeeded || second);
      for (const issue of issues) facts.push({schema:'pdd.metrics.event.v1',id:`check:${comment.id}:${issue}`,repo,issue,type:'check',at:iso(comment.created_at),observedAt,source:`github:${repo}`,data:{pr,head:check.head,verdict:check.verdict,reviewer:reviewer(check),checkerFamily:check.family,checkerMode:check.checker_mode,evidence:comment.html_url,acceptance:accepted ? 'accepted' : 'unknown'}});
      if (isTrusted && check.verdict === 'PASS' && check.head !== pull.head?.sha && suiteGreen && sensitive === false && check.risk < 4 && !split) {
        const oldId = patchId(check.head), newId = patchId(pull.head.sha);
        if (oldId && oldId === newId) for (const issue of issues) facts.push({schema:'pdd.metrics.event.v1',id:`equivalent:${comment.id}:${pull.head.sha}:${issue}`,repo,issue,type:'check',at:observedAt,observedAt,source:`github:${repo}`,data:{pr,head:pull.head.sha,verdict:'PASS',reviewer:reviewer(check),checkerFamily:check.family,checkerMode:check.checker_mode,evidence:comment.html_url,acceptance:'equivalent'}});
      }
    }
    } catch {
      for (const issue of issues) facts.push({schema:'pdd.metrics.event.v1',id:`github-gap:${pr}:${observedAt}:${issue}`,repo,issue,type:'coverage',at:observedAt,observedAt,source:`github-gap:${repo}`,data:{complete:false}});
    }
  }
  return facts;
}
function githubGaps(repo, observedAt, events) {
  return [...new Set(events.filter(e => e.repo === repo).map(e => e.issue))].map(issue => ({schema:'pdd.metrics.event.v1',id:`github-gap:${observedAt}:${issue}`,repo,issue,type:'coverage',at:observedAt,observedAt,source:`github-gap:${repo}`,data:{complete:false}}));
}
function render(report) {
  const lines = [`PDD metrics — ${report.repo}`, `Scope: ${report.scope.kind}${report.scope.date ? ` ${report.scope.date}` : ''}${report.scope.snapshotId ? ` ${report.scope.snapshotId}` : ''}`, `Cutoff: ${report.observedAt} (${report.timezone})`, `Sources: ${(report.sources ?? []).map(s => typeof s === 'string' ? s : s.source).join(', ') || 'none'}`, `Coverage: ${report.coverage?.complete ? 'complete' : 'incomplete'}; missing sources: ${(report.coverage?.missingSources ?? []).join(', ') || 'none recorded'}`];
  const fraction = (name, value) => lines.push(`${name}: ${value.numerator}/${value.denominator} (${value.percentage == null ? 'n/a' : `${value.percentage}%`}; unknown: ${value.unknown}; denominator unknown: ${value.denominatorUnknown ?? 0}; issues: ${(value.issues ?? []).map(i => `#${i}`).join(', ') || 'none'})`);
  for (const [name, value] of Object.entries(report.stages ?? {})) fraction(`Stage ${name}`, value);
  for (const [name, value] of Object.entries(report.transitions ?? {})) fraction(`Transition ${name}`, value);
  if (report.activity === null) lines.push('Daily activity: use --date YYYY-MM-DD');
  for (const [name, group] of Object.entries(report.activity ?? {})) lines.push(`Activity ${name}: ${group.count} ${(group.issues ?? []).map(i => `#${i}`).join(', ')}`);
  if (report.selectorObservation) lines.push(`Selector observation ${report.selectorObservation.snapshotId} at ${report.selectorObservation.observedAt}: ${report.selectorObservation.limit}`);
  for (const [name, group] of Object.entries(report.selectorObservation?.queue ?? {})) lines.push(`Observed selector ${name}: ${group.count}`);
  for (const [name, group] of Object.entries(report.queue ?? {})) lines.push(`Queue ${name}: ${group.count} ${(group.issues ?? []).map(i => `#${i.issue}${i.reasons?.length ? ` (${i.reasons.join('; ')})` : ''}`).join(', ')}`);
  for (const issue of report.issues ?? []) {
    lines.push(`#${issue.issue}: started ${issue.started}, origins ${(issue.origins ?? []).join(', ') || 'unknown'}, PR created ${issue.prCreated}, implementation ready ${issue.implementationReady}, validated ${issue.validated}, delivered ${issue.delivered}, failed fix ${issue.failedFix}, assistance ${issue.assistance?.status ?? 'unknown'}`);
    for (const wait of issue.waits ?? []) lines.push(`  Waiting: ${wait.stage}, ${wait.reason}, since ${wait.since}, elapsed ${wait.elapsedMs}ms`);
    for (const entry of issue.deliveryFollowUps ?? []) lines.push(`  Delivery #${entry.delivery.data.pr}: ${Object.entries(entry.followUp).map(([days, v]) => `${days} days ${v.status}`).join(', ')}`);
    for (const event of [issue.candidate, ...(issue.checks ?? []), ...(issue.ci ?? []), ...(issue.deliveries ?? []), ...(issue.reports ?? []), ...(issue.assistance?.events ?? []), ...(issue.coverage ?? [])].filter(Boolean)) lines.push(`  Evidence ${event.type}: ${event.data.status ?? event.data.verdict ?? event.data.classification ?? ''} ${event.data.evidence ?? ''}`.trimEnd());
  }
  return lines.join('\n') + '\n';
}
export async function runMetrics({argv = [], cwd = process.cwd(), stdout = process.stdout, stderr = process.stderr, ports = {}} = {}) {
  try {
    const opt = options(argv), context = await (ports.repository ?? repository)(cwd);
    const root = context.toplevel ?? context.root ?? cwd, repo = context.repo.toLowerCase();
    const now = iso((ports.now ?? (()=>new Date()))()), cutoff = opt.at ? iso(opt.at) : now;
    const store = ports.store ?? ledger;
    if (opt.action === 'export') {
      const historic = await (ports.historical ?? historical)(context,now);
      if (historic.length) await store.appendEvents({root,events:historic});
      const saved = await store.readEvents({root});
      const known = [...(saved.events ?? saved), ...historic];
      let facts; try { facts = await (ports.github ?? githubFacts)({repo,observedAt:now,cwd,events:known}); } catch { facts = githubGaps(repo,now,known); }
      if (facts.length) await store.appendEvents({root,events:facts});
      const bundle = await store.exportMetrics({root,metadata:{repo,timezone:opt.timezone,exportedAt:now,cliVersion:packageVersion}});
      await (ports.writeFile ?? writeFile)(resolve(cwd,opt.file),JSON.stringify(bundle,null,2)+'\n',{mode:0o600});
      output(stdout,`Exported metrics to ${opt.file}\n`); return 0;
    }
    if (opt.action === 'import' || opt.action === 'record') {
      const value = JSON.parse(await (ports.readFile ?? readFile)(resolve(cwd,opt.file),'utf8'));
      if (opt.action === 'import') {
        if (value.repo?.toLowerCase() !== repo) throw Error('Bundle belongs to another repository');
        await store.importMetrics({root,bundle:value});
      } else {
        const events = Array.isArray(value) ? value : [value];
        if (events.some(e=>e.repo?.toLowerCase() !== repo)) throw Error('Event belongs to another repository');
        await store.appendEvents({root,events});
      }
      output(stdout,`${opt.action === 'import' ? 'Imported' : 'Recorded'} metrics from ${opt.file}\n`); return 0;
    }
    const historic = await (ports.historical ?? historical)(context,now);
    if (historic.length) await store.appendEvents({root,events:historic});
    const saved = await store.readEvents({root});
    let events = [...(saved.events ?? saved), ...historic], scope;
    let githubUnavailable = false, selectorSnapshot;
    if (opt.date) scope = {kind:'activity',date:opt.date};
    else if (opt.snapshot) scope = {kind:'cohort',snapshotId:opt.snapshot};
    else {
      let queue; try { queue = await (ports.selector ?? githubQueue)({repo,observedAt:now,cwd,events,commonDir:context.commonDir,snapshots:saved.snapshots ?? []}); } catch { githubUnavailable = true; queue = {snapshotId:`queue:${now}`,events:[],selectorSnapshot:(await selectorSnapshots({repo,commonDir:context.commonDir,snapshots:saved.snapshots ?? []}))[0]}; }
      selectorSnapshot = queue.selectorSnapshot;
      events.push(...queue.events); await store.appendEvents({root,events:queue.events}); scope = {kind:'queue',snapshotId:queue.snapshotId};
    }
    let facts; try { facts = await (ports.github ?? githubFacts)({repo,observedAt:now,cwd,events}); } catch { githubUnavailable = true; facts = githubGaps(repo,now,events); }
    events.push(...facts); if (facts.length) await store.appendEvents({root,events:facts});
    const report = await (ports.calculate ?? calculateMetrics)({events,repo,scope,timezone:opt.timezone,observedAt:cutoff,sources:[...(saved.sources ?? []), ...[...new Set(events.map(e=>e.source))].filter(source => !(saved.sources ?? []).some(s => (typeof s === 'string' ? s : s.source) === source)), ...(githubUnavailable && !events.some(e => e.source === `github:${repo}`) ? [`github:${repo}`] : []), ...(opt.expectedSources ?? []).filter(source => !events.some(e => e.source === source) && !(saved.sources ?? []).some(s => (typeof s === 'string' ? s : s.source) === source))]});
    if (selectorSnapshot) {
      const observed = await (ports.calculate ?? calculateMetrics)({events:[...events,...selectorSnapshot.events],repo,scope:{kind:'cohort',snapshotId:selectorSnapshot.snapshotId},timezone:opt.timezone,observedAt:now,sources:[]});
      report.selectorObservation = {snapshotId:selectorSnapshot.snapshotId,observedAt:selectorSnapshot.observedAt,limit:'Historical selector observation; current validity unknown',queue:observed.queue,issues:observed.issues.map(({issue,selection}) => ({issue,selection}))};
    }
    if (githubUnavailable && report.coverage && !report.coverage.missingSources.includes(`github:${repo}`)) report.coverage.missingSources.push(`github:${repo}`);
    output(stdout,opt.json ? JSON.stringify(report,null,2)+'\n' : render(report)); return 0;
  } catch (error) { output(stderr,`pdd metrics: ${error.message}\n`); return 1; }
}

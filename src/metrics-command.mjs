// Generated from prompts/cli/metrics-command.prompt.md (sha256: 943d89335977d81983f4bdbb6bc45749be9e8597f10b3a11fff43c4f5530e9c4).
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
const safeIso = (value, fallback) => value && Number.isFinite(Date.parse(value)) ? iso(value) : fallback;
const validSha = sha => typeof sha === 'string' && /^[a-f0-9]{40}$/i.test(sha);
const cleanEvidence = value => {
  if (typeof value !== 'string' || !value) return undefined;
  try {
    const u = new URL(value);
    if (u.protocol !== 'https:' || u.username || u.password || u.search) return undefined;
    if (/^(?:localhost|127\.|10\.|192\.168\.|169\.254\.|172\.(?:1[6-9]|2[0-9]|3[01])\.|\[::1\])/i.test(u.hostname)) return undefined;
    if (u.hash && !(u.hostname === 'github.com' && /^#(?:issuecomment|check-run)-[0-9]+$/.test(u.hash))) return undefined;
    return value;
  } catch { return undefined; }
};
const SKILL_NAMES = new Set(['small-change', 'bug', 'feature', 'no-behavior-change']);
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
    if (SKILL_NAMES.has(run.workflow)) {
      const skillAt = (Array.isArray(run.metrics?.events) ? run.metrics.events.map(e => e?.at) : [])
        .concat(Object.values(run.done ?? {}).map(d => d?.at))
        .find(t => t && Number.isFinite(new Date(t).getTime()));
      const ts = skillAt ? iso(skillAt) : observedAt;
      if (ts) events.push({schema:'pdd.metrics.event.v1',id:`run:${run.runId}:skill`,repo,issue:run.number,type:'milestone',at:ts,observedAt:observedAt ?? ts,source:`legacy:${repo}`,attempt:run.runId,data:{stage:'skill',reason:run.workflow}});
    }
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
      const savedObservedAt = iso(item.at);
      const fallback = backfillRun({run:{...run,done:{[step]:item}},source:`legacy:${repo}`,observedAt:savedObservedAt,idPrefix:`run:${run.runId}`});
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

function parseJsonList(stdout) {
  const trimmed = String(stdout ?? '').trim();
  if (!trimmed) return [];
  try {
    const parsed = JSON.parse(trimmed);
    return Array.isArray(parsed) ? parsed : (parsed && typeof parsed === 'object' ? [parsed] : []);
  } catch {
    const items = [];
    for (const line of trimmed.split('\n')) {
      if (!line.trim()) continue;
      try {
        const value = JSON.parse(line);
        if (Array.isArray(value)) items.push(...value);
        else if (value && typeof value === 'object') items.push(value);
      } catch { /* skip non-JSON line */ }
    }
    return items;
  }
}

function normalizeReceiptStatus(entry) {
  if (entry == null) return null;
  if (typeof entry === 'string') {
    const v = entry.trim().toLowerCase();
    if (['not-applicable', 'na', 'n/a', 'none', 'not-needed', 'not_applicable'].includes(v)) return 'not-applicable';
    if (['done', 'pass', 'passed', 'proved', 'bounded', 'yes', 'true', 'ok'].includes(v)) return 'done';
    if (['missed', 'fail', 'failed', 'blocked', 'no', 'false'].includes(v)) return 'missed';
    if (v === 'unknown') return 'unknown';
    return null;
  }
  if (typeof entry === 'object') {
    if (entry.applies === false) return 'not-applicable';
    if (entry.done === true) return 'done';
    if (entry.done === false && entry.applies === true) return 'missed';
    if (typeof entry.status === 'string') return normalizeReceiptStatus(entry.status);
  }
  return null;
}

function parseReceiptMetadata(text, labels = []) {
  const body = String(text ?? '');
  const labelNames = (Array.isArray(labels) ? labels : [])
    .map(l => (typeof l === 'string' ? l : String(l?.name ?? '')).trim().toLowerCase())
    .filter(Boolean);

  let skill = null;
  let wouldMerge = labelNames.includes('pdd:would-merge') || labelNames.includes('would-merge');
  const checks = { runtime: null, vectors: null, formal: null, complete: null };

  if (labelNames.includes('pdd:no-behavior-change') || labelNames.includes('no-behavior-change')) skill = 'no-behavior-change';
  else if (labelNames.includes('pdd:small-change') || labelNames.includes('small-change')) skill = 'small-change';
  else if (labelNames.includes('pdd:bug') || labelNames.includes('bug')) skill = 'bug';
  else if (labelNames.includes('pdd:feature') || labelNames.includes('feature')) skill = 'feature';

  for (const block of body.matchAll(/```(?:json)?\s*([\s\S]*?)```/g)) {
    let parsed;
    try { parsed = JSON.parse(block[1]); } catch { continue; }
    if (!parsed || typeof parsed !== 'object') continue;
    if (parsed.wouldMerge === true || parsed.would_merge === true || parsed.disposition === 'would-merge') wouldMerge = true;
    const jsonSkill = String(parsed.skill ?? parsed.workflow ?? '').trim().toLowerCase();
    if (SKILL_NAMES.has(jsonSkill)) skill = jsonSkill;
    if (parsed.applies === false) skill = 'no-behavior-change';
    const checkSource = parsed.checks && typeof parsed.checks === 'object' ? parsed.checks
      : parsed.receipts && typeof parsed.receipts === 'object' ? parsed.receipts
      : null;
    if (checkSource) {
      for (const key of ['runtime', 'vectors', 'formal', 'complete']) {
        const status = normalizeReceiptStatus(checkSource[key]);
        if (status) checks[key] = status;
      }
    }
  }

  if (/<!--\s*pdd:autopilot-core:would-merge:/i.test(body)) wouldMerge = true;

  const noBehaviorProse = /\bno-behavior-change\b/i.test(body) || /\bPath:\s*b\b/.test(body);
  if (noBehaviorProse) {
    skill = 'no-behavior-change';
  } else {
    const workflowMatch = /Made with `pdd workflow run (small-change|bug|feature|no-behavior-change)`/i.exec(body)
      || /<!--\s*pdd[-:](?:workflow|skill|autopilot)[^>]*(small-change|bug|feature|no-behavior-change)/i.exec(body)
      || /(?:^|\n)\s*(?:[-*]\s*)?(?:Skill|Workflow)\s*:\s*`?(small-change|bug|feature|no-behavior-change)`?(?:\s|$)/i.exec(body);
    if (workflowMatch) skill = workflowMatch[1].toLowerCase();
  }

  if (!checks.runtime) {
    if (/\bPath:\s*b\b/.test(body) || /(?:Prompt tests|Runtime(?:\s*\([^)]*\))?)\s*:\s*(?:not applicable|n\/a|none|no line\b|not run\s*\((?:no[- ]story|native-only|no prompt|docs))/i.test(body)) {
      checks.runtime = 'not-applicable';
    } else if (/(?:Prompt tests|Runtime(?:\s*\([^)]*\))?)\s*:[^\n]*\b(?:FAIL|failed|missed)\b/i.test(body)) {
      checks.runtime = 'missed';
    } else if (/(?:Prompt tests|Runtime(?:\s*\([^)]*\))?)\s*:[^\n]*\b(?:PASS|passed|\d+\s+of\s+\d+\s+Stories\s+pass)\b/i.test(body)) {
      checks.runtime = 'done';
    }
  }
  if (!checks.vectors) {
    if (/\bPath:\s*b\b/.test(body) || /Replay and formal tests[^:\n]*:\s*none changed/i.test(body) || /Code replay:\s*NOT APPLICABLE/i.test(body) || /(?:Vectors?|Replay tests?)\s*:\s*(?:not applicable|n\/a|none)/i.test(body) || /\bvectors\s*=\s*(?:none|n\/a|not-applicable)\b/i.test(body)) {
      checks.vectors = 'not-applicable';
    } else if (/Code replay:\s*(?:FAIL|BLOCKED)\b/i.test(body) || /(?:Vectors?|Replay tests?[^:\n]*)\s*:\s*(?:FAIL|failed|missed)\b/i.test(body) || /\bvectors\s*=\s*(?:fail|failed|missed)\b/i.test(body)) {
      checks.vectors = 'missed';
    } else if (/Code replay:\s*PASS\b/i.test(body) || /(?:Vectors?|Replay tests?[^:\n]*)\s*:\s*(?:PASS|passed|done)\b/i.test(body) || /\bvectors\s*=\s*(?:pass|passed|done)\b/i.test(body)) {
      checks.vectors = 'done';
    }
  }
  if (!checks.formal) {
    if (/\bPath:\s*b\b/.test(body) || /Replay and formal tests[^:\n]*:\s*none changed/i.test(body) || /Formal check:\s*not needed/i.test(body) || /(?:Formal(?:\s+tests?|\s+check)?)\s*:\s*(?:not applicable|not needed|n\/a|none)/i.test(body) || /\bformal\s*=\s*(?:none|n\/a|not-applicable)\b/i.test(body)) {
      checks.formal = 'not-applicable';
    } else if (/✗\s*Formal check failed/i.test(body) || /(?:Formal(?:\s+tests?[^:\n]*|\s+check)?)\s*:\s*(?:FAIL|failed|missed)\b/i.test(body) || /\bformal\s*=\s*(?:fail|failed|missed)\b/i.test(body)) {
      checks.formal = 'missed';
    } else if (/Formal check \(agent reported\):\s*recorded\s*—\s*(?:proved|bounded|pass)/i.test(body) || /(?:Formal(?:\s+tests?[^:\n]*|\s+check)?)\s*:\s*(?:PASS|passed|proved|bounded|done)\b/i.test(body) || /\bformal\s*=\s*(?:proved|bounded|pass|passed|done)\b/i.test(body)) {
      checks.formal = 'done';
    }
  }
  if (!checks.complete) {
    if (/Complete\s*:\s*(?:not applicable|n\/a|none)/i.test(body)) checks.complete = 'not-applicable';
    else if (/Complete\s*:\s*(?:FAIL|failed|missed)\b/i.test(body)) checks.complete = 'missed';
    else if (/Complete\s*:\s*(?:PASS|passed|done)\b/i.test(body)) checks.complete = 'done';
  }
  if (skill === 'no-behavior-change') {
    for (const key of ['runtime', 'vectors', 'formal', 'complete']) {
      if (!checks[key]) checks[key] = 'not-applicable';
    }
  }

  return { skill, wouldMerge, checks };
}

function extractPrIssueLinks(pull) {
  const prNum = Number(pull?.number);
  const title = String(pull?.title ?? '');
  const body = String(pull?.body ?? '');
  const text = `${title}\n${body}`;
  const ref = String(pull?.head?.ref ?? '');
  const closes = new Set();
  const partOf = new Set();

  for (const match of text.matchAll(/\b(?:close[sd]?|fix(?:e[sd])?|resolve[sd]?)\s+#([1-9]\d*)\b/gi)) {
    const n = Number(match[1]);
    if (Number.isSafeInteger(n) && n !== prNum) closes.add(n);
  }
  const coreBranch = /^pdd\/core-([1-9]\d*)-/i.exec(ref);
  if (coreBranch) {
    const n = Number(coreBranch[1]);
    if (Number.isSafeInteger(n) && n !== prNum) closes.add(n);
  }
  for (const match of text.matchAll(/\b(?:part of|refs?)\s+#([1-9]\d*)\b/gi)) {
    const n = Number(match[1]);
    if (Number.isSafeInteger(n) && n !== prNum && !closes.has(n)) partOf.add(n);
  }
  const workflowBranch = /^(?:pdd|feat|fix|bug|small-change)\/(?:issue-)?([1-9]\d*)(?:-|$)/i.exec(ref);
  if (workflowBranch) {
    const n = Number(workflowBranch[1]);
    if (Number.isSafeInteger(n) && n !== prNum && !closes.has(n)) partOf.add(n);
  }

  const isPromptPr = closes.size === 0 && partOf.size > 0 && !/PR 2 of this run:\s*the code/i.test(body) && (
    /<!--\s*pdd[-:]workflow:[^>]*prompt/i.test(body)
    || /\bPR\s*1\b|\bprompt(?:\s+and\s+tests|\s+PR)\b/i.test(text)
    || (/Made with `pdd workflow run (?:feature|bug)`/i.test(body) && /\bPart of\s+#[1-9]\d*\b/i.test(body))
  );

  if (isPromptPr) {
    return { codeIssues: [], promptIssues: [...partOf] };
  }
  return { codeIssues: [...new Set([...closes, ...partOf])], promptIssues: [] };
}

function emitReceiptEvents({ facts, idPrefix, repo, issue, at, observedAt, pr = null, head = null, evidence = undefined, meta }) {
  const common = {
    ...(Number.isSafeInteger(pr) && pr > 0 ? { pr } : {}),
    ...(validSha(head) ? { head } : {}),
    ...(evidence ? { evidence } : {}),
  };
  if (meta.skill && SKILL_NAMES.has(meta.skill)) {
    facts.push({ schema: 'pdd.metrics.event.v1', id: `${idPrefix}:skill:${issue}`, repo, issue, type: 'milestone', at, observedAt, source: `github:${repo}`, data: { stage: 'skill', reason: meta.skill, ...(common.pr ? { pr: common.pr } : {}) } });
  }
  if (meta.wouldMerge) {
    facts.push({ schema: 'pdd.metrics.event.v1', id: `${idPrefix}:wm:${issue}`, repo, issue, type: 'milestone', at, observedAt, source: `github:${repo}`, data: { stage: 'would-merge', ...common } });
  }
  for (const key of ['runtime', 'vectors', 'formal', 'complete']) {
    const status = meta.checks[key];
    if (!status) continue;
    facts.push({ schema: 'pdd.metrics.event.v1', id: `${idPrefix}:receipt-${key}:${issue}`, repo, issue, type: 'milestone', at, observedAt, source: `github:${repo}`, data: { stage: `receipt-${key}`, status, ...(common.pr ? { pr: common.pr } : {}), ...(common.head ? { head: common.head } : {}) } });
  }
}

function createTrustChecker({ repo, trusted, read }) {
  const lowerTrusted = new Set(trusted.map(x => String(x).toLowerCase()));
  const cache = new Map();
  return async ({ login, association } = {}) => {
    const name = typeof login === 'string' ? login.trim() : '';
    const lower = name.toLowerCase();
    if (association === 'OWNER' || (lower && lowerTrusted.has(lower))) return true;
    if (!name || !/^[a-z0-9](?:[a-z0-9-]{0,37}[a-z0-9])?$/i.test(name)) return false;
    if (association != null && !['MEMBER', 'COLLABORATOR'].includes(association)) return false;
    if (cache.has(lower)) return cache.get(lower);
    let ok = false;
    try {
      const permission = JSON.parse(await read(`repos/${repo}/collaborators/${name}/permission`));
      ok = ['write', 'maintain', 'admin'].includes(permission?.permission);
    } catch { ok = false; }
    cache.set(lower, ok);
    return ok;
  };
}

// Discover PRs, labels, workflow/Autopilot issue notes, skills, check receipts and would-merge across all trusted repository users.
export async function githubAllUserReceipts({ repo, observedAt, trusted = [], exec = execFile, isTrusted: suppliedTrust = null }) {
  const readSingle = async path => (await exec('gh', ['api', path], { maxBuffer: 16 * 1024 * 1024 })).stdout;
  const readPaged = async path => (await exec('gh', ['api', '--paginate', path], { maxBuffer: 16 * 1024 * 1024 })).stdout;
  const isTrusted = suppliedTrust ?? createTrustChecker({ repo, trusted, read: readPaged });

  const facts = [];
  const discoveredPulls = new Map();
  const mappings = new Map();
  const codeMappings = new Set();
  const issuesWithPr = new Set();

  try {
    const pullsRaw = await readSingle(`repos/${repo}/pulls?state=all&sort=updated&direction=desc&per_page=100`);
    for (const pull of parseJsonList(pullsRaw)) {
      if (!pull || !Number.isSafeInteger(pull.number) || pull.number < 1) continue;
      if (!pull.html_url && !pull.head?.sha && !pull.title && !pull.body) continue;
      const authorTrusted = Boolean(pull.merged_at) || await isTrusted({ login: pull.user?.login, association: pull.author_association });
      if (!authorTrusted) continue;

      const { codeIssues, promptIssues } = extractPrIssueLinks(pull);
      const linkedIssues = [...codeIssues, ...promptIssues];
      if (!linkedIssues.length) continue;

      discoveredPulls.set(pull.number, pull);
      const prAt = safeIso(pull.created_at || pull.updated_at || pull.merged_at, observedAt);
      const prHead = validSha(pull.head?.sha) ? pull.head.sha : undefined;
      const prEvidence = cleanEvidence(pull.html_url);
      const meta = parseReceiptMetadata(`${pull.title ?? ''}\n${pull.body ?? ''}`, pull.labels);
      if (!meta.skill && /^pdd\/small-change-/i.test(pull.head?.ref ?? '')) meta.skill = 'small-change';

      for (const issue of codeIssues) {
        issuesWithPr.add(issue);
        codeMappings.add(`${pull.number}:${issue}`);
        const set = mappings.get(pull.number) ?? new Set();
        set.add(issue);
        mappings.set(pull.number, set);
        facts.push({
          schema: 'pdd.metrics.event.v1',
          id: `gh-pr:${pull.number}:${issue}`,
          repo,
          issue,
          type: 'milestone',
          at: prAt,
          observedAt,
          source: `github:${repo}`,
          data: { stage: 'code-pr', pr: pull.number, ...(prHead ? { head: prHead } : {}), ...(prEvidence ? { evidence: prEvidence } : {}) },
        });
        emitReceiptEvents({ facts, idPrefix: `gh-pr:${pull.number}`, repo, issue, at: safeIso(pull.updated_at || pull.merged_at || pull.created_at, observedAt), observedAt, pr: pull.number, head: prHead, evidence: prEvidence, meta });
      }
      for (const issue of promptIssues) {
        issuesWithPr.add(issue);
        const set = mappings.get(pull.number) ?? new Set();
        set.add(issue);
        mappings.set(pull.number, set);
        facts.push({
          schema: 'pdd.metrics.event.v1',
          id: `gh-prompt-pr:${pull.number}:${issue}`,
          repo,
          issue,
          type: 'milestone',
          at: prAt,
          observedAt,
          source: `github:${repo}`,
          data: { stage: 'prompt-pr', pr: pull.number, ...(prHead ? { head: prHead } : {}), ...(prEvidence ? { evidence: prEvidence } : {}) },
        });
        emitReceiptEvents({ facts, idPrefix: `gh-prompt-pr:${pull.number}`, repo, issue, at: safeIso(pull.updated_at || pull.created_at, observedAt), observedAt, pr: pull.number, head: prHead, evidence: prEvidence, meta });
      }
    }
  } catch { /* Optional all-PR list endpoint unavailable on partial mock or restricted token. */ }

  try {
    const issuesRaw = await readSingle(`repos/${repo}/issues?state=all&sort=updated&direction=desc&per_page=100`);
    for (const row of parseJsonList(issuesRaw)) {
      if (!row || row.pull_request != null || !Number.isSafeInteger(row.number) || row.number < 1) continue;
      if (!row.html_url && !row.state && !Array.isArray(row.labels)) continue;
      const issue = row.number;
      const labelNames = (Array.isArray(row.labels) ? row.labels : [])
        .map(l => (typeof l === 'string' ? l : String(l?.name ?? '')).trim().toLowerCase())
        .filter(Boolean);
      const hasPddLabel = labelNames.some(n => n.startsWith('pdd:') || SKILL_NAMES.has(n));
      const issueMeta = parseReceiptMetadata('', row.labels);
      const rowAt = safeIso(row.updated_at || row.created_at, observedAt);
      const rowEvidence = cleanEvidence(row.html_url);

      if (hasPddLabel && (issuesWithPr.has(issue) || labelNames.some(n => n.startsWith('pdd:')))) {
        const noteReason = labelNames.includes('pdd:would-merge') ? 'would-merge'
          : labelNames.includes('pdd:needs-decision') ? 'needs-decision'
          : labelNames.includes('pdd:working') ? 'working'
          : 'observed';
        facts.push({
          schema: 'pdd.metrics.event.v1',
          id: `gh-issue:${issue}:${noteReason}`,
          repo,
          issue,
          type: 'milestone',
          at: rowAt,
          observedAt,
          source: `github:${repo}`,
          data: { stage: 'autopilot-note', reason: noteReason, ...(rowEvidence ? { evidence: rowEvidence } : {}) },
        });
        emitReceiptEvents({ facts, idPrefix: `gh-issue:${issue}`, repo, issue, at: rowAt, observedAt, evidence: rowEvidence, meta: issueMeta });
      }

      if (Number(row.comments) > 0 && (!issuesWithPr.has(issue) || hasPddLabel)) {
        try {
          const { stdout: cText } = await exec('gh', ['api', '--paginate', `repos/${repo}/issues/${issue}/comments?per_page=100`, '--jq', '.[] | {id,body,html_url,created_at,author_association,user}'], { maxBuffer: 16 * 1024 * 1024 });
          for (const comment of parseJsonList(cText)) {
            if (!comment || !comment.id || !(await isTrusted({ login: comment.user?.login, association: comment.author_association }))) continue;
            const cBody = String(comment.body ?? '');
            const autopilotTag = /<!--\s*pdd:autopilot-core:(merge|would-merge|end|question|review):/i.exec(cBody)?.[1]?.toLowerCase() ?? null;
            const cMeta = parseReceiptMetadata(cBody, []);
            const hasStructuredPdd = Boolean(autopilotTag || cMeta.skill || cMeta.wouldMerge || Object.values(cMeta.checks).some(Boolean));
            if (!hasStructuredPdd) continue;
            const cAt = safeIso(comment.created_at, rowAt);
            const cEvidence = cleanEvidence(comment.html_url);
            facts.push({
              schema: 'pdd.metrics.event.v1',
              id: `gh-issue-comment:${comment.id}:${issue}`,
              repo,
              issue,
              type: 'milestone',
              at: cAt,
              observedAt,
              source: `github:${repo}`,
              data: { stage: 'autopilot-note', reason: autopilotTag || 'receipt', ...(cEvidence ? { evidence: cEvidence } : {}) },
            });
            emitReceiptEvents({ facts, idPrefix: `gh-issue-comment:${comment.id}`, repo, issue, at: cAt, observedAt, evidence: cEvidence, meta: { ...cMeta, skill: cMeta.skill ?? issueMeta.skill } });
          }
        } catch { /* Ignore unreadable issue comments. */ }
      }
    }
  } catch { /* Optional all-issues list endpoint unavailable on partial mock or restricted token. */ }

  return { facts, mappings, codeMappings, discoveredPulls };
}

async function githubFacts({repo, observedAt, events, cwd}) {
  let trusted = [];
  try { const config = JSON.parse(await readFile(join(cwd,'pdd.json'),'utf8')); trusted = Array.isArray(config.autopilot?.trust) ? config.autopilot.trust.filter(x => typeof x === 'string').map(x => x.toLowerCase()) : []; } catch { /* No explicit trusted people. */ }
  const read = async path => (await execFile('gh',['api','--paginate',path],{maxBuffer:16*1024*1024})).stdout;
  const isTrusted = createTrustChecker({ repo, trusted, read });

  const mappings = new Map(), codeMappings = new Set();
  for (const e of events) if (e.type === 'milestone' && e.data?.pr) {
    if (e.data.stage === 'code-pr' || e.data.stage === 'implementation-ready') codeMappings.add(`${e.data.pr}:${e.issue}`);
    const issues = mappings.get(e.data.pr) ?? new Set(); issues.add(e.issue); mappings.set(e.data.pr,issues);
  }

  const discovered = await githubAllUserReceipts({ repo, observedAt, trusted, exec: execFile, isTrusted });
  const facts = [...discovered.facts];
  for (const [pr, issues] of discovered.mappings) {
    const set = mappings.get(pr) ?? new Set();
    for (const issue of issues) set.add(issue);
    mappings.set(pr, set);
  }
  for (const codeKey of discovered.codeMappings) codeMappings.add(codeKey);

  for (const [pr,issues] of mappings) {
    try {
    let pull;
    try {
      const fetched = JSON.parse(await read(`repos/${repo}/pulls/${pr}`));
      const prior = discovered.discoveredPulls.get(pr);
      pull = prior && !fetched.head?.sha && !fetched.merged_at ? prior : { ...(prior ?? {}), ...fetched };
    } catch (err) {
      if (discovered.discoveredPulls.has(pr)) pull = discovered.discoveredPulls.get(pr);
      else throw err;
    }
    const pullEvidence = cleanEvidence(pull.html_url);
    if (pull.merged_at && pullEvidence && validSha(pull.head?.sha)) for (const issue of issues) if (codeMappings.has(`${pr}:${issue}`)) facts.push({schema:'pdd.metrics.event.v1',id:`merge:${pr}:${issue}`,repo,issue,type:'delivery',at:iso(pull.merged_at),observedAt,source:`github:${repo}`,data:{pr,head:pull.head.sha,explicit:true,evidence:pullEvidence}});
    if (validSha(pull.head?.sha)) for (const issue of issues) if (codeMappings.has(`${pr}:${issue}`)) facts.push({schema:'pdd.metrics.event.v1',id:`head:${pr}:${pull.head.sha}:${observedAt}:${issue}`,repo,issue,type:'milestone',at:observedAt,observedAt,source:`github:${repo}`,data:{stage:'candidate-head',pr,head:pull.head.sha}});
    if (pull.body || pull.title || Array.isArray(pull.labels)) {
      const prMeta = parseReceiptMetadata(`${pull.title ?? ''}\n${pull.body ?? ''}`, pull.labels);
      const prMetaAt = safeIso(pull.updated_at || pull.merged_at || pull.created_at, observedAt);
      for (const issue of issues) emitReceiptEvents({ facts, idPrefix: `pull:${pr}`, repo, issue, at: prMetaAt, observedAt, pr, head: pull.head?.sha, evidence: pullEvidence, meta: prMeta });
    }
    const {stdout: text} = await execFile('gh',['api','--paginate',`repos/${repo}/issues/${pr}/comments?per_page=100`,'--jq','.[] | {id,body,html_url,created_at,author_association,user}'],{maxBuffer:16*1024*1024});
    const comments = parseJsonList(text);
    const checks = [], allowed = new Set();
    for (const comment of comments) {
      if (await isTrusted({ login: comment.user?.login, association: comment.author_association })) allowed.add(comment);
    }
    for (const comment of comments.filter(comment => allowed.has(comment))) {
      const commentBody = String(comment.body ?? '');
      const commentMeta = parseReceiptMetadata(commentBody, []);
      if (comment.id && (commentMeta.skill || commentMeta.wouldMerge || Object.values(commentMeta.checks).some(Boolean))) {
        const cAt = safeIso(comment.created_at, observedAt);
        const cEvidence = cleanEvidence(comment.html_url);
        for (const issue of issues) emitReceiptEvents({ facts, idPrefix: `pr-comment:${comment.id}`, repo, issue, at: cAt, observedAt, pr, head: pull.head?.sha, evidence: cEvidence, meta: commentMeta });
      }
      for (const block of commentBody.matchAll(/```(?:json)?\s*([\s\S]*?)```/g)) {
        let check; try {check = JSON.parse(block[1]);} catch {continue;}
        if (!['PASS','FAIL','NOT SURE'].includes(check.verdict) || !/^[a-f0-9]{40}$/i.test(check.head ?? '') || !Number.isInteger(check.risk) || check.risk < 1 || check.risk > 5 || !/^[a-z0-9_-]+$/i.test(check.family ?? '') || !checkerSession(check.session) || !['same-family','different-family'].includes(check.checker_mode) || !substantiveEvidence(check.evidence) || !comment.html_url || !comment.created_at) continue;
        checks.push({check,comment,isTrusted:true});
      }
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
      const observations = runs?.length ? runs.map(run => ({key:String(run.id ?? createHash('sha256').update(String(run.name ?? '') + '\0' + String(run.html_url ?? '')).digest('hex')), status: run.status === 'completed' ? (run.conclusion === 'success' ? 'passed' : ['failure','timed_out','action_required','startup_failure'].includes(run.conclusion) ? 'failed' : 'unknown') : 'unknown', evidence: cleanEvidence(run.html_url), reason: run.name})) : [{key:'none',status: runs ? 'missing' : 'unknown'}];
      for (const observation of observations) for (const issue of issues) facts.push({schema:'pdd.metrics.event.v1',id:`ci:${pr}:${pull.head.sha}:${observation.key}:${issue}:${observation.status}`,repo,issue,type:'ci',at:observedAt,observedAt,source:`github:${repo}`,data:{pr,head:pull.head.sha,...Object.fromEntries(Object.entries(observation).filter(([k,v]) => k !== 'key' && v !== undefined))}});
    }
    const patchId = head => {
      const diff = spawnSync('git',['show','--format=','--binary',head],{cwd,maxBuffer:32*1024*1024});
      if (diff.status !== 0 || !diff.stdout.length) return null;
      const patch = spawnSync('git',['patch-id','--stable'],{cwd,input:diff.stdout});
      return patch.status === 0 ? String(patch.stdout).trim().split(/\s+/)[0] || null : null;
    };
    for (const {check,comment,isTrusted: checkTrusted} of checks) {
      const secondNeeded = check.risk >= 4 || split || sensitive === true;
      const second = current.some(x => x !== undefined && x.check !== check && x.check.verdict === check.verdict && x.check.session !== check.session && (x.check.family.toLowerCase() !== check.family.toLowerCase() || (x.check.checker_mode === 'same-family' && check.checker_mode === 'same-family')));
      const accepted = checkTrusted && check.head === pull.head?.sha && sensitive !== null && (!secondNeeded || second);
      const commentEvidence = cleanEvidence(comment.html_url);
      if (!commentEvidence) continue;
      for (const issue of issues) facts.push({schema:'pdd.metrics.event.v1',id:`check:${comment.id}:${issue}`,repo,issue,type:'check',at:iso(comment.created_at),observedAt,source:`github:${repo}`,data:{pr,head:check.head,verdict:check.verdict,reviewer:reviewer(check),checkerFamily:check.family,checkerMode:check.checker_mode,evidence:commentEvidence,acceptance:accepted ? 'accepted' : 'unknown'}});
      if (checkTrusted && check.verdict === 'PASS' && check.head !== pull.head?.sha && suiteGreen && sensitive === false && check.risk < 4 && !split) {
        const oldId = patchId(check.head), newId = patchId(pull.head.sha);
        if (oldId && oldId === newId) for (const issue of issues) facts.push({schema:'pdd.metrics.event.v1',id:`equivalent:${comment.id}:${pull.head.sha}:${issue}`,repo,issue,type:'check',at:observedAt,observedAt,source:`github:${repo}`,data:{pr,head:pull.head.sha,verdict:'PASS',reviewer:reviewer(check),checkerFamily:check.family,checkerMode:check.checker_mode,evidence:commentEvidence,acceptance:'equivalent'}});
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
  if (report.bySkill) {
    lines.push('Skill | Issues | M/WM (Conv%) | PR | Runs | Runtime | Vectors | Formal | Complete');
    const fmtConv = row => `${row.merged}/${row.wouldMerge} (${row.conversionPct == null ? 'n/a' : `${Number(row.conversionPct.toFixed(1))}%`})`;
    const fmtCheck = c => `${c.done}/${c.applies}${c.unknown ? ` (?${c.unknown})` : ''}`;
    for (const skill of ['small-change', 'bug', 'feature', 'no-behavior-change', 'all']) {
      const row = report.bySkill[skill];
      if (!row) continue;
      lines.push(`${skill} | ${row.issues} | ${fmtConv(row)} | ${row.pr} | ${row.runs} | ${fmtCheck(row.checks.runtime)} | ${fmtCheck(row.checks.vectors)} | ${fmtCheck(row.checks.formal)} | ${fmtCheck(row.checks.complete)}`);
    }
  }
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

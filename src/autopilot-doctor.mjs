// Source: prompts/cli/autopilot-doctor.prompt.md.
import * as nativeFiles from 'node:fs';
import {constants} from 'node:fs';
import {join, resolve, delimiter} from 'node:path';
import {runAgentProcess, parseAgentAuthStatus} from './agent-adapters.mjs';
import {loadAgentDefinitions} from './agent-config.mjs';
import {readCodexLimits} from './codex-limits.mjs';
import {checkWorkflowAgents} from './workflow-agents.mjs';
import {githubOriginRepository} from './workflow-worktree.mjs';
import {runtimeOrigin} from './runtime-client.mjs';

const quote = value => `'${String(value).replaceAll("'", "'\\''")}'`;
const clean = value => String(value).replace(/[\x00-\x1f\x7f-\x9f]/g, ' ');
const skills = ['pdd-prompting','pdd-setup','pdd-small-change','pdd-bug','pdd-feature','pdd-product','pdd-graph','pdd-autopilot','pdd-check','pdd-merge'];
const ready = value => value?.code === 0;

export async function runAutopilotDoctor(input, ports = {}) {
  const env = input.env ?? ports.env ?? process.env, files = ports.files ?? nativeFiles;
  const platform = ports.platform ?? process.platform, node = ports.nodeVersion ?? process.versions.node;
  const uid = ports.uid ?? process.getuid?.();
  let cwd = input.cwd;
  const run = async (command, args) => {
    try { return await (ports.run ?? runAgentProcess)(command, args, {cwd, env, timeoutMs:10000, maxBytes:1024*1024}); }
    catch { return {code:1, stdout:'', stderr:''}; }
  };
  const read = path => { try { return files.readFileSync(path, 'utf8'); } catch { return null; } };
  const json = text => { try { return JSON.parse(text); } catch { return null; } };
  const same = (a,b) => { try { return files.realpathSync(a) === files.realpathSync(b); } catch { return false; } };
  const executable = path => { try { files.accessSync(path, constants.X_OK); return files.statSync(path).isFile(); } catch { return false; } };
  const checks = [];
  const add = (id,status,detail,fix) => checks.push({id,status,detail:clean(detail),fix});
  const retry = `${quote(ports.nodePath ?? process.execPath)} ${quote(join(input.packageRoot,'bin/pdd.mjs'))} autopilot doctor`;
  const install = name => platform === 'darwin' ? `brew install ${name}` : `sudo apt-get install ${name}`;
  const selected = (env.PATH ?? '').split(delimiter).map(dir => resolve(cwd,dir || '.', 'pdd')).find(executable);
  const pathVersion = selected ? await run(selected,['--version']) : null;
  const pathHelp = selected ? await run(selected,['autopilot','--help']) : null;
  const correct = selected && same(selected,join(input.packageRoot,'bin/pdd.mjs')) && ready(pathHelp) && /autopilot/.test(pathHelp.stdout);
  // Only accept a version-shaped value, never arbitrary stdout from another CLI.
  const version = String(pathVersion?.stdout ?? '').trim().match(/^\d+\.\d+\.\d+(?:[-+][\w.-]+)?$/)?.[0] ?? 'unknown';
  add('path',correct?'pass':'fail',selected?`${selected} (${version}); ${correct?'this install has Autopilot':'PATH must select this install with Autopilot'}`:'pdd missing on PATH',correct?'pdd autopilot doctor':`npm install -g ${quote(input.packageRoot)} && export PATH="$(npm prefix -g)/bin:$PATH" && hash -r && ${retry}`);
  const parts = node.split('.').map(Number);
  add('node',parts[0]>22 || parts[0]===22 && (parts[1]>20 || parts[1]===20 && parts[2]>=0)?'pass':'fail',`Node ${node}; requires 22.20.0 or newer`,'nvm install 22.20.0 && nvm use 22.20.0');
  add('git',ready(await run('git',['--version']))?'pass':'fail','Git installation',install('git'));
  const root = await run('git',['rev-parse','--show-toplevel']);
  if (ready(root) && root.stdout.trim()) cwd = root.stdout.trim();
  add('repository',ready(root)&&Boolean(root.stdout.trim())?'pass':'fail','Git working repository','git clone https://github.com/OWNER/REPO.git');
  add('github-cli',ready(await run('gh',['--version']))?'pass':'fail','GitHub CLI installation',install('gh'));
  const auth = await run('gh',['auth','status']);
  add('github-auth',ready(auth)?'pass':'fail','GitHub CLI sign-in','gh auth login');
  const metadataReply = await run('gh',['repo','view','--json','nameWithOwner,defaultBranchRef,viewerPermission,mergeCommitAllowed,squashMergeAllowed,rebaseMergeAllowed']);
  const metadata = ready(metadataReply) ? json(metadataReply.stdout) : null;
  const repo = metadata?.nameWithOwner, branch = metadata?.defaultBranchRef?.name;
  const named = typeof repo === 'string' && /^[\w.-]+\/[\w.-]+$/.test(repo);
  const origin = await run('git',['remote','get-url','origin']);
  const originRepo = githubOriginRepository(origin.stdout);
  const write = ['ADMIN','MAINTAIN','WRITE'].includes(metadata?.viewerPermission);
  add('github-permission',named && originRepo?.toLowerCase()===repo.toLowerCase() && write ? 'pass':'fail',`${named?repo:'repository unavailable'}; permission ${['ADMIN','MAINTAIN','WRITE','TRIAGE','READ'].includes(metadata?.viewerPermission)?metadata.viewerPermission:'unknown'}; push and PR need write access`,named?`gh repo fork ${quote(repo)} --clone`:'gh auth setup-git');
  const merge = [metadata?.mergeCommitAllowed,metadata?.squashMergeAllowed,metadata?.rebaseMergeAllowed].includes(true);
  add('merge-method',merge?'pass':'fail','Repository must enable a merge method; permission alone does not bypass reviews',named?`gh repo view ${quote(repo)} --web`:'gh auth login');
  const ruleReply = named && branch ? await run('gh',['api',`repos/${repo}/rules/branches/${encodeURIComponent(branch)}`]) : null;
  const rules = ready(ruleReply)?json(ruleReply.stdout):null;
  add('merge-rules',Array.isArray(rules)?'pass':'warn',Array.isArray(rules)?`Branch rules: ${rules.map(r=>r.type).filter(x=>typeof x==='string').join(', ') || 'none'}; required reviews and checks still apply`:'Branch rules unavailable; merge eligibility is unproved',named&&branch?`gh api ${quote(`repos/${repo}/rules/branches/${encodeURIComponent(branch)}`)}`:'gh repo view --web');

  let definitions = [], agent = null, installed = [];
  try { definitions = await (ports.agentDefinitions ?? loadAgentDefinitions)({cwd,env}); } catch { /* report account failure */ }
  const current = env.CODEX_THREAD_ID?'codex':env.CLAUDECODE?'claude':null;
  definitions = [...(Array.isArray(definitions)?definitions:[]),{id:'agy',kind:'agy',command:'agy',env:{}}];
  const rank = def => def.kind===current?-1:['codex','claude','agy','gemini'].indexOf(def.kind);
  definitions = definitions.map((def,index)=>({def,index})).sort((a,b)=>rank(a.def)-rank(b.def)||a.index-b.index).map(x=>x.def);
  if (ports.selectAgent) { try { agent = await ports.selectAgent({cwd}, {...ports,env}); } catch {} }
  else for (const def of definitions) {
    if (def.kind==='agy') {
      try {
        const result = await checkWorkflowAgents({cwd,env,requested:'agy'},{run:(_file,args,opts)=>(ports.run??runAgentProcess)(def.command,args,opts)});
        if (result.ok) { agent=def; break; }
      } catch {}
      continue;
    }
    if (def.kind==='gemini') {
      const childEnv={...env,...def.env};
      const info=await run(def.command,['--version']);
      const credentials=json(read(join(childEnv.GEMINI_CLI_HOME||childEnv.HOME||'','.gemini','oauth_creds.json')));
      if (ready(info)&&typeof credentials?.refresh_token==='string'&&credentials.refresh_token) { agent=def; break; }
      continue;
    }
    if (!['codex','claude'].includes(def.kind)) continue;
    let status;
    try { status = await (ports.run ?? runAgentProcess)(def.command,def.kind==='codex'?['login','status']:['auth','status','--json'],{cwd,env:{...env,...def.env},timeoutMs:10000,maxBytes:16384}); } catch { continue; }
    installed.push(def);
    if (parseAgentAuthStatus({agent:def.kind,result:status})==='ready') { agent = def; break; }
  }
  const preferred = installed[0] ?? definitions[0];
  const login = preferred?.kind==='claude'?`${quote(preferred.command)} auth login`:`${quote(preferred?.command ?? 'codex')} login`;
  add('agent',agent?'pass':'fail',agent?`${agent.kind} signed in`:'Agent sign-in missing or unavailable',agent?`${quote(agent.command ?? agent.kind)} ${agent.kind==='claude'?'auth status --json':'login status'}`:installed.length?login:'npm install -g @openai/codex');
  if (!agent && !installed.length) add('agent-signin','fail','Sign in after installing Codex, or install Claude Code and sign in',login);
  let usage = {state:'unknown'};
  if (agent?.kind==='codex') { try { usage = await (ports.codexLimits ?? readCodexLimits)({command:agent.command??'codex',cwd,env:{...env,...agent.env}}, {spawn:ports.spawn}); } catch {} }
  add('agent-usage',usage.state==='limited'?'fail':usage.state==='healthy'?'pass':'warn',usage.state==='limited'?'Agent usage limit reached; retry after allowance is available':usage.state==='healthy'?'Read-only usage check healthy':`${agent?.kind ?? 'Agent'} usage is unproved${agent?.kind==='claude'?'; run /usage in Claude Code':''}`,agent?.kind==='claude'?'claude':retry);

  const herdr = await run('herdr',['--version']);
  add('herdr',ready(herdr)?'pass':'fail','Herdr installation','curl -fsSL https://herdr.dev/install.sh | sh');
  const herdrRead = args => run('herdr',['--session','pdd',...args]);
  const serverReply = await herdrRead(['status','server','--json']);
  const server = ready(serverReply)?json(serverReply.stdout):null;
  let count = server?.running===false?0:null;
  if (server?.running===true) {
    const reply = await herdrRead(['pane','list','--json']);
    const panes = ready(reply)?json(reply.stdout)?.result?.panes:null;
    if (Array.isArray(panes)) count = panes.length;
  }
  const budget = env.PDD_HERDR_PANE_BUDGET===undefined?56:/^\d+$/.test(env.PDD_HERDR_PANE_BUDGET)?Number(env.PDD_HERDR_PANE_BUDGET):NaN;
  const room = count!==null && Number.isSafeInteger(budget) && budget>=0 && (budget===0 || count+1<=budget);
  add('herdr-room',room?'pass':'fail',`${count??'unknown'} panes; budget ${Number.isSafeInteger(budget)?budget:'invalid'}; needs 1`,Number.isSafeInteger(budget)?'pdd workflow tidy --dry-run && pdd workflow tidy':'unset PDD_HERDR_PANE_BUDGET');

  const block = ['CLAUDE.md','AGENTS.md'].some(name=>/<!-- pdd:start -->[\s\S]*<!-- pdd:end -->/.test(read(join(cwd,name))??''));
  add('setup-block',block?'pass':'fail','PDD instructions in AGENTS.md or CLAUDE.md','pdd setup');
  const kind = agent?.kind ?? preferred?.kind ?? 'codex';
  const roots = kind==='claude'?[join(cwd,'.claude','skills'),join(env.CLAUDE_CONFIG_DIR??join(env.HOME??'','.claude'),'skills')]:[join(cwd,'.agents','skills'),join(env.HOME??'','.agents','skills')];
  const complete = roots.some(root=>skills.every(skill=>read(join(root,skill,'SKILL.md'))!==null));
  add('setup-skills',complete?'pass':'fail',`${kind} PDD skill bundle`,'npx skills add promptdriven/pdd -g');
  const config = json(read(join(cwd,'pdd.json'))), auto = config?.autopilot;
  const valid = auto && ['auto','observe'].includes(auto.mode) && (auto.trust===undefined || Array.isArray(auto.trust)&&auto.trust.every(x=>typeof x==='string'&&x.trim()));
  add('setup-mode',valid?'pass':'fail',valid?`${auto.mode==='auto'?'auto authorizes eligible branches, PRs and merges':'observe reports work without automatic merges'}; owner and write-access users are trusted; explicit trust: ${(auto.trust??[]).join(', ')||'none'}; ${config.strict_approvals===true?'strict person-terminal approvals required':'delegated ordinary gates allowed; required human reviews still apply'}`:'Choose mode and trust in pdd setup; off does not start work','pdd setup');
  const tracked = await run('git',['ls-files','-z','--','*.prompt.md']);
  const drafts = [], unreadable = [];
  for (const path of ready(tracked)?tracked.stdout.split('\0').filter(Boolean):[]) {
    const text = read(join(cwd,path));
    if (text===null) { unreadable.push(path); continue; }
    const block = text.match(/<summary>Runtime interface<\/summary>[\s\S]*?```json\s*([\s\S]*?)```/i);
    const data = block?json(block[1]):null;
    if (!data || data.status!=='approved') drafts.push(path);
  }
  add('draft-prompts',!ready(tracked)||drafts.length||unreadable.length?'warn':'pass',`First check may need prompt approval: ${drafts.join(', ')||'none'}${unreadable.length?`; unreadable: ${unreadable.join(', ')}`:''}`,'pdd files --json');

  let health;
  try {
    if (ports.runtimeHealth) health = await ports.runtimeHealth({env});
    else {
      const token = await run('gh',['auth','token']);
      if (!ready(token)||!token.stdout.trim()) health = {state:'auth'};
      else {
        const reply = await (ports.fetch??globalThis.fetch)(`${runtimeOrigin(env)}/v1/capacity`,{method:'GET',headers:{Authorization:`Bearer ${token.stdout.trim()}`},signal:AbortSignal.timeout(10000),redirect:'error'});
        const body = await reply.json();
        health = {state:reply.status===200 && body && typeof body==='object' && !Array.isArray(body) && !(Date.parse(body.maintenance?.until)>(ports.now??Date.now)())?'healthy':[401,403].includes(reply.status)?'access':'unavailable'};
      }
    }
  } catch { health = {state:'unavailable'}; }
  add('interpreter',health?.state==='healthy'?'pass':'fail',health?.state==='healthy'?'Read-only interpreter access accepted':'Interpreter access is unproved; no check was submitted',health?.state==='auth'?'gh auth login':health?.state==='access'?`${platform==='darwin'?'open':'xdg-open'} https://promptdriven.ai/login`:retry);
  if (platform==='linux') {
    add('user-timers',ready(await run('systemctl',['--user','show-environment']))?'pass':'fail','systemd user session','systemctl --user status');
    const linger = await run('loginctl',['show-user',String(uid),'--property=Linger','--value']);
    add('linger',ready(linger)&&linger.stdout.trim()==='yes'?'pass':'warn','Lingering keeps timers running after logout','loginctl enable-linger');
  } else if (platform==='darwin') {
    add('user-timers',ready(await run('launchctl',['print',`gui/${uid}`]))?'pass':'fail','launchctl user session',`launchctl print gui/${uid}`);
    const sleep = await run('pmset',['-g','custom']);
    const values = [...(sleep.stdout??'').matchAll(/^\s*sleep\s+(\d+)/gm)].map(x=>Number(x[1]));
    add('sleep',ready(sleep)&&values.length&&values.every(x=>x===0)?'pass':'warn','Sleep can pause work; keep this command running while Autopilot works','caffeinate -i');
  } else add('platform','fail','Autopilot needs Linux or macOS',retry);
  return {exitCode:checks.some(c=>c.status==='fail')?1:0,message:checks.map(c=>`${c.status.toUpperCase()} ${c.id}: ${c.detail}; fix: ${c.fix}`).join('\n'),checks};
}

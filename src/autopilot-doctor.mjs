// Generated from prompts/cli/autopilot-doctor.prompt.md (sha256: 02ad6741adbbaf851a3c13bc73fc6a466aa7330bd28d74ecd5add81239131a63).
// Source: prompts/cli/autopilot-doctor.prompt.md.
import {rememberSecrets, knownSecretValues} from './secret-redaction.mjs';
import * as nativeFiles from 'node:fs';
import {constants} from 'node:fs';
import {join, resolve, delimiter} from 'node:path';
import {runAgentProcess, parseAgentAuthStatus} from './agent-adapters.mjs';
import {loadAgentDefinitions} from './agent-config.mjs';
import {readCodexLimits} from './codex-limits.mjs';
import {checkWorkflowAgents} from './workflow-agents.mjs';
import {githubOriginRepository} from './workflow-worktree.mjs';
import './product.mjs';
import {health as runtimeHealthCheck, runtimeClientSlice} from './runtime-seam.mjs';

const {runtimeOrigin} = runtimeClientSlice();

const quote = value => `'${String(value).replaceAll("'", "'\\''")}'`;
const clean = value => String(value).replace(/[\x00-\x1f\x7f-\x9f]/g, ' ');
const skills = ['pdd-prompting','pdd-setup','pdd-small-change','pdd-bug','pdd-feature','pdd-product','pdd-graph'];
const ready = value => value?.code === 0;

// Shared with start: definition HOME selects agents.json; invocation HOME selects the account.
export async function resolveAutopilotAgent(input, ports = {}) {
  const caller = input.env ?? ports.env ?? process.env, profile = input.profile;
  const definitionEnv = profile ? {...caller, HOME:profile.definitionHome} : caller;
  if (profile) {
    const variable={codex:'CODEX_HOME',claude:'CLAUDE_CONFIG_DIR',gemini:'GEMINI_CLI_HOME'}[profile.agent.kind];
    for (const name of ['CODEX_HOME','CLAUDE_CONFIG_DIR','GEMINI_CLI_HOME']) {
      if (name===variable && profile.configHome) definitionEnv[name]=profile.configHome; else delete definitionEnv[name];
    }
  }
  const invocation = def => {
    const env = {...caller, ...def?.env};
    if (profile) {
      env.HOME = profile.home;
      const variable = {codex:'CODEX_HOME',claude:'CLAUDE_CONFIG_DIR',gemini:'GEMINI_CLI_HOME'}[profile.agent.kind];
      for (const name of ['CODEX_HOME','CLAUDE_CONFIG_DIR','GEMINI_CLI_HOME']) {
        if (name === variable && profile.configHome) env[name] = profile.configHome; else delete env[name];
      }
    }
    return env;
  };
  let definitions = [], configurationError = null, agent = null;
  const installed = [], cwd = input.cwd, files = ports.files ?? nativeFiles;
  try { definitions = await (ports.agentDefinitions ?? loadAgentDefinitions)({cwd,env:definitionEnv}); }
  catch (error) { configurationError = error; }
  for (const def of Array.isArray(definitions)?definitions:[]) rememberSecrets(...knownSecretValues(def.env));
  definitions = [...(Array.isArray(definitions)?definitions:[]),{id:'agy',kind:'agy',command:'agy',env:{}}];
  if (profile) definitions = definitions.filter(def=>def.id===profile.agent.id && def.kind===profile.agent.kind);
  const current = caller.CODEX_THREAD_ID?'codex':caller.CLAUDECODE?'claude':null;
  const rank = def => def.kind===current?-1:['codex','claude','agy','gemini'].indexOf(def.kind);
  definitions = definitions.map((def,index)=>({def,index})).sort((a,b)=>rank(a.def)-rank(b.def)||a.index-b.index).map(x=>x.def);
  if (ports.selectAgent) {
    try { agent = await ports.selectAgent({cwd}, {...ports,env:definitionEnv}); } catch {}
    if (profile && (agent?.id!==profile.agent.id || agent?.kind!==profile.agent.kind)) agent = null;
  } else for (const def of definitions) {
    const env = invocation(def), run = (args,options={})=>(ports.run??runAgentProcess)(def.command,args,{cwd,env,timeoutMs:10000,maxBytes:16384,...options});
    try {
      if (def.kind==='agy') {
        const result = await checkWorkflowAgents({cwd,env,requested:'agy'},{run:(_file,args,opts)=>run(args,opts)});
        if (result.ok) { agent=def; break; }
      } else if (def.kind==='gemini') {
        const info=await run(['--version']);
        let credentials;
        try { credentials=JSON.parse(files.readFileSync(join(env.GEMINI_CLI_HOME||env.HOME||'','.gemini','oauth_creds.json'),'utf8')); } catch {}
        rememberSecrets(...knownSecretValues(credentials));
        if (ready(info)&&typeof credentials?.refresh_token==='string'&&credentials.refresh_token) { agent=def; break; }
      } else if (['codex','claude'].includes(def.kind)) {
        const status=await run(def.kind==='codex'?['login','status']:['auth','status','--json']);
        installed.push(def);
        if (parseAgentAuthStatus({agent:def.kind,result:status})==='ready') { agent=def; break; }
      }
    } catch { /* Another provider may be ready. Never echo provider output. */ }
  }
  const preferred=installed[0] ?? definitions[0];
  return {agent,preferred,installed,env:invocation(agent??preferred),configurationError};
}

export async function runAutopilotDoctor(input, ports = {}) {
  const callerEnv = input.env ?? ports.env ?? process.env, files = ports.files ?? nativeFiles;
  const selection = await resolveAutopilotAgent({...input,env:callerEnv},ports);
  ports.onSelection?.(selection);
  const env = selection.env;
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
  rememberSecrets(...knownSecretValues(env));
  const checks = [];
  const add = (id,status,detail,fix) => checks.push({id,status:status==='fail' && !['agent','agent-signin'].includes(id)?'warn':status,detail:clean(detail),fix});
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
  const permission = named && originRepo?.toLowerCase()===repo.toLowerCase() && write;
  add('github-permission',permission ? 'pass':'fail',`${named?repo:'repository unavailable'}; permission ${['ADMIN','MAINTAIN','WRITE','TRIAGE','READ'].includes(metadata?.viewerPermission)?metadata.viewerPermission:'unknown'}; push and PR need write access`,permission?`gh repo view ${quote(repo)} --json viewerPermission`:named?`gh repo fork ${quote(repo)} --clone`:'gh auth setup-git');
  const merge = [metadata?.mergeCommitAllowed,metadata?.squashMergeAllowed,metadata?.rebaseMergeAllowed].includes(true);
  add('merge-method',merge?'pass':'fail','Repository must enable a merge method; permission alone does not bypass reviews',merge?`gh repo view ${quote(repo)} --json mergeCommitAllowed,squashMergeAllowed,rebaseMergeAllowed`:named?`gh repo edit ${quote(repo)} --enable-squash-merge`:'gh auth login');
  const ruleReply = named && branch ? await run('gh',['api',`repos/${repo}/rules/branches/${encodeURIComponent(branch)}`]) : null;
  const rules = ready(ruleReply)?json(ruleReply.stdout):null;
  add('merge-rules',Array.isArray(rules)?'pass':'warn',Array.isArray(rules)?`Branch rules: ${rules.map(r=>r.type).filter(x=>typeof x==='string').join(', ') || 'none'}; required reviews and checks still apply`:'Branch rules unavailable; merge eligibility is unproved',named&&branch?`${Array.isArray(rules)?'':'gh auth login && '}gh api ${quote(`repos/${repo}/rules/branches/${encodeURIComponent(branch)}`)}`:'gh auth login');
  // Autopilot jobs commit: Git needs a name and an email, from config or from the environment as Git reads it.
  const nonblank = value => typeof value === 'string' && value.trim() !== '';
  const configured = async key => { const reply = await run('git',['config',key]); return ready(reply) && nonblank(reply.stdout); };
  const missing = [];
  if (!(await configured('user.name')) && !(nonblank(env.GIT_AUTHOR_NAME) && nonblank(env.GIT_COMMITTER_NAME))) missing.push('user.name');
  if (!(await configured('user.email')) && !(nonblank(env.GIT_AUTHOR_EMAIL) && nonblank(env.GIT_COMMITTER_EMAIL) || nonblank(env.EMAIL))) missing.push('user.email');
  const identityFix = {'user.name':'git config --global user.name "Your Name"','user.email':'git config --global user.email "you@example.com"'};
  add('git-identity',missing.length?'warn':'pass',missing.length?`Git user.name and user.email are needed for Autopilot commits; missing: ${missing.join(', ')}`:'Git user.name and user.email are set for Autopilot commits',missing.length?missing.map(key=>identityFix[key]).join(' && '):'git config user.name && git config user.email');

  let configurationFix;
  if (selection.configurationError) {
    const path=join(input.profile?.definitionHome??callerEnv.HOME??'', '.config','pdd','agents.json');
    configurationFix=`vi ${quote(path)}`;
    add('agent-config','fail',`Cannot load agent configuration: ${path}`,configurationFix);
  }
  const {agent,preferred,installed}=selection;
  const login = `${quote(preferred?.command ?? 'codex')}${preferred?.kind==='claude'?' auth login':['agy','gemini'].includes(preferred?.kind)?'':' login'}`;
  const statusArgs={codex:'login status',claude:'auth status --json',agy:'models',gemini:'--version'};
  add('agent',agent?'pass':configurationFix?'warn':'fail',agent?`${agent.kind} signed in`:'Sign in to a configured agent; account missing or unavailable',configurationFix??(agent?`${quote(agent.command ?? agent.kind)} ${statusArgs[agent.kind]}`:installed.length?login:'npm install -g @openai/codex'));
  if (!configurationFix && !agent && !installed.length) add('agent-signin','fail','Sign in after installing Codex, or install Claude Code and sign in',login);
  let usage = {state:'unknown'};
  if (agent?.kind==='codex') { try { usage = await (ports.codexLimits ?? readCodexLimits)({command:agent.command??'codex',cwd,env}, {spawn:ports.spawn}); } catch {} }
  add('agent-usage',usage.state==='healthy'?'pass':'warn',usage.state==='limited'?'Agent usage limit reached; retry after allowance is available':usage.state==='healthy'?'Read-only usage check healthy':`${agent?.kind ?? 'Agent'} usage is unproved${agent?.kind==='claude'?'; run /usage in Claude Code':''}`,agent?.kind==='claude'?quote(agent.command??'claude'):retry);

  const block = ['CLAUDE.md','AGENTS.md'].some(name=>/<!-- pdd:start -->[\s\S]*<!-- pdd:end -->/.test(read(join(cwd,name))??''));
  add('setup-block',block?'pass':'fail','PDD instructions in AGENTS.md or CLAUDE.md','pdd setup');
  const kind = agent?.kind ?? preferred?.kind ?? 'codex';
  const roots = kind==='claude'?[join(cwd,'.claude','skills'),join(env.CLAUDE_CONFIG_DIR??join(env.HOME??'','.claude'),'skills')]:[join(cwd,'.agents','skills'),join(env.HOME??'','.agents','skills')];
  const complete = roots.some(root=>skills.every(skill=>read(join(root,skill,'SKILL.md'))!==null));
  add('setup-skills',complete?'pass':'fail',`${kind} PDD skill bundle`,'npx skills add promptdriven/pdd -g');
  const config = json(read(join(cwd,'pdd.json'))), auto = config?.autopilot;
  const valid = auto && ['auto','observe'].includes(auto.mode) && (auto.trust===undefined || Array.isArray(auto.trust)&&auto.trust.every(x=>typeof x==='string'&&x.trim()));
  add('setup-mode',valid?'pass':'fail',valid?`${auto.mode==='auto'?'auto authorizes eligible branches, PRs and merges':'observe reports work without automatic merges'}; owner and write-access users are trusted; explicit trust: ${(auto.trust??[]).join(', ')||'none'}; ${config.strict_approvals===true?'strict person-terminal approvals required':'delegated ordinary gates allowed; required human reviews still apply'}`:'Choose mode and trust in pdd setup; off does not start work','pdd setup');
  // Job worktrees and other machines read pdd.json of the default branch on GitHub.
  // The settings differ as autopilot-github defines: the mode, or the trust names ignoring case and order.
  const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
  const modeOf = value => object(value) && ['off','observe','auto'].includes(value.mode) ? value.mode : 'off';
  const namesOf = value => object(value) && Array.isArray(value.trust) ? value.trust.filter(nonblank) : [];
  const trustKey = value => [...new Set(namesOf(value).map(name=>name.toLowerCase()))].sort().join('\n');
  const settingsOf = value => `${modeOf(value)}, trust ${namesOf(value).join(', ') || '(none)'}`;
  const sameName = (a,b) => a.toLowerCase() === b.toLowerCase();
  const only = (names,other) => names.filter((name,index)=>!other.some(item=>sameName(item,name)) && names.findIndex(item=>sameName(item,name))===index);
  const word = value => /^[\w.@/-]+$/.test(value) ? value : quote(value);
  const contents = named && branch ? `repos/${repo}/contents/pdd.json?ref=${encodeURIComponent(branch)}` : null;
  const show = contents && `gh api ${quote(contents)} -H 'Accept: application/vnd.github.raw'`;
  const remoteReply = contents ? await run('gh',['api',contents]) : null;
  const absent = Boolean(remoteReply) && !ready(remoteReply) && /\(HTTP 404\)/.test(String(remoteReply.stderr ?? ''));
  const file = ready(remoteReply) ? json(remoteReply.stdout) : null;
  const remote = object(file) && file.type==='file' && file.encoding==='base64' && typeof file.content==='string' ? json(Buffer.from(file.content,'base64').toString('utf8')) : null;
  const localText = read(join(cwd,'pdd.json')), ours = auto, theirs = remote?.autopilot;
  if (!contents || !absent && !object(remote)) add('settings-github','warn','Autopilot settings on GitHub are unproved; doctor could not read pdd.json of the default branch',contents?`gh auth login && ${show}`:'gh auth login');
  else if (localText!==null && !object(config)) add('settings-github','warn','pdd.json in this checkout is not a JSON object; the GitHub comparison is unproved','vi pdd.json');
  else if (absent && localText===null) add('settings-github','warn',`pdd.json is missing in this checkout and on GitHub (${branch})`,'pdd setup');
  else if (absent) add('settings-github','warn',`pdd.json is only in this checkout; GitHub (${branch}) has none, so other machines and Autopilot job worktrees do not see it`,`git add pdd.json && git commit -m "Add PDD settings" && git push${['observe','auto'].includes(modeOf(ours))?` # or pdd autopilot ${modeOf(ours)}`:''}`);
  else if (localText===null) add('settings-github','warn',`pdd.json is only on GitHub (${branch}): ${settingsOf(theirs)}; this checkout has none`,`git fetch origin && git checkout ${word(`origin/${branch}`)} -- pdd.json`);
  else if (modeOf(theirs)!==modeOf(ours) || trustKey(theirs)!==trustKey(ours)) {
    const trust = only(namesOf(ours),namesOf(theirs)), untrust = only(namesOf(theirs),namesOf(ours));
    const publish = [...(modeOf(theirs)===modeOf(ours)?[]:[`pdd autopilot ${modeOf(ours)}`]),...(trust.length?[`pdd autopilot trust ${trust.map(word).join(' ')}`]:[]),...untrust.map(name=>`pdd autopilot untrust ${word(name)}`)];
    add('settings-github','warn',`GitHub: ${settingsOf(theirs)}; this checkout: ${settingsOf(ours)}; Autopilot jobs use the GitHub copy`,publish.join(' && '));
  } else add('settings-github','pass',`GitHub (${branch}) has the same Autopilot settings: ${settingsOf(ours)}`,show);
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
  try { runtimeOrigin(env); } catch { health={state:'address'}; }
  try {
    if (health?.state==='address') { /* Keep address guidance; do not call a health port. */ }
    else if (ports.runtimeHealth) health = await ports.runtimeHealth({env});
    else {
      const token = await run('gh',['auth','token']);
      if (ready(token)) rememberSecrets(token.stdout.trim());
      health=await runtimeHealthCheck({env},{gh:()=>({status:token.code,stdout:token.stdout}),fetch:ports.fetch,now:ports.now});
      if (!ready(token)||!token.stdout.trim()) health={...health,state:'auth'};
    }
  } catch { health = {state:'unavailable'}; }
  add('interpreter',health?.state==='healthy'?'pass':'warn',health?.state==='healthy'?'Read-only interpreter access accepted':health?.state==='address'?'PDD_RUNTIME_URL must be an HTTPS origin; unset it to use the default':'Interpreter access is unproved; no check was submitted',health?.state==='address'?`unset PDD_RUNTIME_URL; ${retry}`:health?.state==='auth'?'gh auth login':health?.state==='access'?`${platform==='darwin'?'open':'xdg-open'} https://promptdriven.ai/login`:retry);
  if (platform==='linux') {
    add('user-timers',ready(await run('systemctl',['--user','show-environment']))?'pass':'fail','systemd user session','systemctl --user status; sudo systemctl start user@$(id -u).service');
    const linger = await run('loginctl',['show-user',String(uid),'--property=Linger','--value']);
    add('linger',ready(linger)&&linger.stdout.trim()==='yes'?'pass':'warn','Lingering keeps timers running after logout','loginctl enable-linger');
  } else if (platform==='darwin') {
    add('user-timers',ready(await run('launchctl',['print',`gui/${uid}`]))?'pass':'fail','launchctl user session',`launchctl print gui/${uid}; launchctl bootstrap gui/${uid} "$HOME/Library/LaunchAgents"`);
    const sleep = await run('pmset',['-g','custom']);
    const values = [...(sleep.stdout??'').matchAll(/^\s*sleep\s+(\d+)/gm)].map(x=>Number(x[1]));
    add('sleep',ready(sleep)&&values.length&&values.every(x=>x===0)?'pass':'warn','Sleep can pause work; keep this command running while Autopilot works','caffeinate -i');
  } else add('platform','fail','Autopilot needs Linux or macOS',retry);
  // Only profile paths are literal. Other definition values may be secrets.
  const names=new Set(['HOME','PATH','CODEX_HOME','CLAUDE_CONFIG_DIR','GEMINI_CLI_HOME',...Object.keys((agent??preferred)?.env??{})]);
  const secret=name=>{
    if (/token|secret|password|passwd|credential|api_?key|private_?key|auth/i.test(name)) return true;
    if (/url$/i.test(name)) {
      try {const url=new URL(env[name]);return Boolean(url.username||url.password||url.search||url.hash);} catch {return true;}
    }
    return false;
  };
  // Bind only what differs from the caller's environment, where the person runs the fix.
  const changed=[...names].filter(name=>env[name]===undefined?callerEnv[name]!==undefined:env[name]!==callerEnv[name]);
  const unsets=changed.filter(name=>env[name]===undefined).map(name=>`-u ${name}`);
  const sets=changed.filter(name=>env[name]!==undefined).map(name=>!secret(name)?`${name}=${quote(env[name])}`:`${name}="${'${'}${name}:?Set ${name} for the selected profile}"`);
  if (changed.length) for (const check of checks) check.fix=`env ${[...unsets,...sets].join(' ')} /bin/sh -c ${quote(check.fix)}`;
  return {exitCode:checks.some(c=>c.status==='fail')?1:0,message:checks.map(c=>`${c.status.toUpperCase()} ${c.id}: ${c.detail}${c.status==='pass'?'':`; fix: ${c.fix}`}`).join('\n'),checks};
}

// Implements prompts/cli/issue-dependency-graph.prompt.md.
import { mkdirSync, readFileSync, writeFileSync, renameSync } from 'node:fs';
import { homedir } from 'node:os';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';
import { createServer } from 'node:http';
import { resolveWorkflowRepository } from './workflow-github.mjs';
import { readDependencySnapshot } from './issue-dependencies-github.mjs';
import { projectIssueGraph } from './issue-dependencies.mjs';
import { renderIssueGraph } from './issue-dependency-graph-view.mjs';
const valid = s => /^[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*$/.test(s ?? '');
const root = join(homedir(), '.cache', 'pdd', 'graph');
const file = repository => join(root, ...repository.split('/')) + '.json';
const cache = { read: async ({repository}) => { try { return {json:readFileSync(file(repository),'utf8')}; } catch { return {json:''}; } }, write: async ({repository,json}) => { const f=file(repository); mkdirSync(dirname(f),{recursive:true,mode:0o700}); const tmp=`${f}.${process.pid}.tmp`; writeFileSync(tmp,json,{mode:0o600}); renameSync(tmp,f); return {ok:true}; } };
async function repo(input) { const r = input.repository || (await resolveWorkflowRepository({cwd:input.cwd})).repository; if (!valid(r)) throw Object.assign(Error('invalid-repository'),{code:'invalid-repository'}); return r.toLowerCase(); }
const spawnJob = (action,cwd,repository,issue='') => { const child=spawn(process.execPath,[fileURLToPath(import.meta.url),action,cwd,repository,issue],{detached:true,stdio:'ignore'}); child.unref(); };
const defaults = {cache, snapshots:{read:readDependencySnapshot}, refresh:{schedule:async ({cwd,repository})=>{spawnJob('refresh',cwd,repository);return {ok:true};}}, host:{read:async()=>({headless:process.platform !== 'darwin' && process.platform !== 'win32' && !process.env.DISPLAY && !process.env.WAYLAND_DISPLAY})}};
async function saved(repository,ports) { try { const value=await (ports.cache ?? cache).read({repository}); const data=typeof value?.json === 'string' ? JSON.parse(value.json || 'null') : value; return data?.graph && data.graph.repository?.toLowerCase() === repository ? data : null; } catch { return null; } }
export async function readIssueGraph(input, ports={}) { const repository=await repo(input), data=await saved(repository,ports); await (ports.refresh ?? defaults.refresh).schedule({cwd:input.cwd,repository}); return {graph:data?.graph ?? null,sync:data?'refreshing':'empty',lastSync:data?.lastSync ?? ''}; }
export async function refreshIssueGraph(input,ports={}) { const repository=await repo(input), old=await saved(repository,ports); try { const result=await (ports.snapshots ?? defaults.snapshots).read({cwd:input.cwd,repository}); const snapshot=result.snapshot ?? result; if (snapshot.repository?.toLowerCase() !== repository) throw Error('incomplete'); if (!snapshot.complete) { let warnings=[], projected=null; try { projected=projectIssueGraph({snapshot}); const safe=/^(?:Observation unavailable: (?:issue|authority|comments|blockedBy|blocking|timeline|context|execution) |Impact discovery unavailable: )https:\/\/github\.com\/[a-z0-9_.-]+\/[a-z0-9_.-]+\/issues\/[1-9][0-9]*$/; warnings=[...new Set((projected?.nodes ?? []).flatMap(node=>node.reasons).filter(reason=>safe.test(reason) || reason==='Open issue index unavailable' || reason==='Observation coverage unavailable'))]; } catch { /* unprojectable partial observation */ } return {graph:old?.graph ?? projected,sync:old || projected?'offline':'empty',lastSync:old?.lastSync ?? '',...(warnings.length?{warnings}:{})}; } const graph=projectIssueGraph({snapshot}); const lastSync=snapshot.capturedAt; await (ports.cache ?? cache).write({repository,json:JSON.stringify({graph,lastSync})}); return {graph,sync:'current',lastSync}; } catch { return {graph:old?.graph ?? null,sync:old?'offline':'empty',lastSync:old?.lastSync ?? ''}; } }
function summary(repository,issue,view) { const g=view.graph; if (!g) return `Repository: ${repository}\nNo saved graph. Refresh requested.\n${(view.warnings ?? []).map(w => `Warning: ${w}\n`).join('')}`; const lines=[`Repository: ${repository}`,`Captured: ${g.capturedAt}; last successful sync: ${view.lastSync}; ${view.sync}`,`Review: ${g.nodes.filter(n=>n.reviewState==='current').length} current; dependencies: ${g.nodes.filter(n=>n.dependencyState==='waiting').length} waiting; execution: ${g.nodes.filter(n=>n.executionState==='running').length} running.`]; for (const warning of view.warnings ?? []) lines.push(`Warning: ${warning}`); const rootKey=issue ? `https://github.com/${repository}/issues/${issue}` : ''; const chain=new Set(rootKey?[rootKey]:[]); let changed=true; while(changed) { changed=false; for(const edge of g.edges) if(chain.has(edge.dependent) && !chain.has(edge.blocker)) {chain.add(edge.blocker);changed=true;} } const selected=issue ? g.nodes.filter(n=>chain.has(n.key)) : g.nodes; for(const n of selected) { lines.push(`${n.key} ${n.title}: ${n.dependencyState}; ${n.reviewState}; ${n.executionState}${n.eligible?' (no recorded open blocker)':''}`); for(const r of n.reasons ?? []) lines.push(`  ${r}`); for(const b of n.blockers ?? []) lines.push(`  Blocker: ${b}`); for(const e of g.edges.filter(e=>e.dependent===n.key)) lines.push(`  ${e.blocker}: ${e.reason} ${(e.evidence??[]).join(' ')}`); for(const f of n.facts??[]) lines.push(`  ${f.kind}: ${f.text} ${f.source}`); } if(issue && !selected.length) lines.push('Selected issue is absent or unknown.'); return lines.join('\n')+'\n'; }
export async function runIssueGraph(input,ports={}) { const empty={graph:null,sync:'empty',lastSync:''}; try { const repository=await repo(input); if(input.issue && !/^[1-9][0-9]*$/.test(input.issue)) throw Error('Issue must be a positive number.'); const view=await readIssueGraph({...input,repository},ports); let message=summary(repository,input.issue,view),handoff='',opened=false; if(input.open) { const host=await (ports.host ?? defaults.host).read({}); if(host.headless) { handoff=`pdd graph --open --repo ${repository}${input.issue?` --issue ${input.issue}`:''}`; message+=`On your laptop, run: ${handoff}\nThe laptop reads GitHub; unpublished VM facts may be missing.\n`; } else { const viewer=ports.viewer ?? {open: async ({repository,issue})=> startViewer(input.cwd,repository,issue)}; const result=await viewer.open({repository,issue:input.issue ?? '',graphJson:JSON.stringify(view.graph)}); opened=result.opened; message+=opened?`Viewer launcher invoked: ${result.url}\n`:`Viewer prepared but not opened: ${result.url}\n`; } } return {exitCode:0,message,handoff,opened,view}; } catch(e) { return {exitCode:1,message:`Graph unavailable: ${e.message}. Name a repository with --repo OWNER/REPO or open a chat in one.\n`,handoff:'',opened:false,view:empty}; } }
async function startViewer(cwd,repository,issue) {
  return new Promise((resolve,reject) => {
    const child=spawn(process.execPath,[fileURLToPath(import.meta.url),'serve',cwd,repository,issue],{detached:true,stdio:['ignore','ignore','ignore','ipc']});
    const timer=setTimeout(()=>{child.disconnect();reject(Error('Viewer did not start'));},5000);
    child.once('error',e=>{clearTimeout(timer);reject(e);});
    child.once('message',async ({url})=>{clearTimeout(timer);child.disconnect();child.unref(); const command=process.platform==='darwin'?'open':process.platform==='win32'?'rundll32':'xdg-open'; const args=process.platform==='win32'?['url.dll,FileProtocolHandler',url]:[url]; try { const opener=spawn(command,args,{stdio:'ignore',detached:true}); opener.once('spawn',()=>{opener.unref();resolve({opened:true,url});}); opener.once('error',()=>resolve({opened:false,url})); } catch { resolve({opened:false,url}); } });
  });
}
async function serve(cwd,repository,issue) {
  let view=await readIssueGraph({cwd,repository},{refresh:{schedule:async()=>({ok:true})}});
  let pending;
  const refresh=() => {
    if (!pending) pending=refreshIssueGraph({cwd,repository}).then(result=>{view=result;return result;}).finally(()=>{pending=null;});
    return pending;
  };
  void refresh();
  const server=createServer(async (req,res)=>{
    const host=req.headers.host, expected=`127.0.0.1:${server.address().port}`;
    if(host!==expected || (req.headers.origin && req.headers.origin!==`http://${expected}`) || req.method!=='GET') {res.writeHead(403).end();return;}
    res.setHeader('X-Content-Type-Options','nosniff');res.setHeader('Cache-Control','no-store');
    if(req.url==='/data' || req.url==='/refresh') { if(req.url==='/refresh') await refresh(); res.setHeader('Content-Type','application/json');res.end(JSON.stringify(view));return; }
    if(req.url==='/view.mjs') {res.setHeader('Content-Type','text/javascript');res.end(readFileSync(fileURLToPath(new URL('./issue-dependency-graph-view.mjs',import.meta.url))));return;}
    if(req.url!=='/') {res.writeHead(404).end();return;}
    const state={...view,repository,selected:issue?`https://github.com/${repository}/issues/${issue}`:''};
    res.setHeader('Content-Type','text/html; charset=utf-8');res.end(`<!doctype html><html><head><meta charset="utf-8"><title>PDD dependency graph</title></head><body>${renderIssueGraph(state).html}<script type="application/json" id="graph-state">${JSON.stringify(state).replace(/</g,'\\u003c')}</script><script type="module" src="/view.mjs"></script></body></html>`);
  });
  server.listen(0,'127.0.0.1',()=>process.send?.({url:`http://127.0.0.1:${server.address().port}/`}));
}
if(process.argv[1]===fileURLToPath(import.meta.url)) { const [, , action,cwd,repository,issue]=process.argv; if(action==='refresh') await refreshIssueGraph({cwd,repository}); else if(action==='serve') await serve(cwd,repository,issue); }

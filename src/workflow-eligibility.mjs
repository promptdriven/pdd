// Generated from prompts/cli/workflow-runner.prompt.md (sha256: cea27bfc382c68611970f14c504539f95bf152b6214c7f338c20f85945768480).
import { spawnSync } from 'node:child_process';
import { realpathSync } from 'node:fs';
import { createRequire } from 'node:module';
import { join } from 'node:path';
import { allRuns, runDirFor } from './workflow-runs.mjs';

const req = createRequire(import.meta.url);
let cachedSeam = null;
const seam = () => (cachedSeam ??= req('./runtime-seam.mjs'));

export const oneLine = value => String(value ?? '').replace(/\s+/g, ' ').trim();
export const canonical = value => Array.isArray(value) ? value.map(canonical) : value && typeof value === 'object'
  ? Object.fromEntries(Object.keys(value).sort().map(key => [key, canonical(value[key])])) : value;
export const sameFact = (a,b) => JSON.stringify(canonical(a ?? null)) === JSON.stringify(canonical(b ?? null));
export const prOf = (run, name) => (run.pr ?? []).find(pr => pr.stage === name) ?? null;
export const askArea = run => run.areas.find(area => area.then === 'ask-code') ?? null;
export const commitSha = value => /^(?:[a-f\d]{40}|[a-f\d]{64})$/i.test(value);

// Registration authority is independent of receipt content and source equality.
export const evidenceTests = tests => {
  if (!Array.isArray(tests) || !tests.length || tests.some(path => typeof path !== 'string' || !path || /[\\\x00-\x1f\x7f]/.test(path)
    || path.startsWith('/') || /^[A-Za-z]:/.test(path) || path.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git'))
    || new Set(tests).size !== tests.length) throw Error('Select nonempty unique safe authored-relative test paths.');
  return [...tests].sort();
};
export const selectionEqual = (a,b) => sameFact(evidenceTests(a),evidenceTests(b));
export const associationKey = a => JSON.stringify([a.workspaceRoot,evidenceTests(a.tests),a.source_sha256]);
export function ownedPr1Head(run) {
  const area = askArea(run), pr = area && prOf(run,area.name);
  if (!pr || !Number.isSafeInteger(pr.number) || pr.url !== `https://github.com/${run.repo}/pull/${pr.number}` || !commitSha(pr.publishedHeadSha))
    throw Error('The owned recorded PR 1 head is missing or unavailable.');
  return pr.publishedHeadSha;
}
export function selectedCapture(root,tests,capture,listGitFiles) {
  const readGitFiles = listGitFiles ?? (dir => seam().gitFiles(dir));
  const runCapture = capture ?? ((dir, options) => seam().captureSource(dir, options));
  const visible=new Set(readGitFiles(root));
  if(tests.some(path=>!visible.has(path)))throw Error('A selected authored source is missing or unavailable.');
  return runCapture(root,{tests,appMap:null});
}
export const ANCHOR_FOLDER = {pr1:'evidence-pr1',before:'evidence-before'};
export function frozenRoot(run,head,stage='pr1') { return join(realpathSync(run.runDir),ANCHOR_FOLDER[stage],head); }
// The before stage names its historical source by an explicit full commit id: the caller's reconstruction provenance.
export function beforeHead(a) {
  if (!commitSha(a.sourceAnchor?.head) || a.sourceAnchor.head !== a.sourceAnchor.head.toLowerCase()) throw Error('The registered before commit is missing or invalid.');
  return a.sourceAnchor.head;
}
export function checkedAssociation(run,a,capture,listGitFiles) {
  if (a.runId !== run.runId || a.repo !== run.repo || !['current','pr1','before'].includes(a.stage)
    || !/^[a-f0-9]{64}$/.test(a.source_sha256 ?? '') || realpathSync(a.workspaceRoot) !== a.workspaceRoot
    || a.registration?.operation !== 'evidence-associate' || !Number.isFinite(a.registration.at)
    || a.registration.cwd !== realpathSync(run.root)) throw Error('The evidence association has a different run, owner, producer or registration.');
  evidenceTests(a.tests);
  const head = a.stage === 'pr1' ? ownedPr1Head(run) : a.stage === 'before' ? beforeHead(a) : null;
  const root = a.stage === 'current' ? realpathSync(run.root) : frozenRoot(run,head,a.stage);
  if (a.sourceAnchor?.root !== root || a.sourceAnchor?.head !== head || realpathSync(root) !== root)
    throw Error('The registered stage source anchor is missing, changed or unrelated.');
  if (selectedCapture(root,a.tests,capture,listGitFiles).sha256 !== a.source_sha256) throw Error('The registered stage source has changed or is unavailable.');
  if (a.stage === 'current' && selectedCapture(a.workspaceRoot,a.tests,capture,listGitFiles).sha256 !== a.source_sha256)
    throw Error('The producer selected source has changed or is unavailable.');
  return root;
}

// Canonical, read-only association admission for native workspace consumers.
// The existing registered authority remains the only permission rule.
export function readEvidenceEligibility({root,producerRoot,tests,source_sha256,runId=null,stage=null},ports={}){
  const canonicalPath=ports.realpath??realpathSync;
  const capture=ports.captureSource??((dir,options)=>seam().captureSource(dir,options));
  const listGitFiles=ports.gitFiles??(dir=>seam().gitFiles(dir));
  let result={state:'unavailable',reason:'source or ownership unavailable',runId:null,repo:null,producerRoot:null,tests:[],stage:null,sourceAnchor:null,source_sha256:source_sha256??null};
  try{
    root=canonicalPath(root);producerRoot=canonicalPath(producerRoot);tests=evidenceTests(tests);
    result={...result,producerRoot,tests};
    if(!/^[a-f0-9]{64}$/.test(source_sha256??''))return{...result,state:'ineligible',reason:'original selected source identity is missing'};
    const runs=(ports.allRuns??allRuns)({cancelled:true},ports);
    // Only the consumer's owned source/run may authorize an alternate producer.
    const candidates=[];
    for(const run of runs){
      if(!run||typeof run.root!=='string'||canonicalPath(run.root)!==root)continue;
      for(const association of run.evidenceAssociations??[]){
        if(association.workspaceRoot===producerRoot&&selectionEqual(association.tests,tests)&&association.source_sha256===source_sha256)candidates.push({run,association});
      }
    }
    if(candidates.length){
      if(candidates.length!==1)return{...result,state:'ineligible',reason:'workspace association is ambiguous'};
      const {run,association:a}=candidates[0];
      if(runId!==null&&runId!==run.runId||stage!==null&&stage!==a.stage)return{...result,state:'ineligible',reason:'saved run or stage disagrees with the owned association'};
      // Before-the-fix evidence is historical: only a caller that names that stage may read it.
      if(a.stage==='before'&&stage!=='before')return{...result,state:'ineligible',reason:'before-the-fix evidence is historical; it is read only through its registered import'};
      const inspect=ports.inspectRepository??(path=>{const git=spawnSync('git',['rev-parse','--path-format=absolute','--git-common-dir'],{cwd:path,encoding:'utf8'});if(git.status!==0)throw Error('repository ownership unavailable');return canonicalPath(git.stdout.trim());});
      const common=inspect(root);
      if(canonicalPath(run.commonDir)!==common||canonicalPath(run.runDir)!==canonicalPath(runDirFor(common,run.number))||typeof run.repo!=='string'||!run.runId)return{...result,state:'ineligible',reason:'run ownership is missing or contradictory'};
      checkedAssociation(run,a,capture,listGitFiles);
      return{state:'eligible',reason:null,runId:run.runId,repo:run.repo,producerRoot,tests,stage:a.stage,sourceAnchor:{...a.sourceAnchor},source_sha256};
    }
    if(runId!==null||stage!==null&&stage!=='current')return{...result,state:'ineligible',reason:'saved run/stage has no matching owned association'};
    if(root!==producerRoot)return{...result,state:'ineligible',reason:'alternate producer has no owned workspace association'};
    if(capture(root,{tests,appMap:null}).sha256!==source_sha256)return{...result,state:'ineligible',reason:'the exact selected source has changed'};
    return{state:'eligible',reason:null,runId:null,repo:null,producerRoot,tests,stage:'current',sourceAnchor:{root,head:null},source_sha256};
  }catch(error){return{...result,reason:oneLine(error.message??error)};}
}

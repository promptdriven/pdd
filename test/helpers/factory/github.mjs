// Generated from prompts/test/autopilot-factory.prompt.md.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createGithubRepoFake} from '../github-repo-fake.mjs';

export function factoryGithub(w) {
  const f = createGithubRepoFake({repository:w.repository,owner:'example',issues:0,now:()=>w.time});
  f.add(17,{title:'Use value two',body:'The value must be 2.',created:w.time-1000,updated:w.time-1000});
  f.prs = []; f.commands = []; f.merges = [];
  const ok = value => ({code:0,stdout:typeof value==='string'?value:JSON.stringify(value),stderr:''});
  const flag = (a,k) => a[a.indexOf(k)+1];
  const body = (a,o) => a.includes('--body-file') && flag(a,'--body-file')!=='-' ? readFileSync(flag(a,'--body-file'),'utf8') : String(o.input ?? (a.includes('--body')?flag(a,'--body'):''));
  const find = value => f.prs.find(pr=>pr.url===value || pr.number===Number(value));
  const restPr = pr => ({number:pr.number,state:pr.state.toLowerCase(),body:pr.body,merged:pr.state==='MERGED',merged_at:pr.mergedAt,merge_commit_sha:pr.mergeCommit?.oid,
    head:{sha:pr.headRefOid,ref:pr.headRefName},base:{ref:pr.baseRefName,repo:{full_name:f.repo}}});
  const original = f.gh;
  f.gh = async (a,o={}) => {
    f.commands.push({args:a,input:o.input});
    if(a[0]==='--version')return ok('gh version 2.60');
    if(a[0]==='repo' && a[1]==='view' && a.includes('nameWithOwner,defaultBranchRef,viewerPermission,mergeCommitAllowed,squashMergeAllowed,rebaseMergeAllowed'))return ok({nameWithOwner:w.repository,defaultBranchRef:{name:'main'},viewerPermission:'WRITE',squashMergeAllowed:true});
    if(a[0]==='api' && a[1]?.includes('/rules/branches/'))return ok([]);
    if(a[0]==='label') return ok('');
    if(a[0]==='issue') {
      const n=Number(a[2]);
      if(a[1]==='edit') {
        if(a.includes('--add-label')) for(const label of flag(a,'--add-label').split(',')) if(!f.issues.get(n).labels.includes(label)) f.label(n,label);
        if(a.includes('--remove-label')) for(const label of flag(a,'--remove-label').split(',')) f.unlabel(n,label);
        return ok('');
      }
      if(a[1]==='comment') {f.comment(n,body(a,o));return ok('');}
      if(a[1]==='close') {f.close(n);return ok('');}
      assert.fail(`unsupported factory gh issue ${a[1]}`);
    }
    if(a[0]==='pr') {
      if(a[1]==='create') {
        const branch=flag(a,'--head');
        const pr={number:100+f.prs.length,url:`https://github.com/${f.repo}/pull/${100+f.prs.length}`,state:'OPEN',headRefName:branch,baseRefName:flag(a,'--base'),
          headRefOid:w.git(w.remote,'rev-parse',`refs/heads/${branch}`),body:body(a,o),title:flag(a,'--title'),isDraft:a.includes('--draft'),isCrossRepository:false,
          headRepository:{name:'project'},headRepositoryOwner:{login:'example'},mergeCommit:null,mergedAt:null,statusCheckRollup:[],comments:[],reviews:[],reviewDecision:'APPROVED'};
        f.prs.push(pr);return ok(pr.url+'\n');
      }
      if(a[1]==='list') return ok(f.prs.filter(pr=>(!a.includes('--head') || pr.headRefName===flag(a,'--head')) && (!a.includes('--search') || pr.body.includes(flag(a,'--search').split('"')[1]))));
      const pr=find(a[2]);assert.ok(pr,`unknown factory PR ${a[2]}`);
      if(a[1]==='view') return ok({...pr,comments:pr.comments.map((body,index)=>({body,authorAssociation:'OWNER',createdAt:new Date(w.time+index).toISOString(),url:`${pr.url}#issuecomment-${index}`}))});
      if(a[1]==='edit') {if(a.includes('--base'))pr.baseRefName=flag(a,'--base');if(a.includes('--body-file')||a.includes('--body'))pr.body=body(a,o);return ok('');}
      if(a[1]==='comment') {pr.comments.push(body(a,o));return ok('');}
      if(a[1]==='merge') {
        assert.equal(flag(a,'--match-head-commit'),pr.headRefOid,'merge must pin the checked head');
        assert.ok(pr.statusCheckRollup.length && pr.statusCheckRollup.every(c=>c.conclusion==='SUCCESS'),'CI must pass');
        assert.ok(pr.comments.some(c=>{try{return JSON.parse(c).head===pr.headRefOid && JSON.parse(c).verdict==='PASS';}catch{return false;}}),'fresh checker verdict required');
        const peer=w.mergeCheckout;
        w.git(peer,'fetch','-q','origin');w.git(peer,'switch','-q','-C','factory-merge',`origin/${pr.baseRefName}`);
        w.git(peer,'merge','--no-ff','--no-edit',`origin/${pr.headRefName}`);
        const sha=w.git(peer,'rev-parse','HEAD');w.git(peer,'push','-q',w.remote,`HEAD:refs/heads/${pr.baseRefName}`);
        pr.state='MERGED';pr.mergeCommit={oid:sha};pr.mergedAt=new Date(w.time).toISOString();f.merges.push(pr.number);return ok('');
      }
      assert.fail(`unsupported factory gh pr ${a[1]}`);
    }
    if(a[0]==='api') {
      let endpoint=a.find(x=>x.startsWith('repos/')||x.startsWith('https://api.github.com/'));
      endpoint=endpoint?.replace('https://api.github.com/','');
      let value,handled=true;
      if(endpoint===`repos/${f.repo}`)value={full_name:f.repo,owner:{login:f.owner},default_branch:'main'};
      else if(a.includes('PATCH') && /^repos\/[^/]+\/[^/]+\/issues\/\d+$/.test(endpoint??'')) {
        assert.ok(a.includes('state=open'),'factory issue PATCH must reopen the issue');
        const issue=f.issues.get(Number(endpoint.split('/').at(-1)));assert.ok(issue);
        issue.state='open';issue.state_reason=null;value={number:issue.number,state:issue.state};
      }
      else if(endpoint?.includes('/commits/')) {const commit=endpoint.split('/commits/')[1];value={sha:commit,parents:w.git(w.remote,'rev-list','--parents','-n','1',commit).split(/\s+/).slice(1).map(sha=>({sha}))};}
      else if(endpoint?.includes('/releases'))value=[];
      else if(/\/issues\/\d+\/timeline/.test(endpoint??'') && f.issues.get(Number(endpoint.match(/issues\/(\d+)/)[1]))?.timeline.some(e=>e.source)) {
        value=f.issues.get(Number(endpoint.match(/issues\/(\d+)/)[1])).timeline.map(e=>({id:Number(e.id),event:e.event,actor:{login:e.actor},created_at:new Date(e.created).toISOString(),...(e.source?{source:e.source}:{}),...(e.label?{label:{name:e.label}}:{})}));
      }
      else if(endpoint?.includes('/compare/')) {
        const [base,head]=endpoint.split('/compare/')[1].split('...').map(decodeURIComponent);
        const behind=Number(w.git(w.remote,'rev-list','--count',`${head}..${base}`));
        value={behind_by:behind,status:behind?'behind':'identical'};
      }
      else if(/\/pulls\/\d+(?:\?.*)?$/.test(endpoint??''))value=restPr(find(endpoint.match(/pulls\/(\d+)/)[1]));
      else if(/\/pulls\/\d+\/reviews/.test(endpoint??''))value=find(endpoint.match(/pulls\/(\d+)/)[1]).reviews;
      else handled=false;
      if(handled) return ok(a.includes('--include')?`HTTP/2 200 OK\r\n\r\n${JSON.stringify(value)}`:a.includes('--slurp')?[value]:value);
    }
    const r=await original(a,o);
    // Shared fake models gh api --include. The real CLI also uses bare JSON and slurp.
    if(a[0]==='api' && !a.includes('--include')) {
      const text=r.stdout.split(/\r?\n\r?\n/).slice(1).join('\n\n');
      r.stdout=a.includes('--slurp')?JSON.stringify([JSON.parse(text)]):text;
    }
    assert.ok(!/HTTP 404/.test(r.stderr),`unsupported factory gh route ${a.join(' ')}: ${r.stderr}`);
    return r;
  };
  f.syncHeads = () => {for(const pr of f.prs)if(pr.state==='OPEN')pr.headRefOid=w.git(w.remote,'rev-parse',`refs/heads/${pr.headRefName}`);};
  return f;
}

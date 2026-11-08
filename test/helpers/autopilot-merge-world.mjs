import {createGithubRepoFake} from './github-repo-fake.mjs';

export function mergeWorld({queue=false} = {}) {
  const repo = createGithubRepoFake({repository:'acme/widgets',owner:'acme',issues:1});
  repo.add(17);
  const w = {repo, comments:[], writes:[], reads:0, config:{autopilot:{mode:'auto'}}, trusted:true,
    pull:{id:'PR_17',head:'a'.repeat(40),base:'autopilot-next',baseOid:'b'.repeat(40),state:'OPEN',draft:false,
      reviewDecision:null,pendingReviews:0,mergeStateStatus:'CLEAN',mergeCommit:null,queue,entry:null}};
  w.evidence = {issue:1,head:w.pull.head,base:w.pull.base,area:'cli',authorization:'Operator test mandate',gatesSatisfied:true,
    reviews:[{head:w.pull.head,verdict:'PASS',fresh:true,mustFix:0,session:'fresh-session',risk:2}],
    splitVerdict:false,sensitive:false,fullSuite:{head:w.pull.head,passed:true,noNewSkips:true},repairs:0,questionOpen:false,audit:{planned:true},comment:'Operator test mandate; current head and review evidence'};
  w.ci = {head:w.pull.head,complete:true,checks:[{name:'tests',passed:true}],required:['tests']};
  w.ports = {github:{
    pull:async () => { w.reads++; if (w.onRead) await w.onRead(); return structuredClone(w.pull); },
    config:async () => structuredClone(w.config),
    authority:async () => structuredClone(w.authority ?? w.config),
    trusted:async () => w.trusted,
    ci:async () => structuredClone(w.ci),
    comment:async (pr,body) => {
      const response = await repo.gh(['api','--include','repos/acme/widgets/issues/1/comments','-f',`body=${body}`]);
      if (response.code) throw Error('fake comment refused');
      w.comments.push({pr,body}); if (w.afterComment) await w.afterComment();
    },
    enqueue:async (id,head) => { w.writes.push({kind:'queue',id,head}); w.pull.entry={id:'QE_17',state:'QUEUED'}; if (w.afterWrite) await w.afterWrite(); },
    merge:async (pr,head) => { w.writes.push({kind:'direct',pr,head}); w.pull.state='MERGED'; w.pull.mergeCommit='c'.repeat(40); if (w.afterWrite) await w.afterWrite(); },
  },patchEquivalent:async () => false};
  return w;
}

// Exercise the native adapter through the same gh fake used by repository tests.
// The wrapper supplies merge-queue fields, base policy and default-branch controls.
export function nativeMergeWorld(options) {
  const w=mergeWorld(options);w.commands=[];w.configRefs=[];w.queueBranches=[];
  w.ports={execFile:async(file,args,opts)=>{
    w.commands.push({file,args});
    const json=value=>({stdout:JSON.stringify(value),stderr:''});
    if(file==='git' && args[0]==='remote')return{stdout:'https://github.com/acme/widgets.git\n'};
    if(file!=='gh')throw Error(`Unexpected fake program ${file}`);
    if(args[0]==='repo')return w.repo.gh(args,opts);
    if(args[0]==='api' && args[1]==='graphql'){
      const values=Object.fromEntries(args.slice(2).filter(x=>x.includes('=')).map(x=>{const i=x.indexOf('=');return[x.slice(0,i),x.slice(i+1)];}));
      if(values.query.includes('enqueuePullRequest')){
        w.writes.push({kind:'queue',id:values.id,head:values.head});w.pull.entry={id:'QE_17',state:'QUEUED'};
        if(w.afterWrite)await w.afterWrite();return json({data:{enqueuePullRequest:{mergeQueueEntry:w.pull.entry}}});
      }
      if(values.query.includes('mergeQueue(branch:')){
        w.queueBranches.push(values.branch);
        if(w.queueError)return json({errors:[{message:'queue unavailable'}]});
        return json({data:{repository:{mergeQueue:w.pull.queue?{id:'MQ_NEXT'}:null}}});
      }
      w.reads++;if(w.onRead)await w.onRead();const p=w.pull;
      return json({data:{repository:{pullRequest:{id:p.id,headRefOid:p.head,baseRefName:p.base,baseRefOid:p.baseOid,
        state:p.state,isDraft:p.draft,reviewDecision:p.reviewDecision,reviewRequests:{totalCount:p.pendingReviews},mergeStateStatus:p.mergeStateStatus,
        mergeCommit:p.mergeCommit?{oid:p.mergeCommit}:null,mergeQueueEntry:p.entry}}}});
    }
    if(args[0]==='api' && args[1].includes('/contents/pdd.json?ref=')){
      const ref=decodeURIComponent(args[1].split('?ref=')[1]);w.configRefs.push(ref);
      const current=ref==='main';
      if(current && w.authorityError)throw Object.assign(Error('authority unavailable'),{code:1,stderr:'HTTP 503'});
      if(current && w.authorityMissing)throw Object.assign(Error('authority missing'),{code:1,stderr:'(HTTP 404)'});
      return json({encoding:'base64',content:Buffer.from(JSON.stringify(current?(w.authority ?? w.config):w.config)).toString('base64')});
    }
    if(args[0]==='pr' && args[1]==='checks'){
      const rows=(args.includes('--required')?w.ci.required.map(name=>w.ci.checks.find(c=>c.name===name)??{name,passed:false}):w.ci.checks)
        .map(c=>({name:c.name,bucket:c.bucket ?? (c.passed?'pass':'pending')}));
      if(w.checkExit){throw Object.assign(Error('checks not green'),{code:w.checkExit,stdout:JSON.stringify(rows)});}
      if(w.checkError){throw Object.assign(Error('checks pending'),{code:8,stdout:JSON.stringify(rows)});}
      return json(rows);
    }
    if(args[0]==='pr' && args[1]==='merge'){
      w.writes.push({kind:'direct',pr:Number(args[2]),head:args[args.indexOf('--match-head-commit')+1]});
      w.pull.state='MERGED';w.pull.mergeCommit='c'.repeat(40);if(w.afterWrite)await w.afterWrite();return{stdout:''};
    }
    if(args[0]==='api'){
      const reply=await w.repo.gh(['api','--include',...args.slice(1)],opts);
      if(reply.code)throw Object.assign(Error('fake HTTP error'),{code:reply.code,stderr:reply.stderr,stdout:reply.stdout});
      const payload=reply.stdout.split('\r\n\r\n')[1];
      if(args[1].endsWith('/comments')){w.comments.push({pr:17,body:args.at(-1).slice(5)});if(w.afterComment)await w.afterComment();}
      return{stdout:payload,stderr:''};
    }
    throw Error('Unexpected fake gh route');
  }};
  return w;
}

#!/usr/bin/env node
import * as fs from 'node:fs';
const f = JSON.parse(fs.readFileSync(process.env.READER_FIXTURE_FILE, 'utf8'));
const a=process.argv.slice(2);
fs.appendFileSync(process.env.READER_GH_LOG, JSON.stringify(a)+'\n');
if(a[0]==='repo' && a[1]==='view') { console.log(JSON.stringify({nameWithOwner:'example/project',defaultBranchRef:{name:'main'},url:'https://github.com/example/project'})); process.exit(0); }
if(a[0] !== 'api' || a[1] !== '--include' || a[2] !== '--method' || a[3] !== 'GET') { console.error('unexpected command'); process.exit(2); }
const p=a[4]; let v;
if(p==='repos/example/project') v={owner:{login:'example'}};
else if(p==='repos/example/project/collaborators?per_page=100') v=[];
else if(p==='repos/example/project/issues/17') v={labels:f.labels};
else if(p==='repos/example/project/issues/17/timeline?per_page=100') v=f.events;
else if(p==='repos/example/project/issues/17/comments?per_page=100') v=f.comments;
else { console.error('unexpected endpoint '+p); process.exit(2); }
console.log('HTTP/1.1 200 OK\n\n'+JSON.stringify(v));

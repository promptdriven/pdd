// Generated from prompts/cli/autopilot-metrics.prompt.md.
const kinds = new Set(['started','worked','evidence','validated','merged','regression']);
const fields = ['runtime','vectors','formal','tests'];
const emptyEvidence = () => Object.fromEntries(fields.map(key => [key,false]));
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
function timestamp(value) {
  if (typeof value === 'number') return value;
  if (typeof value !== 'string' || !/^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d(?:\.\d{1,3})?Z$/.test(value)) return NaN;
  const parsed=Date.parse(value);
  return Number.isFinite(parsed) && new Date(parsed).toISOString().slice(0,19) === value.slice(0,19) ? parsed : NaN;
}
const sha = value => typeof value === 'string' && /^[a-f0-9]{40}$/i.test(value);

export function canonicalAutopilotEvidence(text) {
  const lines = typeof text === 'string' ? text.split(/\r?\n/).map(line=>line.trim()).filter(line=>line.startsWith('Evidence:')) : [];
  if (!lines.length) return null;
  let signature, result;
  for (const line of lines) {
    const parts = line.slice('Evidence:'.length).trim().split(/;\s*/);
    if (parts.length !== fields.length) return null;
    const facts = [];
    for (const [index,key] of fields.entries()) {
      const match = new RegExp(`^${key}=(pass|fail|not-run)(?: \\((\\d+)/(\\d+)\\))?$`).exec(parts[index]);
      if (!match) return null;
      const [,state,n,m] = match, passed = n === undefined ? null : Number(n), total = m === undefined ? null : Number(m);
      if (n !== undefined && (!Number.isSafeInteger(passed) || !Number.isSafeInteger(total) || passed > total)) return null;
      facts.push({state,passed,total});
    }
    const next = JSON.stringify(facts);
    if (signature && signature !== next) return null;
    signature = next;
    result = 'Evidence: '+fields.map((key,index)=>`${key}=${facts[index].state}${facts[index].total === null ? '' : ` (${facts[index].passed}/${facts[index].total})`}`).join('; ');
  }
  return result;
}

export function parseAutopilotEvidence(text) {
  const line=canonicalAutopilotEvidence(text);
  if (!line) return emptyEvidence();
  return Object.fromEntries(line.slice('Evidence: '.length).split('; ').map((part,index)=>{
    const [,state,n,m]=/^[a-z]+=(pass|fail|not-run)(?: \((\d+)\/(\d+)\))?$/.exec(part);
    return [fields[index],state === 'pass' && (n === undefined || Number(m) > 0 && Number(n) === Number(m))];
  }));
}

export function normalizeAutopilotMetric(event) {
  if (!object(event) || typeof event.repo !== 'string' || !/^[\w.-]+\/[\w.-]+$/.test(event.repo) || event.repo.split('/').some(part=>part === '.' || part === '..') || !Number.isSafeInteger(event.issue) || event.issue <= 0 || !kinds.has(event.kind) || !Number.isFinite(timestamp(event.at)) || !Number.isFinite(new Date(timestamp(event.at)).getTime())) return null;
  if (event.pr !== undefined && (!Number.isSafeInteger(event.pr) || event.pr <= 0) || event.head !== undefined && !sha(event.head) || event.mergeCommit !== undefined && !sha(event.mergeCommit) || event.evidence !== undefined && typeof event.evidence !== 'string' || event.reason !== undefined && typeof event.reason !== 'string') return null;
  const result = {repo:event.repo.toLowerCase(),issue:event.issue,kind:event.kind,at:new Date(timestamp(event.at)).toISOString()};
  for (const key of ['pr','head','mergeCommit','evidence','reason']) if (event[key] !== undefined) result[key] = ['head','mergeCommit'].includes(key) ? event[key].toLowerCase() : event[key];
  if (object(event.validation)) {
    result.validation = {};
    for (const [key,names] of Object.entries({review:['head','verdict','fresh'],tests:['head','state'],ci:['head','state']})) if (object(event.validation[key])) {
      const part=event.validation[key];
      const allowed=(name,value)=>name === 'head' ? sha(value) : name === 'fresh' ? typeof value === 'boolean' : name === 'verdict' ? ['PASS','FAIL','NOT SURE'].includes(value) : ['pass','fail','not-run'].includes(value);
      result.validation[key] = Object.fromEntries(names.filter(name=>allowed(name,part[name])).map(name=>[name,name === 'head' ? part[name].toLowerCase() : part[name]]));
    }
  }
  return result;
}

const dateShift = (date,days) => new Date(Date.parse(`${date}T12:00:00Z`) + days*86400000).toISOString().slice(0,10);
function calendar(timezone) {
  let formatter;
  try { formatter = new Intl.DateTimeFormat('en-CA',{timeZone:timezone,year:'numeric',month:'2-digit',day:'2-digit',hour:'2-digit',minute:'2-digit',second:'2-digit',hourCycle:'h23'}); }
  catch { throw Error('Invalid timezone'); }
  const local = at => Object.fromEntries(formatter.formatToParts(new Date(at)).map(({type,value})=>[type,value]));
  const boundary = date => {
    const target = Date.parse(`${date}T09:00:00Z`);
    let guess = target;
    for (let i=0;i<4;i++) {
      const p = local(guess), offset = Date.parse(`${p.year}-${p.month}-${p.day}T${p.hour}:${p.minute}:${p.second}Z`) - guess;
      const next = target - offset;
      if (next === guess) break;
      guess = next;
    }
    return guess;
  };
  return {local,boundary};
}
const identity = event => `${event.repo}#${event.issue}`;
function validated(event) {
  const v = event.validation;
  return sha(event.head) && v?.review?.head === event.head && v.review.verdict === 'PASS' && v.review.fresh === true && ['tests','ci'].every(key=>v[key]?.head === event.head && v[key].state === 'pass');
}

export function calculateAutopilotMetrics({events=[],timezone=Intl.DateTimeFormat().resolvedOptions().timeZone,observedAt}) {
  const {local,boundary} = calendar(timezone), now = timestamp(observedAt);
  if (!Number.isFinite(now) || !Number.isFinite(new Date(now).getTime())) throw Error('Invalid cutoff');
  const parts = local(now), date = `${parts.year}-${parts.month}-${parts.day}`;
  const current = Number(parts.hour) < 9 ? dateShift(date,-1) : date, previous = dateShift(current,-1);
  let monday = dateShift(current,-((new Date(`${current}T12:00:00Z`).getUTCDay()+6)%7));
  let finishedDays = Math.round((Date.parse(current)-Date.parse(monday))/86400000), label = 'Week avg';
  if (!finishedDays) { monday=dateShift(monday,-7); finishedDays=7; label='Last week'; }
  const weekEnd = dateShift(monday,finishedDays);
  const clean = events.map(normalizeAutopilotMetric).filter(event=>event && Date.parse(event.at) <= now);
  const merges = clean.filter(event=>event.kind === 'merged');
  const daily = startDate => {
    const start=boundary(startDate), end=boundary(dateShift(startDate,1));
    const sets=Object.fromEntries(['started','worked','runtime','vectors','formal','validated','merged','regressions'].map(key=>[key,new Set()]));
    for (const event of clean) {
      const at=Date.parse(event.at); if (at < start || at >= end) continue;
      const id=identity(event); sets.worked.add(id);
      if (event.kind === 'started' || event.kind === 'merged') sets[event.kind].add(id);
      if (event.kind === 'evidence') for (const [key,pass] of Object.entries(parseAutopilotEvidence(event.evidence))) if (pass && key !== 'tests') sets[key].add(id);
      if (event.kind === 'validated' && validated(event)) sets.validated.add(id);
      if (event.kind === 'regression' && ['reverted','bad-audit','merge-ci-red'].includes(event.reason) && merges.some(merge=>identity(merge) === id && Date.parse(merge.at) < at && (event.pr === undefined || merge.pr === event.pr) && (event.mergeCommit === undefined || merge.mergeCommit === undefined || merge.mergeCommit === event.mergeCommit))) sets.regressions.add(id);
    }
    return sets;
  };
  const daySets=daily(previous), weekSets=Array.from({length:finishedDays},(_,i)=>daily(dateShift(monday,i)));
  const conversion = sets => {
    const starts=new Set(sets.flatMap(group=>[...group.started])), merged=new Set(sets.flatMap(group=>[...group.merged]));
    return starts.size ? [...starts].filter(id=>merged.has(id)).length/starts.size*100 : null;
  };
  const labels={started:'Issues started',worked:'Issues worked on',runtime:'Runtime passed',vectors:'Test vectors passed',formal:'Formal verification',validated:'Validation passed',merged:'Merged by Autopilot',regressions:'Regressions'};
  return {scope:'local-autopilot',timezone,observedAt:new Date(now).toISOString(),day:{date:previous,label:new Intl.DateTimeFormat('en-US',{weekday:'short',timeZone:'UTC'}).format(new Date(`${previous}T12:00:00Z`)),start:new Date(boundary(previous)).toISOString(),end:new Date(boundary(current)).toISOString()},week:{label,start:new Date(boundary(monday)).toISOString(),end:new Date(boundary(weekEnd)).toISOString(),finishedDays},rows:[...Object.entries(labels).map(([key,label])=>({key,label,day:daySets[key].size,weekAverage:weekSets.reduce((sum,group)=>sum+group[key].size,0)/finishedDays})),{key:'startedToMerged',label:'Started-to-merged %',day:conversion([daySets]),weekAverage:conversion(weekSets)}]};
}

export function renderAutopilotMetrics(report) {
  const format=(value,percent)=>value === null ? 'n/a' : `${Number(value.toFixed(2))}${percent ? '%' : ''}`;
  const rows=report.rows.map(row=>[row.label,format(row.day,row.key === 'startedToMerged'),format(row.weekAverage,row.key === 'startedToMerged')]);
  const table=[['Autopilot',report.day.label,report.week.label],...rows], widths=[0,1,2].map(i=>Math.max(...table.map(row=>row[i].length)));
  return `Autopilot — ${report.day.date} (${report.timezone}, 09:00–09:00)\n`+table.map(row=>row.map((cell,i)=>i ? cell.padStart(widths[i]) : cell.padEnd(widths[i])).join('  ')).join('\n')+'\n';
}

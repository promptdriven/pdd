// Generated from prompts/cli/metrics-gap.prompt.md (sha256: 2bd474af2b688457c5358e550521bd73e6869cfbbcb85a6b28cd52d9df81b7a6).
// Best-effort durable fallback when metrics identity or outbox creation fails.
import * as nativeFiles from 'node:fs';
import {join} from 'node:path';
import {randomUUID} from 'node:crypto';

export function recordCaptureGap({commonDir,repo,issue,at}, fs = nativeFiles) {
  const dir=join(commonDir,'pdd','metrics-gaps'); fs.mkdirSync(dir,{recursive:true,mode:0o700});
  const id=randomUUID(), temp=join(dir,`.${id}.tmp`), file=join(dir,`${id}.json`), time=new Date(at).toISOString();
  const event={schema:'pdd.metrics.event.v1',id:`gap:${id}`,repo:repo.toLowerCase(),issue,type:'coverage',at:time,observedAt:time,source:`gap:${id}`,data:{complete:false}};
  const fd=fs.openSync(temp,'wx',0o600);
  try { fs.writeFileSync(fd,JSON.stringify(event)); fs.fsyncSync(fd); } finally {fs.closeSync(fd);}
  try { fs.renameSync(temp,file); const parent=fs.openSync(dir,'r'); try {fs.fsyncSync(parent);} finally {fs.closeSync(parent);} }
  finally {try {fs.unlinkSync(temp);} catch {}}
}

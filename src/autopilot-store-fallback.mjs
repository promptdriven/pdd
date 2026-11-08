// Implements prompts/cli/autopilot-store-fallback.prompt.md.
import * as nativeFs from 'node:fs';
import { randomUUID } from 'node:crypto';
import { hostname } from 'node:os';
import { join } from 'node:path';

const owners = new Set();
const copy = value => value === undefined ? undefined : JSON.parse(JSON.stringify(value));
const buckets = new Set(['control','queue','runs','leases','budgets','costs','events','cache','alerts']);
export function openFallbackStore({root}, ports={}) {
  const fs=ports.fs??nativeFs, file=join(root,'machine-state.json'), lock=join(root,'.machine-owner');
  fs.mkdirSync(root,{recursive:true,mode:0o700});
  const acquire=()=>{
    if(owners.has(root))throw Error('Nested machine state transaction');
    fs.mkdirSync(lock,{recursive:true,mode:0o700});
    const token=randomUUID(), leaf=join(lock,`owner-${token}.json`), text=JSON.stringify({pid:process.pid,host:hostname(),token});
    const temp=join(root,`.owner-${token}.tmp`), until=Date.now()+5000;
    const release=()=>{owners.delete(root);try{if(fs.readFileSync(leaf,'utf8')===text)fs.unlinkSync(leaf);}catch{}};
    try {
      fs.writeFileSync(temp,text,{flag:'wx',mode:0o600});fs.renameSync(temp,leaf);
      while(true){
        for(const name of fs.readdirSync(lock)){
          if(name===`owner-${token}.json`)continue;
          let other,bytes;const path=join(lock,name);
          try{bytes=fs.readFileSync(path,'utf8');other=JSON.parse(bytes);}catch{continue;}
          if(other.host!==hostname()||!Number.isInteger(other.pid)||other.pid<1||name!==`owner-${other.token}.json`)continue;
          let dead=false;try{process.kill(other.pid,0);}catch(error){dead=error.code==='ESRCH';}
          if(dead)try{if(fs.readFileSync(path,'utf8')===bytes)fs.unlinkSync(path);}catch{}
        }
        if(fs.readdirSync(lock).every(name=>name===`owner-${token}.json`)){owners.add(root);return release;}
        if(Date.now()>=until)throw Error('Machine state is busy');
        // Competing unacquired tokens withdraw to let one contender proceed.
        fs.unlinkSync(leaf);
        Atomics.wait(new Int32Array(new SharedArrayBuffer(4)),0,0,10);
        fs.writeFileSync(temp,text,{flag:'wx',mode:0o600});fs.renameSync(temp,leaf);
      }
    }catch(error){release();throw error;}finally{try{fs.unlinkSync(temp);}catch{}}
  };
  return {close(){},transaction(callback){
    const release=acquire();let usable=true;
    try{
      let state;
      try{state=JSON.parse(fs.readFileSync(file,'utf8'));}catch(error){if(error.code!=='ENOENT')throw error;state={v:1,records:[],journal:[],sequence:0,imports:[]};}
      if(state.v!==1||!Array.isArray(state.records)||!Array.isArray(state.journal)||!Array.isArray(state.imports)||!Number.isSafeInteger(state.sequence))throw Error('Unsupported machine state snapshot');
      const check=(bucket,key,optional=false)=>{if(!usable)throw Error('Machine state transaction has ended');if(!buckets.has(bucket)||!(typeof key==='string'||(optional&&key===undefined)))throw new TypeError('Invalid machine state address');};
      const tx={
        get(bucket,key){check(bucket,key);return copy(state.records.find(row=>row.bucket===bucket&&row.key===key)?.value);},
        put(bucket,key,value){check(bucket,key);if(value===undefined)throw new TypeError('Machine state requires a JSON value');tx.remove(bucket,key);state.records.push({bucket,key,value:copy(value)});},
        remove(bucket,key){check(bucket,key);state.records=state.records.filter(row=>row.bucket!==bucket||row.key!==key);},
        list(bucket){check(bucket,undefined,true);return state.records.filter(row=>row.bucket===bucket).sort((a,b)=>a.key<b.key?-1:a.key>b.key?1:0).map(({key,value})=>({key,value:copy(value)}));},
        append(bucket,scope,value){check(bucket,scope);if(value===undefined)throw new TypeError('Machine state requires a JSON value');const sequence=++state.sequence;state.journal.push({bucket,scope,sequence,value:copy(value)});return sequence;},
        entries(bucket,scope){check(bucket,scope,true);return state.journal.filter(row=>row.bucket===bucket&&(scope===undefined||row.scope===scope)).map(({sequence,scope,value})=>({sequence,scope,value:copy(value)}));},
        removeEntry(bucket,scope,sequence){check(bucket,scope);state.journal=state.journal.filter(row=>row.bucket!==bucket||row.scope!==scope||row.sequence!==sequence);},
        prune(bucket,scope,before){check(bucket,scope);state.journal=state.journal.filter(row=>row.bucket!==bucket||row.scope!==scope||row.sequence>before);},
        migrate(identity,read,apply){if(!usable)throw Error('Machine state transaction has ended');if(typeof identity!=='string')throw new TypeError('Invalid migration identity');if(state.imports.includes(identity))return;const value=read();if(value===undefined)return;apply(value);state.imports.push(identity);},
      };
      const result=callback(tx);usable=false;
      if(result&&typeof result.then==='function')throw new TypeError('Machine state transactions must be synchronous');
      const temp=join(root,`.machine-${randomUUID()}.tmp`);
      try{
        const fd=fs.openSync(temp,'wx',0o600);
        try{fs.writeFileSync(fd,JSON.stringify(state));fs.fsyncSync(fd);}finally{fs.closeSync(fd);}
        fs.renameSync(temp,file);
        const parent=fs.openSync(root,'r');try{fs.fsyncSync(parent);}finally{fs.closeSync(parent);}
      }finally{try{fs.unlinkSync(temp);}catch{}}
      return result;
    }finally{usable=false;release();}
  }};
}

// Contract: prompts/cli/phone-approval.prompt.md.
import {webcrypto} from 'node:crypto';

const UUID=/^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/;
const STAGE=/^(?=.{1,64}$)[a-z][a-z0-9]*(?:-[a-z0-9]+)*$/;
const PHONE=/^[A-Za-z0-9_-]{1,128}$/;
const positive=value=>Number.isSafeInteger(value)&&value>0;
const object=value=>value!==null&&typeof value==='object'&&!Array.isArray(value);
const validText=value=>typeof value==='string'&&[...value].length>=1&&[...value].length<=4000&&!/[\x00-\x08\x0b-\x1f\x7f-\x9f]/u.test(value);
const messages={
  phone_invalid_token:'The phone approval token is malformed.',
  phone_binding_mismatch:'The phone approval token does not match this run, gate or decision.',
  phone_token_expired:'The phone approval token is too old or its time is in the future.',
  phone_token_replayed:'This phone approval token has already been used.',
  phone_ledger_unavailable:'The phone approval could not be checked against the fleet ledger.',
  phone_not_active:'The phone has been removed from the fleet ledger.',
  phone_invalid_signature:'The phone approval signature could not be verified.',
};
const refuse=code=>({ok:false,code,message:messages[code]});
function exactKeys(value,keys) {
  return object(value)&&Object.keys(value).length===keys.length&&keys.every(key=>Object.hasOwn(value,key));
}
function decode(value) {
  if(typeof value!=='string'||!value||!/^[A-Za-z0-9_-]+$/.test(value))throw Error('encoding');
  const bytes=Buffer.from(value,'base64url');
  if(bytes.toString('base64url')!==value)throw Error('encoding');
  return bytes;
}
function validBinding(value) {
  return object(value)&&UUID.test(value.runId??'')&&STAGE.test(value.stage??'')
    &&['approve','changes','skip'].includes(value.decision)&&positive(value.expectSeq)&&PHONE.test(value.phoneId??'')
    &&(value.decision==='changes'?validText(value.text):value.text===undefined);
}
function canonicalPayload(payload) {
  return {runId:payload.runId,stage:payload.stage,decision:payload.decision,expectSeq:payload.expectSeq,
    phoneId:payload.phoneId,time:payload.time,nonce:payload.nonce,
    ...(payload.decision==='changes'?{text:payload.text}:{})};
}

export async function verifyPhoneApproval(input,ports={}) {
  try {
    if(!validBinding(input)||typeof input.token!=='string'||input.token.length>40000
      ||input.usedNonces!==undefined&&!Array.isArray(input.usedNonces))return refuse('phone_invalid_token');
    let envelope,signature;
    try {
      // A fatal decoder prevents alternate malformed UTF-8 from supplying signed text.
      envelope=JSON.parse(new TextDecoder('utf-8',{fatal:true}).decode(decode(input.token)));
      if(!object(envelope)||!['v','alg','payload','signature'].every(key=>Object.hasOwn(envelope,key))||envelope.v!==1||envelope.alg!=='ES256')return refuse('phone_invalid_token');
      const payload=envelope.payload;
      const keys=['runId','stage','decision','expectSeq','phoneId','time','nonce',...(payload?.decision==='changes'?['text']:[])];
      if(!exactKeys(payload,keys)||!validBinding(payload)||!Number.isSafeInteger(payload.time)||payload.time<0||!UUID.test(payload.nonce??''))return refuse('phone_invalid_token');
      signature=decode(envelope.signature);if(signature.length!==64)return refuse('phone_invalid_token');
    }catch{return refuse('phone_invalid_token');}
    const payload=envelope.payload;
    if(['runId','stage','decision','expectSeq','phoneId','text'].some(key=>input[key]!==payload[key]))return refuse('phone_binding_mismatch');
    const now=(ports.now??Date.now)();
    if(!Number.isSafeInteger(now)||now<0)return refuse('phone_invalid_token');
    if(payload.time<now-300000||payload.time>now+300000)return refuse('phone_token_expired');
    if((input.usedNonces??[]).some(used=>used===payload.nonce||object(used)&&used.phoneId===payload.phoneId&&used.nonce===payload.nonce))return refuse('phone_token_replayed');
    if(typeof ports.lookupPhone!=='function')return refuse('phone_ledger_unavailable');
    let phone;
    try{phone=await ports.lookupPhone(payload.phoneId);}catch{return refuse('phone_ledger_unavailable');}
    if(!object(phone)||phone.phoneId!==payload.phoneId)return refuse('phone_ledger_unavailable');
    if(phone.removed===true||phone.state==='removed')return refuse('phone_not_active');
    if(phone.removed!==false||phone.state!==undefined&&phone.state!=='active'||!object(phone.publicKeyJwk))return refuse('phone_ledger_unavailable');
    try {
      const jwk=phone.publicKeyJwk;
      if(!object(jwk)||jwk.kty!=='EC'||jwk.crv!=='P-256'||Object.hasOwn(jwk,'d'))return refuse('phone_invalid_signature');
      const key=await webcrypto.subtle.importKey('jwk',jwk,{name:'ECDSA',namedCurve:'P-256'},false,['verify']);
      const bytes=new TextEncoder().encode(JSON.stringify(canonicalPayload(payload)));
      if(!await webcrypto.subtle.verify({name:'ECDSA',hash:'SHA-256'},key,signature,bytes))return refuse('phone_invalid_signature');
    }catch{return refuse('phone_invalid_signature');}
    return {ok:true,approvalRecord:{kind:'phone',phoneId:payload.phoneId,nonce:payload.nonce,at:payload.time}};
  }catch{return refuse('phone_invalid_token');}
}

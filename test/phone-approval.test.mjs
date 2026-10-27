import test from 'node:test';
import assert from 'node:assert/strict';
import {webcrypto} from 'node:crypto';
import {verifyPhoneApproval} from '../src/phone-approval.mjs';

const now=1793059200000;
const runId='11111111-1111-4111-8111-111111111111';
const nonce='22222222-2222-4222-8222-222222222222';
const phoneId='phone_A-17';
const base={runId,stage:'change',decision:'approve',expectSeq:17,phoneId,time:now,nonce};
const encode=value=>Buffer.from(JSON.stringify(value)).toString('base64url');
async function fixture() {
  const pair=await webcrypto.subtle.generateKey({name:'ECDSA',namedCurve:'P-256'},false,['sign','verify']);
  assert.equal(pair.privateKey.extractable,false);
  const publicKeyJwk=await webcrypto.subtle.exportKey('jwk',pair.publicKey);
  let lookups=0;
  const ports={now:()=>now,lookupPhone:async id=>{lookups++;assert.equal(id,phoneId);return {phoneId,removed:false,publicKeyJwk};}};
  async function sign(payload=base) {
    const signature=Buffer.from(await webcrypto.subtle.sign({name:'ECDSA',hash:'SHA-256'},pair.privateKey,new TextEncoder().encode(JSON.stringify(payload)))).toString('base64url');
    return encode({v:1,alg:'ES256',payload,signature});
  }
  const input=token=>({token,phoneId,runId,stage:'change',decision:'approve',expectSeq:17,usedNonces:[]});
  return {ports,sign,input,pair,publicKeyJwk,get lookups(){return lookups;}};
}

test('real non-exportable WebCrypto device key proves active phone approval',async()=>{
 const f=await fixture(),token=await f.sign();const result=await verifyPhoneApproval(f.input(token),f.ports);
 assert.deepEqual(result,{ok:true,approvalRecord:{kind:'phone',phoneId,nonce,at:now}});assert.equal(f.lookups,1);
});
test('same signature with changed binding or changes text never admits',async()=>{
 const f=await fixture(),token=await f.sign();
 for(const patch of [{runId:'33333333-3333-4333-8333-333333333333'},{stage:'verify'},{decision:'skip'},{expectSeq:18},{phoneId:'other'}])assert.equal((await verifyPhoneApproval({...f.input(token),...patch},f.ports)).code,'phone_binding_mismatch');
 const change={...base,decision:'changes',text:'Please add Unicode 😀 edge case.\nKeep tests.'},signed=await f.sign(change);
 assert.equal((await verifyPhoneApproval({...f.input(signed),decision:'changes',text:change.text},f.ports)).ok,true);
 assert.equal((await verifyPhoneApproval({...f.input(signed),decision:'changes',text:'Different request'},f.ports)).code,'phone_binding_mismatch');
});
test('old or future token refuses, exact time boundaries accept',async()=>{
 const f=await fixture();
 for(const time of [now-300001,now+300001])assert.equal((await verifyPhoneApproval(f.input(await f.sign({...base,time})),f.ports)).code,'phone_token_expired');
 for(const time of [now-300000,now+300000])assert.equal((await verifyPhoneApproval(f.input(await f.sign({...base,time})),f.ports)).ok,true);
});
test('saved nonce refuses replay without ledger call',async()=>{
 const f=await fixture(),token=await f.sign();
 for(const usedNonces of [[nonce],[{phoneId,nonce}]])assert.equal((await verifyPhoneApproval({...f.input(token),usedNonces},f.ports)).code,'phone_token_replayed');
 assert.equal(f.lookups,0);
 assert.equal((await verifyPhoneApproval({...f.input(token),usedNonces:[{phoneId:'different',nonce}]},f.ports)).ok,true);
});
test('ledger unavailable, missing, mismatched and removed phone all refuse',async()=>{
 const f=await fixture(),input=f.input(await f.sign());
 assert.equal((await verifyPhoneApproval(input,{now:()=>now})).code,'phone_ledger_unavailable');
 assert.equal((await verifyPhoneApproval(input,{...f.ports,lookupPhone:async()=>{throw Error('private endpoint');}})).code,'phone_ledger_unavailable');
 for(const entry of [null,undefined,{phoneId,publicKeyJwk:f.publicKeyJwk},{phoneId:'different',removed:false,publicKeyJwk:f.publicKeyJwk},{phoneId,removed:false,publicKeyJwk:f.publicKeyJwk,state:'unverified'},{phoneId,removed:false}])assert.equal((await verifyPhoneApproval(input,{...f.ports,lookupPhone:async()=>entry})).code,'phone_ledger_unavailable');
 for(const entry of [{phoneId,removed:true,publicKeyJwk:f.publicKeyJwk},{phoneId,removed:false,publicKeyJwk:f.publicKeyJwk,state:'removed'}])assert.equal((await verifyPhoneApproval(input,{...f.ports,lookupPhone:async()=>entry})).code,'phone_not_active');
 assert.equal((await verifyPhoneApproval(input,{...f.ports,lookupPhone:async()=>({phoneId,removed:false,publicKeyJwk:f.publicKeyJwk,state:'active',fleetId:'fleet-fixture',publicKeySpki:'adapter-owned'})})).ok,true);
});
test('different real signing key and edited signed bytes are rejected',async()=>{
 const f=await fixture(),other=await fixture();
 assert.equal((await verifyPhoneApproval(f.input(await other.sign()),f.ports)).code,'phone_invalid_signature');
 const envelope=JSON.parse(Buffer.from(await f.sign(),'base64url'));envelope.payload.time++;
 assert.equal((await verifyPhoneApproval(f.input(encode(envelope)),f.ports)).code,'phone_invalid_signature');
});
test('public-only P-256 ledger key is required',async()=>{
 const f=await fixture(),input=f.input(await f.sign());
 for(const publicKeyJwk of [{...f.publicKeyJwk,d:'untrusted'},{...f.publicKeyJwk,crv:'P-384'},{...f.publicKeyJwk,x:'broken'}])assert.equal((await verifyPhoneApproval(input,{...f.ports,lookupPhone:async()=>({phoneId,removed:false,publicKeyJwk})})).code,'phone_invalid_signature');
});
test('malformed envelope, signature and unknown payload fields refuse without lookup',async()=>{
 const f=await fixture(),good=JSON.parse(Buffer.from(await f.sign(),'base64url'));
 const bad=[null,'', '%%%', 'a'.repeat(40001),encode({...good,v:2}),encode({...good,alg:'HS256'}),encode({...good,payload:{...good.payload,extra:true}}),encode({...good,signature:'abc'}),encode({...good,payload:{...good.payload,expectSeq:0}}),encode({...good,payload:{...good.payload,nonce:'not-a-nonce'}})];
 for(const token of bad)assert.equal((await verifyPhoneApproval(f.input(token),f.ports)).code,'phone_invalid_token');
 assert.equal(f.lookups,0);
});
test('wire property order does not change canonical signed payload',async()=>{
 const f=await fixture(),envelope=JSON.parse(Buffer.from(await f.sign(),'base64url'));
 envelope.payload=Object.fromEntries(Object.entries(envelope.payload).reverse());
 assert.equal((await verifyPhoneApproval(f.input(encode(envelope)),f.ports)).ok,true);
});
test('missing changes text, control characters and unexpected nonchanges text refuse',async()=>{
 const f=await fixture();
 for(const payload of [{...base,text:'extra'},{...base,decision:'changes'},{...base,decision:'changes',text:'\u0000'},{...base,decision:'changes',text:'x'.repeat(4001)}])assert.equal((await verifyPhoneApproval({...f.input(await f.sign(payload)),decision:payload.decision,text:payload.text},f.ports)).code,'phone_invalid_token');
});

test('a public key placed in the token never replaces the signed ledger key',async()=>{
 const trusted=await fixture(),attacker=await fixture();
 const forged=JSON.parse(Buffer.from(await attacker.sign(),'base64url'));
 forged.publicKeyJwk=attacker.publicKeyJwk;
 assert.equal((await verifyPhoneApproval(trusted.input(encode(forged)),trusted.ports)).code,'phone_invalid_signature');
 delete forged.publicKeyJwk;
 assert.equal((await verifyPhoneApproval(trusted.input(encode(forged)),trusted.ports)).code,'phone_invalid_signature');
 const legitimate=JSON.parse(Buffer.from(await trusted.sign(),'base64url'));
 legitimate.publicKeyJwk=attacker.publicKeyJwk; legitimate.ignoredMetadata={source:'attacker-controlled'};
 assert.equal((await verifyPhoneApproval(trusted.input(encode(legitimate)),trusted.ports)).ok,true);
});

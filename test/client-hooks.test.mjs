import test from 'node:test';
import assert from 'node:assert/strict';
import {getOptionalClientHooks} from '../src/client-hooks.mjs';

test('missing or nonfunction hooks stay absent without manufacturing success',()=>{
  for(const input of [undefined,{}, {clientAdapter:null,updateModule:null},
    {clientAdapter:{runStatusCommand:true,doctorChecks:{}},updateModule:{runUpdateCommand:0}}]) {
    const hooks=getOptionalClientHooks(input);
    assert.deepEqual(hooks,{});assert.equal(Object.isFrozen(hooks),true);
  }
});

test('resolution is inert and preserves exact hook arguments, receiver and returned promise',async()=>{
  let calls=0;
  const argv=['--all'],ports={marker:{}},doctorInput={mode:'check-only'};
  const updateInput={action:'check',value:null,fleet:false,force:false};
  const statusResult=Promise.resolve(17),doctorResult=Promise.resolve({checks:[{id:'client',state:'skip',detail:'Offline',next:null}]}),updateResult=Promise.resolve({state:'unavailable',code:1,message:'No release source.'});
  const clientAdapter={
    runStatusCommand(a,p){calls++;assert.equal(this,clientAdapter);assert.equal(a,argv);assert.equal(p,ports);return statusResult;},
    doctorChecks(i){calls++;assert.equal(this,clientAdapter);assert.equal(i,doctorInput);return doctorResult;},
  };
  const updateModule={runUpdateCommand(i,p){calls++;assert.equal(this,updateModule);assert.equal(i,updateInput);assert.equal(p,ports);return updateResult;}};
  const hooks=getOptionalClientHooks({clientAdapter,updateModule});
  assert.equal(calls,0);assert.deepEqual(Object.keys(hooks),['runStatusCommand','doctorChecks','runUpdateCommand']);
  assert.equal(hooks.runStatusCommand(argv,ports),statusResult);
  assert.equal(hooks.doctorChecks(doctorInput),doctorResult);
  assert.equal(hooks.runUpdateCommand(updateInput,ports),updateResult);
  assert.equal(calls,3);assert.equal(await statusResult,17);
});

test('explicit client registration wins over legacy alias and update registration stays separate',()=>{
  const phoneCli={runStatusCommand(){return 3;},doctorChecks(){return {checks:[]};}};
  const clientAdapter={runStatusCommand(){return 7;},runUpdateCommand(){assert.fail('not an update-module binding');}};
  assert.equal(getOptionalClientHooks({phoneCli}).runStatusCommand(),3);
  assert.equal(getOptionalClientHooks({phoneCli,clientAdapter}).runStatusCommand(),7);
  assert.deepEqual(getOptionalClientHooks({phoneCli,clientAdapter:null}),{});
  assert.equal('runUpdateCommand' in getOptionalClientHooks({clientAdapter}),false);
  const hooks=getOptionalClientHooks({clientAdapter:null,updateModule:{runUpdateCommand(){return 11;}}});
  assert.equal(hooks.runUpdateCommand(),11);assert.equal('runStatusCommand' in hooks,false);
});

test('hook failures retain identity and stay with the owner without retry',async()=>{
  const failure=Error('owner failure');let calls=0;
  const hooks=getOptionalClientHooks({clientAdapter:{runStatusCommand(){calls++;throw failure;},doctorChecks(){calls++;return Promise.reject(failure);}}});
  assert.throws(()=>hooks.runStatusCommand(),e=>e===failure);
  await assert.rejects(hooks.doctorChecks(),e=>e===failure);assert.equal(calls,2);
  assert.throws(()=>getOptionalClientHooks({clientAdapter:{get doctorChecks(){throw failure;}}}),e=>e===failure);
});

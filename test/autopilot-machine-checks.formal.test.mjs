import test from 'node:test';
import assert from 'node:assert/strict';
import { calculateCheckCapacity } from '../src/test-suite-queue.mjs';
import { checkMachine, GiB } from './helpers/check-machine.mjs';

test('bounded capacity rule: 1..128 cores, 0..32 GiB, personal and affinity modes, overrides and load boundary',()=>{
  let cases=0;
  for(let count=1;count<=128;count++) for(let memoryGiB=0;memoryGiB<=32;memoryGiB++)
    for(const virtualized of [false,true]) for(const platform of ['linux','darwin']) for(const battery of [false,true]) for(const affinity of [false,true])
      for(const checks of [undefined,1,5]) {
        const personal=platform==='darwin'||battery||!virtualized, usable=personal?Math.max(1,Math.floor(count/2)):count;
        const fromCores=Math.max(1,Math.floor(usable/12)), fromMemory=Math.max(1,Math.floor(memoryGiB/4));
        const calculated=platform==='linux'&&affinity?Math.min(fromCores,fromMemory):1;
        for(const load of [usable,usable+1]) {
          const ports=checkMachine({count,free:memoryGiB*GiB,platform,battery,virtualized,taskset:affinity?'/fake/taskset':null,load}).ports;
          const got=calculateCheckCapacity({checks},ports), chosen=checks??calculated;
          assert.deepEqual([got.usableCores,got.calculatedChecks,got.checks,got.runs,got.coresPerCheck,got.busy],
            [usable,calculated,chosen,2*chosen,Math.max(1,Math.floor(usable/chosen)),load>usable]);
          cases++;
        }
      }
  assert.equal(cases,405504);
});

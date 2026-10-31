import { promisify } from 'node:util';
import { execFile } from 'node:child_process';
const W = process.env.W;
const { changeRun } = await import(W + '/src/workflow-runner.mjs');
const [source, stateDir, clock, request = 'First'] = process.argv.slice(2);
const exec = promisify(execFile);
const ports = {
  execFile: async (file,args,options) => {
    if (file !== 'git') throw Error('No external command except local git is allowed');
    return exec(file,args,{...options,encoding:'utf8'});
  }, stateDir, now: () => Number(clock), env: { HOME: process.env.HOME },
  herdr: async args => {
    if (args[0] !== 'agent' || args[1] !== 'get') throw Error('No native Herdr call allowed');
    throw Object.assign(Error('not ready'), {code:'agent_not_found'});
  },
  sleep: async () => {
    process.send({waiting:true,pid:process.pid});
    await new Promise(resolve => setTimeout(resolve, 60_000));
  }
};
const result = await changeRun({ref:'17',text:request,cwd:source},ports);
process.send({result});
process.disconnect();

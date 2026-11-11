import test from 'node:test';
import assert from 'node:assert/strict';
import {writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture} from './helpers/workflow-runner-fixture.mjs';
const {stepDone, approveRun} = await import(process.env.PDD_DESCRIPTION_RUNNER || '../src/workflow-runner.mjs');

const classic = 'GraphQL: Projects (classic) is being deprecated in favor of the new Projects experience (repository.pullRequest.projectCards)';
const ok = result => assert.equal(result.exitCode, 0, result.message);
async function published(t) {
  const f = await fixture(t, {agent: 'codex'}), exec = f.ports.execFile;
  f.patches = []; f.legacyEdits = 0;
  f.ports.execFile = async (file, args, options) => {
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'edit') {
      f.legacyEdits++;
      return {code: 1, stdout: '', stderr: classic};
    }
    if (file === 'gh' && args[0] === 'api' && args.includes('PATCH')) {
      f.patches.push({args, input: options.input});
      if (f.failure) return f.failure();
    }
    return exec(file, args, options);
  };
  ok(await f.run());
  f.done = (step, summary = 'Synthetic regression step') => stepDone({step, summary, cwd: f.record().root}, f.agentPorts());
  ok(await f.done('scope'));
  ok(await approveRun({ref: '17', cwd: f.source, said: 'Synthetic approval for isolated native test.'}, f.ports));
  writeFileSync(join(f.record().root, 'value.mjs'), 'export const value = 2;\n');
  for (const step of ['change', 'verify', 'formal']) ok(await f.done(step));
  assert.equal(f.prs.length, 1);
  f.change = () => {
    const root = f.record().root;
    writeFileSync(join(root, 'value.mjs'), 'export const value = 3;\n');
    f.git(root, 'commit', '-qam', 'Source update');
  };
  return f;
}

test('2830: descriptions update when gh pr edit has the Projects classic failure', async t => {
  const f = await published(t);
  f.change();
  const summary = 'Multiline description: "quotes", café 😀 and $literal\nSecond line: `code` and \\backslash';
  const result = await f.done('formal', summary);
  ok(result);
  assert.equal(f.legacyEdits, 0, 'PR descriptions must bypass the Projects classic query');
  assert.equal(f.patches.length, 2, 'Pending and final descriptions both use REST');
  for (const patch of f.patches) {
    assert.deepEqual(patch.args, ['api', '--hostname', 'github.com', '--method', 'PATCH', 'repos/example/project/pulls/23', '--input', '-']);
    assert.deepEqual(Object.keys(JSON.parse(patch.input)), ['body']);
  }
  const body = JSON.parse(f.patches.at(-1).input).body;
  assert.equal(body, f.prs[0].body, 'The entire body survives JSON stdin transport');
  assert.ok(body.includes(summary.split('\n')[0]));
  assert.ok(body.includes(summary.split('\n')[1]));
  assert.ok(body.includes('\n'));
});

for (const mode of ['returned exit', 'thrown stderr', 'thrown message']) {
  test(`2830: ${mode} preserves a safe gh diagnostic and retry before any source push`, async t => {
    const f = await published(t), previous = f.prs[0].body, pushes = f.pushes.length;
    f.change();
    const token = 'ghp_abcdefghijklmnopqrstuvwxyz0123456789ABCD';
    const diagnostic = `\x1b[31mgh: description permission denied\x1b[0m\t${token}\r\nsecond diagnostic line`;
    f.failure = () => {
      if (mode === 'returned exit') return {code: 1, stdout: '', stderr: diagnostic};
      if (mode === 'thrown stderr') throw Object.assign(Error('Command failed'), {code: 1, stderr: diagnostic});
      throw Object.assign(Error(diagnostic), {code: 1});
    };
    const result = await f.done('formal');
    assert.equal(result.exitCode, 1);
    assert.match(result.message, /description permission denied/);
    assert.match(result.message, /workflow done formal/);
    assert.doesNotMatch(result.message, /ghp_|\x1b|second diagnostic line/);
    assert.ok(result.message.split('\n').some(line => line.includes('description permission denied') && line.includes('workflow done formal')));
    assert.equal(f.pushes.length, pushes, 'Failed pending update cannot push new source');
    assert.equal(f.prs[0].body, previous);
  });
}

test('2830: rejected final REST update keeps publication pending and names gh and retry', async t => {
  const f = await published(t), exec = f.ports.execFile;
  f.change();
  let updates = 0;
  f.ports.execFile = async (file, args, options) => {
    if (file === 'gh' && args[0] === 'api' && args.includes('PATCH') && ++updates === 2)
      return {code: 1, stderr: 'gh: final description rejected (HTTP 403)', stdout: ''};
    return exec(file, args, options);
  };
  const pushes = f.pushes.length, result = await f.done('formal');
  assert.equal(result.exitCode, 1);
  assert.match(result.message, /final description rejected \(HTTP 403\)/);
  assert.match(result.message, /workflow done formal/);
  assert.match(result.message, /Source was pushed; the PR stays publication-pending/);
  assert.equal(f.pushes.length, pushes + 1);
  assert.match(f.prs[0].body, /publication-pending/);
});

test('2830: advertised retry restores code approval after the run enters code', async t => {
  const {prepared} = await import('./helpers/workflow-prompt-reentry-fixture.mjs');
  const f = await prepared(t, {code:false, realRemote:true});
  ok(await approveRun({ref:'17',cwd:f.source,said:'Publish PR 1 and stop.'},f.ports));
  const baseExec = f.ports.execFile;
  const exec = async (file,args,options) => {
    const result = await baseExec(file,args,options);
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'view' && args.at(-1) === 'body,headRefOid') {
      const view = JSON.parse(result.stdout); view.headRefOid = f.prs[0].headRefOid; return {...result, stdout:JSON.stringify(view)};
    }
    return result;
  };
  f.ports.execFile = async (file,args,options) => {
    if (file === 'gh' && args[0] === 'api' && args.includes('PATCH') && options.input.includes('Make the code PR now'))
      return {code:1,stderr:'gh: approval update refused',stdout:''};
    return exec(file,args,options);
  };
  const gateBefore = f.record().gate;
  const out = await approveRun({ref:'17',cwd:f.source,said:'Make the code PR now.'},f.ports);
  ok(out); assert.match(out.message,/Retry: .*workflow approve 17/);
  const before = f.record(), body = f.prs[0].body;
  assert.equal(before.areas[before.area].name,'code');
  assert.doesNotMatch(body,/Make the code PR now/);
  const failedAgain = await approveRun({ref:'17',cwd:f.source},f.ports);
  assert.equal(failedAgain.exitCode,1);
  f.ports.execFile = exec;
  f.prs[0].body += '\nNew reviewer text';
  const changedBody = await approveRun({ref:'17',cwd:f.source},f.ports);
  assert.equal(changedBody.exitCode,1); assert.match(changedBody.message,/description or head changed/);
  assert.ok(f.prs[0].body.endsWith('New reviewer text'));
  f.prs[0].body = body;
  const head = f.prs[0].headRefOid; f.prs[0].headRefOid = 'a'.repeat(40);
  const changedHead = await approveRun({ref:'17',cwd:f.source},f.ports);
  assert.equal(changedHead.exitCode,1); assert.equal(f.prs[0].body,body);
  f.prs[0].headRefOid = head;
  const save = record => writeFileSync(join(record.runDir,'status.json'),JSON.stringify(record));
  for (const state of ['cancelled','completed']) {
    save({...before,state});
    const edits = f.edits.length;
    const ended = await approveRun({ref:'17',cwd:f.source},f.ports);
    assert.equal(ended.exitCode,1); assert.equal(f.edits.length,edits);
    save(before);
  }
  let changed = false;
  f.ports.execFile = async (file,args,options) => {
    const result = await exec(file,args,options);
    if (!changed && file === 'gh' && args[0] === 'pr' && args[1] === 'view' && args.at(-1) === 'body,headRefOid') {
      changed = true; const record = f.record(); record.pr1DescriptionRecovery.head = 'b'.repeat(40); save(record);
    }
    return result;
  };
  const edits = f.edits.length;
  const raced = await approveRun({ref:'17',cwd:f.source},f.ports);
  assert.equal(raced.exitCode,1); assert.equal(f.edits.length,edits);
  save(before); f.ports.execFile = exec;
  save({...before, gate: gateBefore});
  const interrupted = await approveRun({ref:'17',cwd:f.source},f.ports);
  ok(interrupted);
  const recovered = f.record();
  assert.deepEqual(recovered.gate, gateBefore); assert.equal(recovered.area, before.area);
  assert.deepEqual(recovered.decisions, before.decisions); assert.deepEqual(recovered.chats, before.chats);
  f.prs[0].body = body; save(before);
  const retried = await approveRun({ref:'17',cwd:f.source},f.ports);
  ok(retried); assert.match(f.prs[0].body,/Make the code PR now/);
  const after = f.record();
  assert.equal(after.area,before.area); assert.equal(after.branch,before.branch);
  assert.deepEqual(after.decisions,before.decisions); assert.deepEqual(after.chats,before.chats);
});

test('2830: unavailable approval refresh keeps the gate retryable', async t => {
  const {prepared} = await import('./helpers/workflow-prompt-reentry-fixture.mjs');
  const f = await prepared(t, {code:false, realRemote:true});
  ok(await approveRun({ref:'17',cwd:f.source,said:'Publish PR 1 and stop.'},f.ports));
  const exec = f.ports.execFile;
  f.ports.execFile = async (file,args,options) => {
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'view' && args.at(-1) === 'body,headRefOid')
      throw Error('gh: cannot read PR');
    return exec(file,args,options);
  };
  const first = await approveRun({ref:'17',cwd:f.source,said:'Make the code PR now.'},f.ports);
  assert.equal(first.exitCode,1); assert.match(first.message,/workflow approve 17 --said -/); assert.doesNotMatch(first.message,/saved approval remains usable/);
  const before = f.record(); assert.equal(before.gate.kind,'ask-code');
  assert.equal(f.git(before.root, 'branch', '--show-current'), before.pr[0].branch);
  const approvalCount = before.decisions.length, chats = before.chats.length;
  f.ports.execFile = exec;
  const retry = await approveRun({ref:'17',cwd:f.source,said:'Make the code PR now.'},f.ports);
  ok(retry);
  const after = f.record(); assert.equal(after.areas[after.area].name,'code');
  assert.equal(after.decisions.length,approvalCount + 1); assert.equal(after.chats.length,chats + 1);
  assert.match(f.prs[0].body,/Make the code PR now/);
});

for (const field of ['body', 'headRefOid']) {
  test(`2830: initial approval update refuses a changed remote ${field}`, async t => {
    const {prepared} = await import('./helpers/workflow-prompt-reentry-fixture.mjs');
    const f = await prepared(t, {code:false, realRemote:true});
    ok(await approveRun({ref:'17',cwd:f.source,said:'Publish PR 1 and stop.'},f.ports));
    const exec = f.ports.execFile; let views = 0, patches = 0;
    f.ports.execFile = async (file,args,options) => {
      if (file === 'gh' && args[0] === 'pr' && args[1] === 'view' && args.at(-1) === 'body,headRefOid') {
        if (++views === 2) {
          if (field === 'body') f.prs[0].body += '\nReviewer edit';
          else f.prs[0].headRefOid = 'a'.repeat(40);
        }
        const result = await exec(file,args,options);
        const view = JSON.parse(result.stdout); view.headRefOid = f.prs[0].headRefOid;
        return {...result, stdout:JSON.stringify(view)};
      }
      if (views >= 2 && file === 'gh' && args[0] === 'api' && args.includes('PATCH')) patches++;
      return exec(file,args,options);
    };
    const result = await approveRun({ref:'17',cwd:f.source,said:'Make the code PR now.'},f.ports);
    ok(result); assert.match(result.message,/description or head changed/); assert.equal(patches,0);
    if (field === 'body') assert.match(f.prs[0].body,/Reviewer edit/);
    else assert.equal(f.prs[0].headRefOid,'a'.repeat(40));
  });
}

test('2830: failed draft confirmation after saving the code decision retains description recovery', async t => {
  const {prepared} = await import('./helpers/workflow-prompt-reentry-fixture.mjs');
  const f = await prepared(t, {code:false, realRemote:true});
  ok(await approveRun({ref:'17',cwd:f.source,said:'Publish PR 1 and stop.'},f.ports));
  const record = f.record(); record.draft = true; f.prs[0].isDraft = true;
  writeFileSync(join(record.runDir,'status.json'),JSON.stringify(record));
  const exec = f.ports.execFile; let failed = false;
  f.ports.execFile = async (file,args,options) => {
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'view' && args.at(-1) === 'number,url,isDraft') {
      if (!failed && f.record().decisions.some(d => d.text === 'Make the code PR now.')) {
        failed = true; throw Error('gh: draft confirmation unavailable');
      }
      return {stdout:JSON.stringify({number:f.prs[0].number,url:f.prs[0].url,isDraft:true})};
    }
    const result = await exec(file,args,options);
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'view' && args.at(-1) === 'body,headRefOid') {
      const view = JSON.parse(result.stdout); view.headRefOid = f.prs[0].headRefOid;
      return {...result,stdout:JSON.stringify(view)};
    }
    return result;
  };
  const result = await approveRun({ref:'17',cwd:f.source,said:'Make the code PR now.'},f.ports);
  ok(result); assert.equal(failed,true); assert.match(result.message,/Retry: .*workflow approve 17/);
  const before = f.record(); assert.ok(before.pr1DescriptionRecovery);
  const retry = await approveRun({ref:'17',cwd:f.source},f.ports);
  ok(retry); assert.match(f.prs[0].body,/Make the code PR now/);
  const after = f.record(); assert.deepEqual(after.decisions,before.decisions);
  assert.equal(after.area,before.area); assert.equal(after.branch,before.branch); assert.deepEqual(after.chats,before.chats);
});

import "./helpers/test-home.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {createHash, randomUUID} from "node:crypto";
import {existsSync, mkdirSync, readFileSync, realpathSync, renameSync, writeFileSync} from "node:fs";
import {join} from "node:path";
import {fixture, packageRoot} from "./helpers/workflow-runner-fixture.mjs";
import {automaticFixture} from "./helpers/autopilot-run-base-fixture.mjs";
import {healthyMachine} from "./helpers/healthy-machine.mjs";
import {isolatedCheckCapacity} from "./helpers/check-machine.mjs";
import {createGithubRepoFake} from "./helpers/github-repo-fake.mjs";
import {runAutopilotLauncher, tickAutopilot} from "../src/autopilot-launcher.mjs";

const repo = "example/project", coordinatorId = "park-owner", machine = "park-machine";
function addClaimEra(github, at) {
  const comment = github.claim(17, {coordinatorId, machine});
  const issue = github.issues.get(17);
  const eventId = issue.timeline.filter(event => event.label === "pdd:working").at(-1).id;
  const bodyRecord = JSON.parse(/```json\n([\s\S]*?)\n```/.exec(comment.body)[1]);
  github.editComment(17, comment.id, `Autopilot claim.\n\n\`\`\`json\n${JSON.stringify({...bodyRecord, lastSeen:new Date(at).toISOString()})}\n\`\`\``);
  return {commentId:comment.id, eventId};
}

test("3157: public issue release cleans a pending archived automatic claim", async t => {
  const f = await automaticFixture(t);
  assert.equal((await f.begin()).exitCode, 0);
  const pending = f.record(), github = createGithubRepoFake({repository:pending.repo, owner:"example", issues:18, now:()=>f.clock});
  const comment = github.claim(17, {coordinatorId:pending.automaticOrigin.coordinatorId, machine:pending.automaticOrigin.machine});
  const eventId = github.issues.get(17).timeline.filter(event => event.label === "pdd:working").at(-1).id;
  github.editComment(17, comment.id, `Autopilot claim.\n\n\`\`\`json\n${JSON.stringify({
    repository:pending.repo, coordinatorId:pending.automaticOrigin.coordinatorId,
    machine:pending.automaticOrigin.machine, labelEventId:eventId, lastSeen:new Date(f.clock).toISOString(),
  })}\n\`\`\``);
  github.label(17, "pdd:stuck");
  pending.automaticOrigin.claim = {commentId:comment.id, labelEventId:eventId};
  pending.state = "cancelled";
  pending.cancelled = {state:"cancelled", at:f.clock};
  pending.claimRelease = {state:"pending", reason:"cancel", at:f.clock};
  pending.gate = null;
  pending.chats = [];
  pending.layout = {phase:"closed"};
  writeFileSync(join(pending.runDir, "status.json"), JSON.stringify(pending));
  const archive = `${pending.runDir}-cancelled-${pending.runId.slice(0,8)}`;
  renameSync(pending.runDir, archive);
  mkdirSync(pending.runDir);
  const direct = {...pending, runId:randomUUID(), runDir:pending.runDir};
  delete direct.automaticOrigin;
  delete direct.claimRelease;
  writeFileSync(join(direct.runDir, "status.json"), JSON.stringify(direct));
  const allocation = join(pending.commonDir, "pdd", "worktree-assignments", "issues", "17.json");
  assert.ok(existsSync(allocation), "the archived run still owns its local issue allocation");

  const originalExec = f.ports.execFile;
  const fakeExec = async (file, args, options={}) => file === "gh" && args[0] === "api"
    ? github.gh(args, options) : originalExec(file, args, options);
  const ports = {...healthyMachine, ...f.ports, stateRoot:f.automaticPorts.autopilotStateRoot,
    checkCapacityPorts:isolatedCheckCapacity(f.base), authority:{read:async()=>({authority:"trusted"})}, execFile:fakeExec,
    run:async (file,args,options={}) => {
      if (file === "gh" && args[0] === "api") return fakeExec(file,args,options);
      if (file === "gh" && args[0] === "repo") return {code:0, stdout:JSON.stringify({nameWithOwner:pending.repo,url:`https://github.com/${pending.repo}`,defaultBranchRef:{name:"main"}}), stderr:""};
      return {code:0,...await f.ports.execFile(file,args,options)};
    },
    reconcileDependencyIntake:async()=>({eligible:[],claims:[],groups:[],queued:[],skipped:[]}),
    sendDigest:async()=>({exitCode:0}),
  };
  const result = await runAutopilotLauncher({command:"release", cwd:f.source, env:f.ports.env, issues:["17"]}, ports);
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(JSON.parse(readFileSync(join(archive, "status.json"), "utf8")).claimRelease, undefined);
  const unchanged = JSON.parse(readFileSync(join(direct.runDir, "status.json"), "utf8"));
  assert.equal(unchanged.runId, direct.runId, "the non-automatic current record stays untouched");
  assert.equal(Object.hasOwn(unchanged, "automaticOrigin"), false);
  assert.equal(existsSync(allocation), false, "the archived run released its own local allocation");
  assert.deepEqual(github.issues.get(17).labels, []);
});

for (const firstClaimPresent of [true, false]) test(`3157: public no-run release preserves replacement when first current claim is ${firstClaimPresent ? "present" : "absent"}`, async t => {
  const f = await fixture(t, {agent:"codex"});
  const now = () => f.clock;
  const github = createGithubRepoFake({repository:repo, owner:"example", issues:18, now});
  if (firstClaimPresent) {
    addClaimEra(github, f.clock);
    github.label(17, "pdd:stuck");
  } else {
    github.label(17, "pdd:stuck");
  }
  const originalExec = f.ports.execFile;
  let replacement = null, injected = false; const deletions = [];
  const fakeExec = async (file, args, options={}) => {
    if (file === "gh" && args[0] === "api") {
      const path = args.find(value => value.includes("/labels/"));
      const deleting = args.includes("--method") && args[args.indexOf("--method") + 1] === "DELETE";
      if (deleting && path) deletions.push(path.split("/labels/").at(-1));
      const result = await github.gh(args, options);
      if (deleting && path?.endsWith("/labels/pdd%3Astuck") && !injected) {
        injected = true;
        if (github.issues.get(17).labels.includes("pdd:working")) github.unlabel(17, "pdd:working");
        replacement = addClaimEra(github, f.clock);
        github.label(17, "pdd:stuck");
      }
      return result;
    }
    return originalExec(file, args, options);
  };
  const stateFolder = join(f.ports.env.HOME, ".local", "state", "pdd", "autopilot");
  mkdirSync(stateFolder, {recursive:true});
  const root = realpathSync(f.source), id = createHash("sha256").update(root).digest("hex").slice(0,20);
  const stateFile = join(stateFolder, `${id}.json`);
  writeFileSync(join(f.source, "pdd.json"), JSON.stringify({autopilot:{mode:"auto",trust:[]}}));
  writeFileSync(stateFile, JSON.stringify({enabled:true, defaultBranch:"main", baseBranch:"main", stateFile,
    cwd:f.source, repo, packageRoot, runs:1, coordinatorId, machine, activatedAt:1,
    agent:{id:"codex",kind:"codex",command:"codex"}, environment:f.ports.env, retryAt:f.clock + 86400000}));
  const ports = {...healthyMachine, ...f.ports, checkCapacityPorts:isolatedCheckCapacity(f.base),
    authority:{read:async()=>({authority:"trusted"})},
    execFile:fakeExec,
    run:async (file,args,options={}) => {
      if (file === "gh" && args[0] === "api") return fakeExec(file, args, options);
      if (file === "gh" && args[0] === "repo") return {code:0, stdout:JSON.stringify({nameWithOwner:repo,url:`https://github.com/${repo}`,defaultBranchRef:{name:"main"}}), stderr:""};
      return {code:0,...await f.ports.execFile(file,args,options)};
    },
    reconcileDependencyIntake:async()=>({eligible:[],claims:[],groups:[],queued:[],skipped:[]}),
    sendDigest:async()=>({exitCode:0}),
  };
  const result = await runAutopilotLauncher({command:"release", cwd:f.source, env:f.ports.env, issues:["17"]}, ports);
  assert.equal(injected, true, "release removed stale stuck label and takeover was injected after it");
  assert.ok(replacement);
  assert.equal(result.exitCode, 1, result.message);
  assert.deepEqual(deletions, ["pdd%3Astuck"], "the release stops deleting labels after a replacement is observed");
  assert.deepEqual(github.issues.get(17).labels, ["pdd:working", "pdd:stuck"], "both replacement labels stay intact");
  assert.ok(github.issues.get(17).comments.some(comment => comment.id === replacement.commentId), "replacement claim comment remains");
  assert.ok(github.issues.get(17).timeline.some(event => event.id === replacement.eventId && event.label === "pdd:working"), "replacement era event remains");
});


test("3157: public release keeps a concurrent stop and fresh replacement cache", async t => {
  const f = await fixture(t, {agent:"codex"});
  const now = () => f.clock;
  const github = createGithubRepoFake({repository:repo, owner:"example", issues:18, now});
  const first = addClaimEra(github, f.clock);
  github.label(17, "pdd:stuck");
  const stateFolder = join(f.ports.env.HOME, ".local", "state", "pdd", "autopilot");
  mkdirSync(stateFolder, {recursive:true});
  const root = realpathSync(f.source), id = createHash("sha256").update(root).digest("hex").slice(0,20);
  const stateFile = join(stateFolder, id + ".json");
  const issue = "https://github.com/" + repo + "/issues/17";
  const cached = {issue, owner:coordinatorId, coordinatorId, machine, active:true,
    commentId:String(first.commentId), labelEventId:String(first.eventId)};
  writeFileSync(join(f.source, "pdd.json"), JSON.stringify({autopilot:{mode:"auto",trust:[]}}));
  writeFileSync(stateFile, JSON.stringify({enabled:true, defaultBranch:"main", baseBranch:"main", stateFile,
    cwd:f.source, repo, packageRoot, runs:1, coordinatorId, machine, controlRevision:"before-release", activatedAt:1,
    agent:{id:"codex",kind:"codex",command:"codex"}, environment:f.ports.env, retryAt:f.clock + 86400000,
    githubIntake:{at:f.clock,eligible:[],groups:[],claims:[cached]}, parkedNumbers:[17]}));
  const originalExec = f.ports.execFile;
  let ports, injected = false, workingDeleted = false, replacement, stoppedRevision;
  const fakeExec = async (file, args, options={}) => {
    if (file === "gh" && args[0] === "api") {
      const endpoint = args.find(value => /^repos\//.test(value));
      const method = args.includes("--method") ? args[args.indexOf("--method") + 1] : "GET";
      const result = await github.gh(args, options);
      if (method === "DELETE" && endpoint?.endsWith("/labels/pdd%3Aworking")) workingDeleted = true;
      if (!injected && workingDeleted && method === "GET" && endpoint === "repos/" + repo + "/issues/17") {
        injected = true;
        const stopped = await runAutopilotLauncher({command:"stop", cwd:f.source, env:f.ports.env}, ports);
        assert.equal(stopped.exitCode, 0, stopped.message);
        replacement = addClaimEra(github, f.clock);
        github.label(17, "pdd:stuck");
        const latest = JSON.parse(readFileSync(stateFile, "utf8"));
        stoppedRevision = latest.controlRevision;
        latest.githubIntake = {...latest.githubIntake, claims:[{issue, owner:coordinatorId, coordinatorId, machine, active:true,
          commentId:String(replacement.commentId), labelEventId:String(replacement.eventId)}]};
        latest.parkedNumbers = [17, 99];
        writeFileSync(stateFile, JSON.stringify(latest));
      }
      return result;
    }
    return originalExec(file, args, options);
  };
  ports = {...healthyMachine, ...f.ports, checkCapacityPorts:isolatedCheckCapacity(f.base),
    authority:{read:async()=>({authority:"trusted"})}, execFile:fakeExec,
    run:async (file,args,options={}) => {
      if (file === "gh" && args[0] === "api") return fakeExec(file, args, options);
      if (file === "systemctl" || file === "launchctl") return {code:0, stdout:"", stderr:""};
      if (file === "gh" && args[0] === "repo") return {code:0, stdout:JSON.stringify({nameWithOwner:repo,url:"https://github.com/" + repo,defaultBranchRef:{name:"main"}}), stderr:""};
      return {code:0,...await f.ports.execFile(file,args,options)};
    },
    reconcileDependencyIntake:async()=>({eligible:[],claims:[],groups:[],queued:[],skipped:[]}),
    sendDigest:async()=>({exitCode:0}),
  };
  const result = await runAutopilotLauncher({command:"release", cwd:f.source, env:f.ports.env, issues:["17"]}, ports);
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(injected, true, "the concurrent stop ran after remote release and before cache pruning");
  assert.ok(replacement);
  const latest = JSON.parse(readFileSync(stateFile, "utf8"));
  assert.equal(latest.enabled, false, "release does not restore enabled after stop");
  assert.equal(latest.controlRevision, stoppedRevision, "release keeps the stop control revision");
  assert.notEqual(latest.controlRevision, "before-release");
  assert.deepEqual(latest.githubIntake.claims.map(claim => [claim.commentId, claim.labelEventId]),
    [[String(replacement.commentId), String(replacement.eventId)]], "a fresh replacement cache is not pruned by issue number");
  assert.deepEqual(latest.parkedNumbers, [17, 99], "number-only reservations stay for ordinary reconciliation");
  assert.deepEqual(github.issues.get(17).labels, ["pdd:working", "pdd:stuck"], "the replacement era remains remote");
});


const releaseTickCases = [
  {name:"the exact cached era", invocation:"complete"},
  {name:"an empty latest cache", invocation:"complete", emptyLatestCache:true},
  {name:"an absent invocation cache", invocation:"absent"},
  {name:"an incomplete invocation cache", invocation:"incomplete"},
];
for (const {name, invocation, emptyLatestCache = false} of releaseTickCases) test("3157: public release blocks an older tick from restoring " + name, async t => {
  const f = await fixture(t, {agent:"codex"});
  const now = () => f.clock;
  const github = createGithubRepoFake({repository:repo, owner:"example", issues:18, now});
  const first = addClaimEra(github, f.clock);
  github.label(17, "pdd:stuck");
  const stateFolder = join(f.ports.env.HOME, ".local", "state", "pdd", "autopilot");
  mkdirSync(stateFolder, {recursive:true});
  const root = realpathSync(f.source), id = createHash("sha256").update(root).digest("hex").slice(0,20);
  const stateFile = join(stateFolder, id + ".json");
  const issue = "https://github.com/" + repo + "/issues/17";
  const cached = {issue, owner:coordinatorId, coordinatorId, machine, active:false,
    commentId:String(first.commentId), labelEventId:String(first.eventId)};
  const incomplete = {issue, owner:coordinatorId, coordinatorId, machine, active:false, commentId:String(first.commentId)};
  const invocationClaims = invocation === "complete" ? [cached] : invocation === "incomplete" ? [incomplete] : null;
  const invocationIntake = invocationClaims && {at:f.clock,eligible:[],groups:[],claims:invocationClaims};
  writeFileSync(join(f.source, "pdd.json"), JSON.stringify({autopilot:{mode:"observe",trust:[]}}));
  writeFileSync(stateFile, JSON.stringify({enabled:true, defaultBranch:"main", baseBranch:"main", stateFile,
    cwd:f.source, repo, packageRoot, runs:1, coordinatorId, machine, controlRevision:"before-release", activatedAt:1,
    agent:{id:"codex",kind:"codex",command:"codex"}, environment:f.ports.env, recipeDelivered:true,
    ...(invocationIntake ? {githubIntake:invocationIntake} : {}), parkedNumbers:[17,99]}));
  let tickReached, continueTick, emptied = false, intakeRead = false, tickPaused = false;
  const tickWithClaim = new Promise(resolve => { tickReached = resolve; });
  const tickMayFinish = new Promise(resolve => { continueTick = resolve; });
  const originalExec = f.ports.execFile;
  const fakeExec = async (file, args, options={}) => {
    if (file === "gh" && args[0] === "api") {
      const result = await github.gh(args, options);
      const endpoint = args.find(value => /^repos\//.test(value));
      const method = args.includes("--method") ? args[args.indexOf("--method") + 1] : "GET";
      if (emptyLatestCache && !emptied && method === "DELETE" && endpoint?.endsWith("/labels/pdd%3Aworking")) {
        emptied = true;
        const latest = JSON.parse(readFileSync(stateFile, "utf8"));
        latest.githubIntake = {...latest.githubIntake, claims:[]};
        writeFileSync(stateFile, JSON.stringify(latest));
      }
      return result;
    }
    return originalExec(file, args, options);
  };
  const ports = {...healthyMachine, ...f.ports, checkCapacityPorts:isolatedCheckCapacity(f.base),
    authority:{read:async()=>({authority:"trusted"})}, execFile:fakeExec,
    run:async (file,args,options={}) => {
      if (file === "gh" && args[0] === "api") return fakeExec(file, args, options);
      if (file === "gh" && args[0] === "repo") return {code:0, stdout:JSON.stringify({nameWithOwner:repo,url:"https://github.com/" + repo,defaultBranchRef:{name:"main"}}), stderr:""};
      return {code:0,...await f.ports.execFile(file,args,options)};
    },
    tidyRuns:async()=>{}, listRuns:async()=>{
      if (!tickPaused && intakeRead) {
        tickPaused = true;
        tickReached();
        await tickMayFinish;
      }
      return [];
    }, readRunProgress:async()=>[], readEnvironmentWaits:async()=>[],
    reconcileDependencyIntake:async()=>{ intakeRead = true; return {eligible:[],claims:[cached],groups:[],queued:[],skipped:[]}; },
    queryIssues:async()=>({status:304}), sendDigest:async()=>({exitCode:0}), sendAlert:async()=>({exitCode:0}),
    readAttention:async()=>[], warn:()=>{},
  };
  const ticking = tickAutopilot(stateFile, ports);
  await tickWithClaim;
  const released = await runAutopilotLauncher({command:"release", cwd:f.source, env:f.ports.env, issues:["17"]}, ports);
  assert.equal(released.exitCode, 0, released.message);
  assert.equal(emptied, emptyLatestCache, "the controlled cache transition ran only for the empty-cache ordering");
  const expectedClaims = emptyLatestCache || invocation === "complete" ? [] : invocationClaims ?? [];
  const releasedState = JSON.parse(readFileSync(stateFile, "utf8"));
  assert.deepEqual(releasedState.githubIntake?.claims ?? [], expectedClaims, "release only prunes a complete exact cached era before the held tick continues");
  continueTick();
  await ticking;
  const latest = JSON.parse(readFileSync(stateFile, "utf8"));
  assert.deepEqual(latest.githubIntake?.claims ?? [], expectedClaims, "an older tick must not restore the released cache");
  assert.notEqual(releasedState.controlRevision, "before-release", "the successful release invalidates an older tick control snapshot");
  assert.equal(latest.controlRevision, releasedState.controlRevision, "the older tick cannot replace the released control revision");
  assert.deepEqual(latest.parkedNumbers, [17,99], "the release does not replace unrelated cached reservations");
});

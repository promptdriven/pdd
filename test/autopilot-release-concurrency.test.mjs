import "./helpers/test-home.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {createHash} from "node:crypto";
import {mkdirSync, realpathSync, writeFileSync} from "node:fs";
import {join} from "node:path";
import {fixture, packageRoot} from "./helpers/workflow-runner-fixture.mjs";
import {healthyMachine} from "./helpers/healthy-machine.mjs";
import {isolatedCheckCapacity} from "./helpers/check-machine.mjs";
import {createGithubRepoFake} from "./helpers/github-repo-fake.mjs";
import {runAutopilotLauncher} from "../src/autopilot-launcher.mjs";

const repo = "example/project", coordinatorId = "park-owner", machine = "park-machine";
function addClaimEra(github, at) {
  const comment = github.claim(17, {coordinatorId, machine});
  const issue = github.issues.get(17);
  const eventId = issue.timeline.filter(event => event.label === "pdd:working").at(-1).id;
  const bodyRecord = JSON.parse(/```json\n([\s\S]*?)\n```/.exec(comment.body)[1]);
  github.editComment(17, comment.id, `Autopilot claim.\n\n\`\`\`json\n${JSON.stringify({...bodyRecord, lastSeen:new Date(at).toISOString()})}\n\`\`\``);
  return {commentId:comment.id, eventId};
}
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

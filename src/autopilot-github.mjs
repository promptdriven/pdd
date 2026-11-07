// Generated from prompts/cli/autopilot-github.prompt.md (sha256: 292eb70196bd68fa81e102743d56ef05b64efc37fd9a48d383b4c758d0cbb44a).
import { execFile } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { resolveWorkflowRepository } from './workflow-github.mjs';

const MODES = ['off', 'observe', 'auto'];
const REFUSED = [403, 409, 422];
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const success = status => Number.isInteger(status) && status >= 200 && status < 300;
const clean = value => String(value).replace(/[\x00-\x1f\x7f]/g, '');
// The same JSON value, whatever the key order.
const canonical = value => JSON.stringify(value ?? null, (key, item) => object(item)
  ? Object.fromEntries(Object.keys(item).sort().map(name => [name, item[name]])) : item);
const modeOf = value => object(value) && MODES.includes(value.mode) ? value.mode : 'off';
const namesOf = value => object(value) && Array.isArray(value.trust) ? value.trust.filter(name => typeof name === 'string' && name.trim()) : [];
const trustKey = value => [...new Set(namesOf(value).map(name => name.toLowerCase()))].sort().join('\n');
const shown = value => namesOf(value).map(clean).join(', ') || '(none)';
const segments = branch => branch.split('/').map(encodeURIComponent).join('/');
class Stop extends Error {}

const execute = (file, args, { cwd, input }) => new Promise((resolve, reject) => {
  const child = execFile(file, args, { cwd, encoding: 'utf8', shell: false, timeout: 15000, maxBuffer: 8 * 1024 * 1024 }, (error, stdout, stderr) => {
    if (error) { error.stdout = stdout; error.stderr = stderr; reject(error); }
    else resolve({ stdout, stderr });
  });
  child.stdin?.on('error', () => {});
  child.stdin?.end(input);
});
const parse = text => { try { return JSON.parse(text); } catch { return null; } };

// gh owns the sign-in; pdd adds no credentials.
function nativeGithub(root, exec) {
  return {
    repository: () => resolveWorkflowRepository({ cwd: root }, { execFile: exec }),
    async request({ method, path, body }) {
      const args = ['api', '--method', method, '-H', 'Accept: application/vnd.github+json', path, ...(body === undefined ? [] : ['--input', '-'])];
      try { return { status: 200, body: parse((await exec('gh', args, { cwd: root, input: body === undefined ? undefined : JSON.stringify(body) })).stdout) }; }
      catch (error) {
        const status = Number(/\(HTTP (\d{3})\)/.exec(String(error?.stderr ?? ''))?.[1]);
        if (!Number.isInteger(error?.code) || !status) throw Error('no HTTP answer');
        return { status, body: parse(error.stdout) };
      }
    },
  };
}

async function context(cwd, ports) {
  const exec = ports.execFile ?? execute;
  const root = String((await exec('git', ['rev-parse', '--show-toplevel'], { cwd })).stdout).trim();
  if (!root) throw Error('no Git root');
  let config = {};
  try { config = JSON.parse(readFileSync(join(root, 'pdd.json'), 'utf8')); }
  catch (error) { if (error.code !== 'ENOENT') throw error; }
  if (!object(config)) throw Error('pdd.json is not an object');
  return { root, local: config.autopilot, github: ports.github ?? nativeGithub(root, exec) };
}

function repositoryReason(error) {
  if (error?.code === 'workflow_github_origin_invalid') return 'origin is not a github.com repository';
  if (error?.code === 'workflow_github_command_unavailable') return 'gh is missing or did not answer in time';
  if (/No such remote/i.test(String(error?.detail ?? ''))) return 'this repository has no origin remote';
  return 'GitHub could not be reached or gh is not signed in';
}
async function repositoryOf(github) {
  let repo;
  try { repo = await github.repository(); } catch (error) { throw new Stop(repositoryReason(error)); }
  if (!object(repo) || typeof repo.repository !== 'string' || typeof repo.defaultBranch !== 'string') throw new Stop('GitHub did not name the default branch');
  return repo;
}
async function ask(github, request) {
  try { return await github.request(request); }
  catch { throw new Stop('GitHub could not be reached or gh is not signed in'); }
}
async function readRemote(github, repository, branch) {
  const answer = await ask(github, { method: 'GET', path: `repos/${repository}/contents/pdd.json?ref=${encodeURIComponent(branch)}` });
  if (answer?.status === 404) return { sha: undefined, config: {} };
  if (!success(answer?.status)) throw new Stop(`GitHub did not send pdd.json (HTTP ${answer?.status})`);
  const file = answer.body;
  if (!object(file) || file.type !== 'file' || typeof file.sha !== 'string' || file.encoding !== 'base64' || typeof file.content !== 'string') throw new Stop(`GitHub did not send pdd.json of ${clean(branch)}`);
  let config;
  try { config = JSON.parse(Buffer.from(file.content, 'base64').toString('utf8')); } catch { config = null; }
  if (!object(config)) throw new Stop(`pdd.json on ${clean(branch)} is not a JSON object; fix it on GitHub first`);
  return { sha: file.sha, config };
}
const textFor = (config, local) => `${JSON.stringify({ ...config, autopilot: local }, null, 2)}\n`;
const put = (github, repository, branch, remote, local, message) => ask(github, { method: 'PUT', path: `repos/${repository}/contents/pdd.json`,
  body: { message, content: Buffer.from(textFor(remote.config, local)).toString('base64'), branch, ...(remote.sha ? { sha: remote.sha } : {}) } });

export async function publishAutopilotSettings({ cwd, action, mode, retry } = {}, ports = {}) {
  const again = clean(retry || 'the same pdd autopilot command');
  const notUpdated = reason => ({ state: 'not-updated', message: `pdd.json on GitHub was not updated: ${reason}. This checkout has the new setting. To retry, run ${again}.` });
  try {
    let found;
    try { found = await context(cwd, ports); } catch { return notUpdated('the local pdd.json could not be read'); }
    const { local, github } = found;
    if (!object(local)) return { state: 'skipped', message: '' };
    const { repository, defaultBranch } = await repositoryOf(github);
    const remote = await readRemote(github, repository, defaultBranch);
    if (canonical(remote.config.autopilot) === canonical(local)) return { state: 'current', message: 'pdd.json on GitHub is already up to date.' };
    const message = action === 'mode' ? `Set PDD Autopilot mode to ${clean(mode)}` : 'Update PDD Autopilot trust list';
    const direct = await put(github, repository, defaultBranch, remote, local, message);
    if (success(direct?.status)) {
      const commit = direct.body?.commit;
      const url = typeof commit?.html_url === 'string' ? commit.html_url : typeof commit?.sha === 'string' ? `https://github.com/${repository}/commit/${commit.sha}` : '';
      return { state: 'written', message: `Updated pdd.json on GitHub (${clean(defaultBranch)})${url ? `: ${clean(url)}` : '.'}` };
    }
    if (!REFUSED.includes(direct?.status)) throw new Stop(`GitHub refused the change (HTTP ${direct?.status})`);
    // The default branch wants a PR: the same one-file change goes on a new branch.
    const head = await ask(github, { method: 'GET', path: `repos/${repository}/git/ref/heads/${segments(defaultBranch)}` });
    if (!success(head?.status) || typeof head.body?.object?.sha !== 'string') throw new Stop(`GitHub did not send the head of ${clean(defaultBranch)} (HTTP ${head?.status})`);
    const branch = `pdd/autopilot-settings-${(ports.shortId ?? (() => randomBytes(4).toString('hex')))()}`;
    const created = await ask(github, { method: 'POST', path: `repos/${repository}/git/refs`, body: { ref: `refs/heads/${branch}`, sha: head.body.object.sha } });
    if (!success(created?.status)) throw new Stop(`${clean(defaultBranch)} does not accept a direct change, and GitHub refused the branch ${branch} (HTTP ${created?.status})`);
    const onBranch = await readRemote(github, repository, branch);
    const written = await put(github, repository, branch, onBranch, local, message);
    if (!success(written?.status)) throw new Stop(`${clean(defaultBranch)} does not accept a direct change, and GitHub refused the change on ${branch} (HTTP ${written?.status})`);
    const title = modeOf(local) !== 'off' && modeOf(remote.config.autopilot) === 'off' ? 'Turn on PDD Autopilot' : 'Update PDD Autopilot settings';
    const body = `This PR sets \`autopilot\` in \`pdd.json\`, as \`${again}\` saved it:\n\n\`\`\`json\n${JSON.stringify(local, null, 2)}\n\`\`\`\n\n`
      + `${clean(defaultBranch)} does not accept a direct change. Autopilot workers start from ${clean(defaultBranch)}, so they use this setting only after the merge.\n`;
    const pull = await ask(github, { method: 'POST', path: `repos/${repository}/pulls`, body: { title, head: branch, base: defaultBranch, body } });
    if (!success(pull?.status) || typeof pull.body?.html_url !== 'string') throw new Stop(`branch ${branch} has the change, but GitHub did not open the PR (HTTP ${pull?.status}); open a PR from it to ${clean(defaultBranch)}`);
    return { state: 'pull-request', message: `${clean(defaultBranch)} does not accept a direct change, so pdd opened ${clean(pull.body.html_url)}. Merge it before Autopilot workers use the ${action === 'mode' ? 'new mode' : 'new trust list'}.` };
  } catch (error) {
    return notUpdated(error instanceof Stop ? error.message : 'an unexpected error stopped the update');
  }
}

export async function checkAutopilotSettings({ cwd } = {}, ports = {}) {
  try {
    const { local, github } = await context(cwd, ports);
    const { repository, defaultBranch } = await repositoryOf(github);
    const remote = (await readRemote(github, repository, defaultBranch)).config.autopilot;
    if (modeOf(remote) === modeOf(local) && trustKey(remote) === trustKey(local)) return { state: 'same', message: '' };
    return { state: 'different', message: `Warning: pdd.json on GitHub (${clean(defaultBranch)}) has other Autopilot settings (GitHub: ${modeOf(remote)}, trust ${shown(remote)}; this checkout: ${modeOf(local)}, trust ${shown(local)}). Autopilot workers use the GitHub copy. To update it, run pdd autopilot ${modeOf(local)}.` };
  } catch { return { state: 'unknown', message: '' }; }
}

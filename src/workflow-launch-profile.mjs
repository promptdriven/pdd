// Generated from prompts/cli/workflow-launch-profile.prompt.md (sha256: 368bc6927360a539c3737887f3b69ebdbdf0b99213233e6508453cfd7cca7b05).
import * as nodeFs from 'node:fs';
import { createHash } from 'node:crypto';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { parse } from './vendor/smol-toml/parse.js';

const hash = value => createHash('sha256').update(value).digest('hex');
const namePattern = /^[a-z][a-z0-9_-]{0,24}$/;
const modelValid = value => typeof value === 'string' && value.length > 0 && value === value.trim() && !/^[\-]|[\x00-\x1f\x7f]/.test(value);
const problem = message => Object.assign(Error(message), { code: 'invalid_launch_profile' });
export function launchProfile(run, chat) {
  const saved = chat ? chat.launchProfile : run.launchProfile;
  return { agent: saved?.agent ?? chat?.agent ?? run.agent,
    configDir: saved ? saved.configDir : chat ? chat.configDir ?? null : run.configDir ?? null,
    model: saved?.model ?? null,
    herdrAgentName: saved?.herdrAgentName ?? `pdd-${hash(`${run.repo ?? ''}:${run.runId ?? ''}`).slice(0, 12)}`,
    codexThreads: saved?.codexThreads ?? null };
}
export const chatAgentName = (profile, area, run) => `${profile.herdrAgentName}-${hash(`${run.repo ?? ''}:${run.runId ?? ''}:${area}`).slice(0, 6)}`;
export function validLaunchProfile(value) {
  return value && typeof value === 'object' && !Array.isArray(value)
    && Object.keys(value).length === 5 && ['agent','configDir','model','herdrAgentName','codexThreads'].every(key => Object.hasOwn(value, key))
    && ['codex','claude','gemini','agy'].includes(value.agent)
    && (value.configDir === null || typeof value.configDir === 'string' && value.configDir.length > 0)
    && (value.model === null || modelValid(value.model)) && namePattern.test(value.herdrAgentName)
    && (value.codexThreads === null || value.agent === 'codex' && Number.isSafeInteger(value.codexThreads) && value.codexThreads >= 4);
}
export function selectLaunchProfile({ run, configDir, model, herdrAgentName, codexThreads }, { env = process.env, profileFs = nodeFs } = {}) {
  const profile = launchProfile(run);
  if (configDir !== undefined) profile.configDir = configDir;
  if (model !== undefined) {
    if (!modelValid(model)) throw problem('Use --model with a nonblank model name without controls or a leading dash.');
    profile.model = model;
  }
  if (herdrAgentName !== undefined) {
    if (typeof herdrAgentName !== 'string' || !namePattern.test(herdrAgentName)) throw problem('Use --herdr-agent-name with 1 to 25 lowercase letters, digits, underscores or dashes, starting with a letter.');
    profile.herdrAgentName = herdrAgentName;
  }
  if (codexThreads !== undefined) {
    if (profile.agent !== 'codex' || !['string','number'].includes(typeof codexThreads) || !/^[4-8]$/.test(String(codexThreads))) throw problem('Use --codex-threads with a whole number from 4 through 8 for Codex.');
    profile.codexThreads = Number(codexThreads);
  }
  if (profile.agent === 'codex' && profile.codexThreads !== null) {
    const home = env.HOME || homedir(), raw = profile.configDir;
    const folder = raw === '~' ? home : raw?.startsWith('~/') ? join(home, raw.slice(2)) : raw || join(home, '.codex');
    let source;
    try { source = profileFs.readFileSync(join(folder, 'config.toml'), 'utf8'); }
    catch (error) { if (error.code !== 'ENOENT') throw problem('The selected Codex config.toml cannot be read. Fix it before selecting this launch profile.'); }
    if (source !== undefined) {
      let configured;
      try { configured = parse(source)?.features?.multi_agent_v2?.max_concurrent_threads_per_session; }
      catch { throw problem('The selected Codex config.toml is malformed. Fix it before selecting this launch profile.'); }
      if (configured !== undefined) {
        if (!Number.isSafeInteger(configured) || configured < 1) throw problem('The selected Codex thread limit must be a positive whole number.');
        profile.codexThreads = Math.max(profile.codexThreads, configured);
      }
    }
  }
  if (!validLaunchProfile(profile)) throw problem('The saved launch profile is malformed. Inspect it before starting a chat.');
  return profile;
}

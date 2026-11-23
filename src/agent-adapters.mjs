// Generated from prompts/cli/agent-adapters.prompt.md (sha256: 24a5dbd69ad0cee7b39632558f86b0ade0cce955cc171424166a10fe92c3fe59).
// Thin compatibility adapter composing Layer-0 agent discovery/process helpers with
// local agent config and re-exporting Layer-2 Autopilot step launch helpers.
import { loadAgentDefinitions } from './agent-config.mjs';
import {
  agyStatus,
  discoverAgents as rawDiscoverAgents,
  executableMissing,
  geminiCapabilityError,
  parseAgentAuthStatus,
  runAgentProcess,
} from './shared/agent-process.mjs';
import { resolveAgentStepLaunch, runStepAgentProcess } from './autopilot/step-runner.mjs';

export function discoverAgents(options = {}) {
  return rawDiscoverAgents({ loadDefinitions: loadAgentDefinitions, ...options });
}

export {
  agyStatus,
  executableMissing,
  geminiCapabilityError,
  parseAgentAuthStatus,
  resolveAgentStepLaunch,
  runAgentProcess,
  runStepAgentProcess,
};

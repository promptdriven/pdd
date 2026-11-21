// Generated from prompts/cli/agent-adapters.prompt.md (sha256: d33174a4c41938e26dd655e332a8d6d0621f65ebbd4ef8a6316df2e2203d6add).
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

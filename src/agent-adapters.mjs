// Generated from prompts/cli/agent-adapters.prompt.md (sha256: f0f36d7410276dbd2dc8f7ce98a5bb01d82eae46dc2f3277912fc8d3806d123c).
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

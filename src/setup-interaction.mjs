// Implements prompts/cli/setup-interaction.prompt.md.
export function setupMayAsk({ yes = false, stdinIsTTY = false, stdoutIsTTY = false } = {}) {
  return !yes && Boolean(stdinIsTTY && stdoutIsTTY);
}

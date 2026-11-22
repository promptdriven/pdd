// Generated from prompts/cli/accounts-cli.prompt.md.
// Thin compatibility facade for the accounts CLI subsystem under src/accounts/.
export {
  applyAutoSwitchBlock,
  refreshInstalledAutoSwitchBlocks,
  removeAutoSwitchBlock,
  renderAutoSwitchBlock,
} from './accounts/auto-switch.mjs';

export {
  detectImportProvider,
  readClaudeTokenFromPath,
  readCodexFullAuthBundle,
  readLocalClaudeToken,
} from './accounts/import-auth.mjs';

export { runAccountsCli } from './accounts/cli-dispatch.mjs';

// Generated from prompts/cli/login-pool.prompt.md.
// Layer-1 shared CloudAccountsError with automatic secret redaction.
import { redactSecrets } from '../secret-redaction.mjs';

export class CloudAccountsError extends Error {
  constructor(message, { status = 0, code = 'cloud_accounts_error', payload = null, exitCode = 1 } = {}) {
    super(redactSecrets(String(message ?? 'Cloud accounts request failed.')));
    this.name = 'CloudAccountsError';
    this.status = status;
    this.code = code;
    this.payload = payload;
    this.exitCode = exitCode;
  }
}

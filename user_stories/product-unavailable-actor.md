# Continue when my account lookup is unavailable

I can keep using product commands when my token cannot identify my account.

## Acceptance criteria

1. Status and next ignore outsider marker claims when the account reply has no login, and each looks up the account at most once.
2. Preparing phone-1 still creates issue 82 and starts no workflow when outsider claims cannot be trusted.

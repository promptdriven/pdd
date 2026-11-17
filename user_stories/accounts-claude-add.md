# Enroll a fresh Claude account from the terminal

As a developer enrolling a Claude subscription in PDD Cloud, I want to see Claude's prompt and paste the browser authorization code in my terminal, whether I enroll one account or use `--loop`.

## Acceptance criteria

1. When Claude displays a wrapped OAuth token, `pdd accounts add --provider claude` submits the complete new token to PDD Cloud.
2. When Claude prints no OAuth token to stdout, enrollment fails without uploading an existing token.

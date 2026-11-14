# Pair a phone at setup

As a person connecting a phone, I want to confirm its key at my terminal, so that this machine can recognize my phone.

## Acceptance criteria

1. `pdd setup --pair-code K7Q2-9MXD` shows that exact code for ten minutes and waits for a matching phone; ordinary interactive setup offers pairing when no phone is paired and, if accepted, generates and shows its own code.
2. A matching signed offer saves the phone's public key for the current GitHub login only after the terminal confirms the same code; a declined, invalid, expired or mismatched offer saves no key.
3. A local service can read pending code and paired public keys through `pdd pair status --json`, and submit an offer through `pdd pair offer --message FILE`; the offer command alone never saves a key or exposes a private key.
4. A supplied code can pair an additional phone; invalid codes, a supplied code with `--yes` or `--no-pair`, and a supplied code without a terminal exit 2 before setup effects. Ordinary nonterminal setup skips pairing.

```pdd-boundary
prompts/cli/pdd-cli.prompt.md
prompts/cli/interpreter-version.prompt.md
```

## Verification boundary

The Runtime scenario checks CLI routing using injected setup and pairing ports. Native tests must establish file bytes, real Git behavior, signature verification, terminal confirmation, expiry and concurrent handoff; a supplied port result cannot prove those effects.

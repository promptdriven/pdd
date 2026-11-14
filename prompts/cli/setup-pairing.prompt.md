# Phone pairing

Own `src/setup-pairing.mjs`. Export `runSetupPairing({cwd, env, code, interactive}, ports)`, `pairStatus({cwd, env}, ports)`, and `pairOffer({cwd, env, messageFile}, ports)`. The CLI supplies terminal streams and permits injected clock, random, login, state, wait and confirmation ports; defaults use the local machine. Each operation returns `{exitCode, message}`; `message` is text without a trailing newline, empty when there is nothing to print. `runSetupPairing` writes the invitation and confirmation question to its supplied streams as they happen. `pairStatus` returns its JSON object serialized in `message`; `pairOffer` returns a finite confirmation or error message. The CLI prints a nonempty message on stdout for exit 0, stderr otherwise. These operations establish a public key for a GitHub login, not workflow approval authority.

## Domain decisions

On interactive setup, unless a code was explicitly supplied, ask `Pair a phone? [y/N]` before looking up the GitHub login. A decline returns successfully without a login lookup or state change. On acceptance obtain the current GitHub login; skip pairing if that login already has a paired phone, otherwise generate a short code and show it. An explicit code obtains the login without the initial question. A supplied code is shown unchanged. Publish a pending invitation for exactly ten minutes, await a matching signed offer, and ask `Does your phone show CODE? [y/N]`. Only an affirmative terminal confirmation before expiry saves the public key, scoped to this machine and login, and prints `Paired: DEVICE (key KEYID)`. Decline, expiry, invalid offer, unavailable login or interrupted wait never saves a key. The phone private key never enters pdd. Explicit code permits adding another phone.

The local offer file is a UTF-8 JSON object with exactly `v` (integer 1), `login`, `code`, `keyId`, `deviceName`, `publicKey`, and `signature` (strings except the key). `publicKey` is exactly a P-256 public JWK: `kty` is `EC`, `crv` is `P-256`, and `x` and `y` are base64url strings. `signature` is base64url of the 64-byte IEEE-P1363 ECDSA P-256 SHA-256 signature over UTF-8 JSON of the other fields, recursively sorted by key with no whitespace. Verify the signature with the supplied public key, and match login and code exactly against the unexpired invitation. Never save a key from the offer command itself. Reject malformed, mismatched, expired or unverifiable offers with a finite error and no key change.

`pairStatus` is read-only and exposes only `{pending, paired}`: pending is null or `{login, code, expiresAt}` with ISO UTC expiry; paired is an array of `{login, keyId, deviceName, publicKey}` for the current machine. No tokens, private keys or other secrets appear. `pairOffer` submits the file's offer only to a currently waiting setup; no waiting setup means refusal. Serialize competing invitations and offer delivery so an old, expired or concurrent offer cannot be consumed by a later invitation. Clear pending state on completion, expiry or interruption. State lives in the user state directory, scoped to this machine, and keys are scoped to login. No network transport is implied by the local handoff.

## Dependencies

Node's cryptography and filesystem facilities provide signature verification and local state. The caller supplies terminal context and dispatches commands.

<details>
<summary>Runtime interface</summary>

```json
{
  "kind": "native-only",
  "status": "approved",
  "prose_sha256": "e10aece20b26e1d75a3c39c77653de558df450da03bb7116ecb983ff808c1e2b",
  "reason": "Cryptographic verification, terminal confirmation, concurrent filesystem handoff and expiry require real native effects that bound Runtime ports cannot establish."
}
```
</details>

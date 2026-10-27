# Verify a phone's signed workflow decision

Own `src/phone-approval.mjs`. Module function
`verifyPhoneApproval({token,phoneId,runId,stage,decision,expectSeq,text?,usedNonces:[]},
{lookupPhone,now}={})` verifies the device proof before the runner admits a phone
approval without a terminal. This is a new portable seam: preserve its declared
wire format, fail-closed behavior and result. It does not discover credentials,
read disk secrets, contact a private service, mutate a journal or advance a run.

The phone retains its non-exportable P-256 private key; the fleet ledger supplies
its public key. Terminal and chat-file checks are defence in depth against an
agent with the same Unix account, not a hard wall. A valid phone signature proves
possession of the separate device key, provided the trusted ledger and verifier
are intact. There is no HMAC or same-machine private-key fallback.

A successful call returns `{ok:true,approvalRecord:{kind:'phone',phoneId,nonce,
at:time}}`. Refusal returns `{ok:false,code,message}` with a finite, credential-free
message. The function never throws. `lookupPhone(phoneId)` is a trusted host port
returning `{phoneId,removed:false,publicKeyJwk,state?,fleetId?,publicKeySpki?}`
for the current active phone after verifying the signed fleet ledger chain.
The host adapter owns chain verification; no unverified ledger response is
authority. Additional ledger metadata is not read as signing material.
Missing lookup or failed lookup is `phone_ledger_unavailable`; absent, mismatched
or unproved active identity is likewise unavailable. An explicitly removed phone
is `phone_not_active`. A supplied state must be active; removed refuses and any
other state is unavailable. Missing public-key data is unavailable. The default clock is
Date.now; `now()` returns epoch milliseconds.

<details>
<summary>Exact wire bytes, binding and refusal rules</summary>

The token is canonical unpadded base64url of UTF-8 JSON:
`{v:1,alg:'ES256',payload,signature}`. These four envelope fields are required.
Additional envelope metadata, including any token-supplied public key, is ignored
and never grants authority. Only the trusted ledger supplies a verification key.
Its maximum encoded length is 40,000 ASCII characters.
`signature` is canonical unpadded base64url of the 64-byte raw IEEE-P1363 ECDSA
signature returned by WebCrypto ECDSA with SHA-256 on P-256.

The signed bytes are UTF-8 JSON.stringify of a newly constructed object with
keys in this exact order:
`{runId,stage,decision,expectSeq,phoneId,time,nonce}`.
For changes only, append `text` as the final key. There is no whitespace outside
JSON strings. The incoming payload must have exactly these keys, but its JSON
key order need not match: verification reconstructs the canonical signed object.
The phone uses this same canonical order before signing. The envelope version
and algorithm are fixed; unsigned envelope metadata cannot extend signed policy.

Run and nonce are lowercase UUIDv4. Stage is 1–64 lowercase letters/digits,
letter first, with single hyphen separators. Decision is approve, changes or
skip. expectSeq is a positive safe integer. Phone id is 1–128 ASCII letters,
digits, underscore or hyphen; identity is case-sensitive. Time is a nonnegative
safe integer in epoch milliseconds. Changes text is 1–4000 Unicode characters,
allowing tab/newline and refusing other control characters; other decisions
forbid text. The requested input has the same binding domains.

Request runId, stage, decision, expectSeq, phoneId and changes text must equal
the signed values exactly. Any mismatch is `phone_binding_mismatch`. Invalid
encoding, envelope, field values or key format is `phone_invalid_token`. Valid
signature requires a ledger JWK with kty EC, crv P-256, no private d field and
valid x/y coordinates. Import/verification failure is `phone_invalid_signature`.
Never obtain the verification key from the token or command-line arguments.

Refuse `phone_token_expired` if `time < now-300000` or `time > now+300000`;
the endpoints are allowed. An invalid clock refuses `phone_invalid_token`.
`usedNonces` is the complete run's durable phone-nonce list, as strings or
`{phoneId,nonce}` records; a matching nonce string, or a matching record for the
same phone, refuses `phone_token_replayed`. Missing usedNonces means empty;
nonarrays refuse. This function does not consume a nonce. The caller verifies
under its run lock, then saves the returned phoneId/nonce with the decision
before any effect, so two concurrent commands cannot both admit one token.
Tokens bind to one run and cannot be used against another run's nonce store.

Validation, binding, time and replay checks occur before ledger lookup. A trusted
fresh ledger response proves active phone identity and public key; only then can
signature verification succeed. No failure admits authority or leaks the token.

</details>

## Dependencies

- Node `node:crypto` WebCrypto: runtime/generation, import the ledger's public EC
  JWK and verify ECDSA/SHA-256. Node Buffer and TextEncoder supply wire decoding.
- [Decision seam](workflow-decide.prompt.md): integration; owns authorization
  composition and passes the current authoritative gate binding.
- [Runner](workflow-runner.prompt.md): integration; owns locked admission, durable
  nonce consumption and stale checks. The verifier cannot replace these guards.
- Trusted `lookupPhone` port: runtime; ledger endpoint/schema adaptation is owned
  by the mobile host. Without that port this module refuses safely.

Nonce uniqueness is per run, across all phones: usedNonces contains every admitted
phone nonce from this run. A different active phone cannot reuse one; phoneId in
a supplied nonce record is informational and does not narrow the replay check.

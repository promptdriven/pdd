# See oversized scenarios before checking Stories

I can see why a scenario cannot be checked, so checking all my Stories never hides one because its JSON file is too large.

## Acceptance criteria

1. Valid scenario JSON files of 1,048,575 and 1,048,576 bytes remain selectable by default, Story name, Story path and test path.
2. A scenario JSON file of 1,048,577 bytes makes default discovery refuse with exit 4 before sign-in, network or AI calls, naming its path, actual byte size and the 1,048,576-byte test-file allowance, even alongside multiple normal scenarios.
3. Explicit selection of an oversized scenario by test path or ordinary test alias, or by an established Story name or path, reports the limit reason instead of "Unknown story"; explicit selection of a normal Story still works when oversized candidates are unselected.
4. A valid scenario containing an actual 1,048,576-byte ASCII input plus JSON overhead receives the same oversized diagnostic without increasing execution or source limits; size counts serialized UTF-8 bytes, not characters.
5. Complete inspection of JSON up to 10,485,760 bytes uses actual top-level schema and Story keys, including late and duplicate keys; a marker inside a data string does not make data a scenario.
6. Valid unrelated JSON objects above 1 MiB and within the inspection budget remain outside Story discovery, and can be explicitly included as ordinary source when existing source safety and total limits allow.
7. Beyond that inspection budget, a safely established non-object root stays unrelated; otherwise discovery refuses uncertain candidates with their path, actual size, test allowance and inspection budget. Default selection cannot claim completeness, and a potentially hidden Story cannot be declared unknown.
8. Conclusively unknown selections retain exit 2. Ordinary non-test non-regular JSON entries at or below 1,048,576 bytes (the entry's own metadata byte size) are skipped without following links, so default Check, --files and Try retain normal discovery, "No tests found" guidance and unknown-Story errors. Unsafe oversized inspection and unreadable or unstable regular-file inspection remain explicit errors, without unbounded reads; selected payload and dependency symlinks remain refused.

## Rules to check

The execution test-file allowance is inclusive: 1,048,576 serialized UTF-8 bytes including JSON overhead. The independent per-file discovery inspection budget is 10,485,760 bytes, inclusive. Existing total-source byte/file/tar limits and safe-file rules remain unchanged. Incomplete objects cannot prove unrelatedness or final Story aliases, even with an early schema key. Full JSON parsing uses the last duplicate key. A successful all-Story selection that omits a confirmed oversized or unclassified candidate is forbidden.

## Concrete regression cases (native; not executable Runtime scenarios)

Use isolated Git repositories and the actual CLI plus native discovery/selection bindings. Derive assertions from these criteria before execution:

- Materialize valid scenarios at exactly cap-1, cap and cap+1 bytes; test default, Story name/path and test path/alias. Repeat with several normal scenarios and one oversized candidate; default refusal has zero authentication, RPC and AI effects, while explicit normal selection remains usable.
- Put schema and Story keys early and after 1 MiB; repeat duplicate keys in both orders, with the final value deciding identity and aliases. Include nested and escaped marker strings as decoys. A conclusively unknown Story still exits 2.
- Materialize valid unrelated objects at 1,048,577 bytes and approximately 1.3 MiB; default discovery ignores them. Include one explicitly as ordinary source alongside a normal scenario with the combined payload and tar below existing limits; its size alone must not trigger the test-file cap.
- Check complete documents exactly at the inspection budget and objects beyond it with late/duplicate identity keys. Beyond-budget partial objects stay unclassified; a safe non-object array-root control is unrelated. Potentially hidden Story selection reports uncertainty and both limits. Exercise unsafe oversized inspection, unreadable/unstable regular files and bounded reads separately.
- With unrelated non-regular JSON entries (including configuration symlinks, dangling symlinks and FIFOs) at or below the allowance by their own lstat size, check normal default/--files/Try selection, no-tests guidance and conclusively unknown Story errors, without target reads or FIFO blocking. Selected source/dependency symlinks still refuse. Keep synthetic symlink-ancestor inputs separate from actual Git listing.
- Include multibyte UTF-8 content whose character count is below the cap but serialized byte count exceeds it. Independently measure the actual bytes.

For legitimate bounded native fixtures, author a minimal prompt interface whose input schema genuinely accepts a string field and a matching valid scenario; do not add an unknown field to Harbor Coffee's closed order schema. Construct real input text with `Buffer.alloc(n, 65).toString('ascii')`, serialize the scenario and adjust real padding by the measured serialized overhead. For the payload case set that accepted string to exactly 1,048,576 ASCII bytes and measure the larger serialized file. Independently assert `Buffer.byteLength(serialized, 'utf8')`, written file stat size and a supplemental SHA-256 round-trip digest. Hashes and claimed counts never substitute for materialized bytes. Keep generation finite, including beyond-budget fixtures. This native fixture recipe grants no Runtime filesystem authority and does not assert that Runtime can execute a one-MiB inline payload.

## Runtime check

Not run: the owning preflight prompt has no executable Runtime interface or injected Git/filesystem ports. Its native exports read the host filesystem directly; a runtime root string or supplied byte count cannot materialize those files. Concrete discovery, bounded reads and CLI exit/effect evidence require native execution. Executable module binding remains a separate contract decision tracked by https://github.com/promptdriven/pdd/issues/2548. No new Runtime field, repeat-byte primitive or server-cap increase is invented; no Runtime pass or approval is claimed.

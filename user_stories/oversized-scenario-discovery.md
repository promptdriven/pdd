# See oversized scenarios before checking Stories

I can see why a scenario cannot be checked, so checking all my Stories never hides one because its JSON file is too large.

## Acceptance criteria

1. Valid scenario JSON files of 1,048,575 and 1,048,576 bytes remain selectable by default, Story name, Story path and test path.
2. A scenario JSON file of 1,048,577 bytes makes default discovery refuse with exit 4 and a diagnostic naming its path, actual byte size and the 1,048,576-byte test-file allowance; it is never silently omitted from an apparently complete all-Story result.
3. Explicit selection of an oversized scenario by test path, or by an established Story name or path, reports the source-limit reason instead of "Unknown story", with exit 4 and no sign-in, network or AI calls.
4. A scenario containing an actual 1,048,576-byte ASCII input plus JSON overhead receives the same oversized diagnostic, without increasing execution or source limits.
5. Unrelated large JSON conclusively classified as non-scenario data does not become a Story; a marker inside a data string does not establish scenario identity.
6. When bounded inspection cannot classify large JSON, including a late schema or Story key, discovery refuses explicitly with its path and source-limit reason instead of claiming completeness or declaring a potentially hidden Story unknown.

## Rules to check

The test-file limit is inclusive and counts serialized UTF-8 bytes, including JSON overhead. Discovery inspects at most 1,048,576 bytes per oversized JSON file and preserves safe file handling. Unclassified files may cause conservative refusal. A successful all-Story selection with an omitted oversized or unclassified candidate is forbidden. No unsupported server limit increase or symbolic size/hash assertion substitutes for real fixture bytes.

## Concrete regression cases (not executable Runtime scenarios)

Use isolated Git repositories with one ordinary scenario and the candidate. Exercise default selection, Story name, Story path and test path through the actual CLI. Materialize valid scenario JSON of exactly 1,048,575, 1,048,576 and 1,048,577 bytes. The first two select normally; the third refuses as above. Repeat with early/late schema and Story keys, a conclusively unrelated large JSON control, and an unclassified large JSON control with a marker only inside data. Unknown selections remain ordinary command errors only when discovery is conclusive.

For concrete bytes, construct the candidate with a real ASCII string (for example Node Buffer.alloc(n, 65).toString('ascii')), serialize, and adjust padding by the measured serialized overhead. Independently assert Buffer.byteLength(serialized, 'utf8') and the written file's stat size before discovery. For the payload boundary, place exactly 1,048,576 actual ASCII bytes in the input and measure the larger serialized JSON file; expect source-limit refusal. A digest may supplement byte-integrity checks but never replace materialized bytes. This native fixture mechanism does not grant Runtime filesystem authority.

## Runtime check

Not run: the owning preflight prompt has no executable Runtime interface or injected Git/filesystem ports. Its native exports read the host filesystem directly; a runtime root string or supplied byte count cannot materialize those files. Concrete discovery, bounded reads and CLI exit/effect evidence require native execution. The person must decide adoption of an executable module binding separately. These case expectations are drafts for contract review; no Runtime pass or approval is claimed.

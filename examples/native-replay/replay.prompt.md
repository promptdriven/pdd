# Native case replay recipe

`replay.mjs` is a Node command for the accompanying synthetic native cases. It
accepts a case JSON path and a JavaScript module path as its two arguments. The
module exports `countWords`; each case supplies its input and exactly one expected
return value or expected error name and message. Call that real export for every
case. A return passes only when it deeply equals the expected return; a thrown
error passes only when both its name and message match the expected error.
A missing expected error, an unexpected error, a wrong error or wrong return
fails the case. Print one `PASS <id>` or `FAIL <id>` line per case, followed by
`<passed>/<total> passed`, and exit 0 only when all cases pass. Invalid cases,
missing exports and setup errors exit nonzero and must not count as detections.
The cases are independently authored expectations, not values copied from a run.

This verification command owns neither the target module nor its Runtime
interface. It demonstrates native execution; it is not a Runtime entry and has
no declared Runtime interface. Native results do not approve prompts or gates.

<a id="native-validation-profile-replay"></a>
<details><summary>Native validation profile: replay</summary>

```json
{"schema":"pdd.native-profile.v1","profileId":"replay","reportFormat":"pdd.native-node-report.v1","requiredIds":["test/native-replay-recipe-3160.test.mjs::native recipe executes the public function and detects return and error controls@13:1"],"requiredGates":[],"fixtures":[],"mappings":[{"storyPath":"user_stories/native-replay-recipe-3160.md","criterionId":"AC1","criterionText":"A matching return or matching error name and message passes its case.","nativeIds":["test/native-replay-recipe-3160.test.mjs::native recipe executes the public function and detects return and error controls@13:1"]},{"storyPath":"user_stories/native-replay-recipe-3160.md","criterionId":"AC2","criterionText":"A wrong return, wrong error, missing expected error or unexpected error fails its case and the command exits nonzero.","nativeIds":["test/native-replay-recipe-3160.test.mjs::native recipe executes the public function and detects return and error controls@13:1"]},{"storyPath":"user_stories/native-replay-recipe-3160.md","criterionId":"AC3","criterionText":"Missing exports, malformed cases and setup failures exit nonzero without claiming a case passed.","nativeIds":["test/native-replay-recipe-3160.test.mjs::native recipe executes the public function and detects return and error controls@13:1"]}],"sourcePaths":["examples/native-replay/replay.mjs","examples/native-replay/count-words.mjs","examples/native-replay/cases.json","examples/native-replay/capture.mjs","examples/native-replay/capture.prompt.md"],"testPaths":["test/native-replay-recipe-3160.test.mjs"]}
```
</details>

## Dependencies

The command reads its case file and imports the target module supplied by the
caller. Node.js supplies file and module loading and deep equality.

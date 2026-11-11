# PDD release notice

Own `src/release-notice.mjs`. Export async module function `releaseNotice({version, ci, probe}, {releases} = {})`, returning exactly `{message}` with a string message and no trailing newline. This adds a release reminder; it never runs an installer, starts a child process, changes an install or writes persistent state. Automatic installation is outside this feature, including during workflows and CI.

Return an empty message without calling the release port when ci or probe is true or the installed version is invalid. Otherwise call injected `releases.latest({})` exactly once. It returns `{tag}`, the latest published non-draft, non-prerelease release tag, or an empty tag when unavailable. A rejection or invalid reply gives an empty message.

Installed versions are three canonical nonnegative decimal integers separated by dots, each a JavaScript safe integer, optionally followed by a SemVer prerelease and/or build suffix. Prerelease identifiers are nonempty ASCII letters, digits or hyphens separated by dots; numeric identifiers have no leading zeros. Build identifiers have the same character set and may have leading zeros. Release tags are exactly `alpha-vMAJOR.MINOR.PATCH` or `vMAJOR.MINOR.PATCH`, with the same canonical safe integers and no suffix. Compare the three numbers numerically in major, minor, patch order; a stable release with the same numbers is newer than an installed prerelease. Build suffixes do not affect order. Equal, older, malformed or unrecognized tags give an empty message. Validating the tag before using it in the command prevents remote text from adding shell syntax or extra lines.

For a newer release return exactly `pdd VERSION is available (installed INSTALLED). Update: npm install -g github:promptdriven/pdd#TAG`, substituting the release's three numbers, the supplied installed version and the validated tag. Use the GitHub package, because the npm registry's `pdd` is a different product. Check on each invocation rather than caching a no-update answer, so the next command can notice a release.

The default release port is an anonymous HTTPS GET of `https://api.github.com/repos/promptdriven/pdd/releases/latest`, accepting GitHub JSON. It sends no credentials or gh calls, refuses redirects, and accepts only a successful JSON object with `draft === false`, `prerelease === false` and a string `tag_name`. Bound the whole lookup, including response body consumption, to 1000 ms and at most 65536 body bytes. Abort on timeout or overflow; HTTP, network, body and JSON errors are unavailable, silently. Always clear the timer. These native transport bounds are checked with native tests; the injected port binds the actual release read for deterministic decision checks.

## Dependencies

- Runtime JavaScript comparison, regular expressions, safe integer checks and string formatting.
- Native default port: Node fetch, AbortController, timers and streamed UTF-8 JSON decoding. Required only for actual GitHub access; injected `releases.latest` replaces that access for decision checks.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "1646db313f37f9d771270f794195210b70d504ef8cbf7daaf70ae6c25a968ba7",
  "entries": [
    {
      "operation": "releaseNotice",
      "input_schema": {
        "type": "object",
        "properties": {
          "version": {
            "type": "string"
          },
          "ci": {
            "type": "boolean"
          },
          "probe": {
            "type": "boolean"
          }
        },
        "required": [
          "version",
          "ci",
          "probe"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "message": {
            "type": "string"
          }
        },
        "required": [
          "message"
        ],
        "additionalProperties": false
      },
      "errors": []
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "releases",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "latest",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "tag": {
                "type": "string"
              }
            },
            "required": [
              "tag"
            ],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 20,
    "max_model_calls": 12
  },
  "conventions": [],
  "kind": "partial"
}
```
</details>

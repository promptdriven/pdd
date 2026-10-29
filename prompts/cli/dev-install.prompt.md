# Install a development checkout

Own the checkout development installer exposed by `node scripts/dev-install.mjs`. It installs a build from the given source checkout into the same managed version layout used by the release installer, selects that development version, reports the installed version, and can later remove that development installation while restoring the active installation that was selected before it. This behavior is separate from release signing and validation, direct `node bin/pdd.mjs` source use, and the regular release installer; those remain unchanged.

The install operation must read the checkout package metadata to derive its version and append `-dev` to identify the development build. It must create the managed version record (including the version's `runtime.json` and any required Node tool layout), remember the previously active selection, and make the checkout-built version active. It must not overwrite an unrelated active version or discard the saved prior selection. A successful install reports the derived development version on stdout and exits successfully; failures leave no partial development state and report one diagnostic on stderr.

The uninstall operation removes the matching development installation and restores the saved prior active selection and state. It must not remove or change a different active installation that replaced the development version after install; in that case it reports the conflict and leaves state intact. A successful uninstall reports the restored selection on stdout and exits successfully. Repeated or missing uninstall requests are errors and do not change state.

The exact public argument spelling, managed-state schema, checkout artifact copy rules, supported platforms and conflict policy remain to be confirmed at the Story gate; this prompt records the required observable behavior without choosing those unresolved details.

## Dependencies

- [Local CLI boundary](public-boundary.prompt.md), for the package's source-checkout and release-install preservation rules.
- [Package metadata](../../package.json), runtime use for the checkout version.

<details><summary>Runtime interface</summary>

```json
{"status":"draft","prose_sha256":"","entries":[{"operation":"main","input_schema":{"type":"object","properties":{"argv":{"type":"array","items":{"type":"string"}}},"required":["argv"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"exit_code":{"type":"integer"},"stdout":{"type":"string"},"stderr":{"type":"string"}},"required":["exit_code","stdout","stderr"],"additionalProperties":false},"errors":["invalid-arguments","install-failed","uninstall-failed","active-install-conflict","missing-development-install"]}],"calls":[],"resources":[],"limits":{"max_steps":4,"max_model_calls":4},"conventions":[{"path":"/entries/0/input_schema","convention":"cli"},{"path":"/entries/0/result_schema","convention":"cli"}]}
```

</details>

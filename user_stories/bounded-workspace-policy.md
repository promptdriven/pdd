# Set an allowed-file ceiling

I can opt in with a small repository policy. My Story selection stays separate from permission. The proposed file is pdd-workspace.json; pdd-source.json keeps additive includes.

Draft for review. These choices and expected results are not approved.

## Acceptance criteria

1. With no pdd-workspace.json, policy loading reports unconfigured and does not read a missing file.
2. A policy with allowed_paths ["simulation/", "contracts/shared.md"] retains those two entries in order and does not select Stories or add source includes.
3. A present empty allowed_paths list reports a configured policy with no permitted authored paths.
4. Malformed policy, unknown keys and unsafe path spellings are refused as workspace-config-invalid; no source content is read by policy loading.
5. A linked or oversized policy is refused as workspace-config-unsafe before its content is read.

## Rules to check

The policy is a ceiling. Directory matching uses full path components. A policy never weakens source safety or grants upload membership. Forbidden: an include, selection or preparation hook widens permission. Native ancestor/regular-file and matching checks are separate from the supplied file-port replies.

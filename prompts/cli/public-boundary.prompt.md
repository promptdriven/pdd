# Public PDD command line

Implement the public PDD command line from this prompt before changing its source.

Use `pdd` as the only public command name. Derive help and shell completion from one source-defined catalog so every supported command form has a single plain description. Keep help, version, skill output, completion, and local workflow listing usable from public source without the installed PDD Host.

Represent each supported command with a typed command ID, an exact command prefix, and an allowlist of operand and option types. Parse every argument before dispatch, reject unknown commands/options and invalid combinations, then reconstruct a fresh argument vector from parsed values. Never forward the caller's original argument vector or shell text. Runtime expert calls may name only the eight operations in the catalog and may not accept arbitrary forwarded arguments.

Delegate only catalogued Host-dependent commands to the existing installed Host `runCli` export. Preserve that implementation's existing person and approval checks. If the installed export is absent or cannot load, explain that the Host component is required and that the command is coming soon in a source-only build. Do not add network endpoints, login bypasses, or copied Host, phone, server, runtime, pool, operations, or internal prompt source.

The terminal phone command only displays the PDD web app link and a QR code for the person to scan on their own phone. Workflow changes must remind the person to review, commit, and push workflow files before using them to start work. Keep paths within the current project when reading local workflows.

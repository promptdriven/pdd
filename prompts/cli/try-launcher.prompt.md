# Find the current repository's virtual program without changing PATH

Own src/try-launcher.mjs. Install one shared pdd virtual launcher beside the invoked pdd executable, with
program names as symbolic links to it. That folder is already on PATH; users and agents need no PATH export.
Export installNamedLauncher({root, name, descriptorPath, binDir, path}) returning the named executable path,
and runNamedShim(name, argv, ports) returning the program or wrapper exit code.

Installation is an owner setup operation outside the sandbox. Require the safe CLI name selected by Try doors.
Refuse a reserved launcher name, an existing non-PDD file/link at either destination, or any real command
of that name on PATH. Do not overwrite commands, ask for silent permission, or change global agent config.
An existing link to this shared launcher is reusable across repositories. Replace only a regular single-link
file bearing the exact PDD shared-launcher marker. Use a POSIX shell shebang that execs the absolute Node executable with constant dynamic-import JavaScript, independent of the project’s CommonJS/ESM mode. Use atomic mode0700 writes; shell/JavaScript syntax must
not interpolate untrusted paths as source. An unwritable bin directory gets an actionable path-specific error.

Store only a descriptor pointer in the repository's ignored private .pdd/try/programs/<name>.json. It must
resolve within that repository's .pdd/try/sessions tree; never contain credentials. A compatibility link in
.pdd/try/bin may point to the same shared launcher; there is only one executable launcher implementation.

On invocation, derive the safe program name from the invoked filename. Walk up from the current directory
to the nearest Git root (.git can be a file or directory), then select that root's program pointer. Do not
use another parent's Try after reaching a Git root without a matching open program. A nested folder works;
the same name in another repo selects that repo's own Try. Outside a repository or with no matching record,
print `pdd try: no open Try here: run pdd try STORY --cli in your repo` on stderr and return125 with empty stdout.
Reject symlinked private directories, pointer files, hardlinked pointers and escaping descriptor paths.
Delegate command/source identity, mailbox/direct selection, streams, usage and execution to Try doors.

## Dependencies

- [Try doors](try-doors.prompt.md): navigation to the delegated runShim binding and setup name policy.
  Required callable interface: runShim(descriptorPath, argv, ports={}) returns a Promise of numeric exit status.
  Its contract is consumed by the installed module; no prompt loading dependency back into this module.

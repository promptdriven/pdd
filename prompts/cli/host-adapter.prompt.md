# Installed Host adapter

Follow `public-boundary.prompt.md` for shared public naming and closed-source boundaries.

Own `src/host-adapter.mjs`. Export `installedHostPath(home)` and `loadInstalledHost({ home, importer })`. Resolve the installed Host module under the person's pocket app, import it only when requested by a validated public command, and return its exported `runCli` function. Return `null` if the module is missing, fails to load, or does not export `runCli`. Loading the adapter must not invoke a Host command.

Accept an optional onUnavailable callback. Before returning null, report only a fixed reason: missing when ERR_MODULE_NOT_FOUND identifies the exact entry module URL, incompatible when runCli is absent, and load-failed for other import errors (including missing dependencies). Never pass the raw exception, its message or paths to the callback. Preserve the function-or-null return contract.

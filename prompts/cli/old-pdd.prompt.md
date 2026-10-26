# Earlier `pdd` PATH detector

Own `src/old-pdd.mjs`. Walk the supplied `PATH` in order, resolve each
executable named `pdd`, and stop when the Alpha executable is reached. Use the
resolved target for owner classification and Python-environment lookup, while
retaining the PATH spelling for diagnostics. Return the first different
executable with a stable classification: Python `pdd-cli`
and its conda/pip/pipx/uv owner, the legacy R-line wrapper (normally
`~/.local/bin/pdd`), or unknown. Detection is diagnostic and never removes or
rewrites a path.

The Python replacement plan names only the owning uninstall command. `uv` uses
`uv tool uninstall pdd-cli`; `pipx` uses `pipx uninstall pdd-cli`; other Python
environments use that environment's `python -m pip uninstall -y pdd-cli`.
Interactive setup may ask before running that plan, then must recheck PATH.
R-line and unknown entries always receive manual owner-removal guidance and are
never deleted. Non-interactive setup keeps the command and prints its full path
and an Alpha alias. Session and workflow starts only print a one-line warning.

## Dependencies

- [CLI dispatcher](pdd-cli.prompt.md): invokes the detector for setup and start
  warnings.
- [Prompting guide](../../docs/prompting-guide.md): authoring and preservation.

# Public shell completion

Follow `public-boundary.prompt.md` for shared public naming and closed-source boundaries.

Own `src/completion.mjs`. Export `renderCompletion(shell)`. Generate Bash or Zsh completion from `PUBLIC_COMMAND_ROUTES`, including only catalogued command words and option names. Return one newline-terminated script for `bash` or `zsh`; throw `TypeError` for any other shell. Never list commands that are absent from the public catalog.

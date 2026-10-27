# PDD executable entry

Own `bin/pdd.mjs`. Thin Node executable. Keep the bin name pdd, not pdd-alpha. No extra launcher or private adapter.

Before each command, call [skills install](skills-install.prompt.md) `installSkills({packageRoot, home})` with this package root and the person's home folder (`os.homedir()`). Do this here and not in `runPdd`, so in-process tests never write to a real home. If the install throws, write one line to stderr: `pdd: the PDD skills could not be installed in your home folder (<reason>). pdd still runs.` `<reason>` is the error code, or the message when there is no code. Then run the command as usual. An install failure never changes the exit code.

Then import the local public `runPdd`, pass process.argv.slice(2), and assign the returned integer to process.exitCode.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

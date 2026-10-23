# PDD executable entry

Follow `public-boundary.prompt.md` for shared public naming and closed-source boundaries.

Own `bin/pdd.mjs`. Keep this file as a thin Node executable: pass `process.argv.slice(2)` to `runPdd`, then assign its integer result to `process.exitCode`. Do not parse or dispatch commands here.

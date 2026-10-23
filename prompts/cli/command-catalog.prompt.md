# Public command catalog

Follow `public-boundary.prompt.md` for shared public naming and closed-source boundaries.

Own `src/command-catalog.mjs`. Export `PUBLIC_COMMAND_ROUTES`, `PUBLIC_COMMAND_IDS`, `PUBLIC_COMMAND_MANIFEST`, and `RUNTIME_OPERATIONS`. Each route has a stable `id`, exact `prefix`, typed operand and option specifications, optional validation tag, local/Host disposition, and one or more manifest forms with one plain description each. Keep command forms and completion inputs in this catalog. Do not include commands that belong to closed product components.

#!/usr/bin/env node
// Generated from prompts/cli/bin-entry.prompt.md (sha256: fad45bcafa37fd797174eb30355fb318288222ad11e6f4fa1e700315257f780b).
import { homedir } from 'node:os';
import { fileURLToPath } from 'node:url';
import { installSkills } from '../src/skills-install.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

try { installSkills({ packageRoot: fileURLToPath(new URL('..', import.meta.url)), home: homedir() }); }
catch (error) { process.stderr.write(`pdd: the PDD skills could not be installed in your home folder (${error.code ?? error.message}). pdd still runs.\n`); }
const exitCode = await runPdd(process.argv.slice(2));
process.exitCode = exitCode;

#!/usr/bin/env node
// Generated from prompts/cli/bin-entry.prompt.md (sha256: c36b4a3a573881e4ca0465db8148a1e648d012ff68ea647d728d0821e4c1f67a).
import { homedir } from 'node:os';
import { fileURLToPath } from 'node:url';
import { installSkills } from '../src/skills-install.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

try { installSkills({ packageRoot: fileURLToPath(new URL('..', import.meta.url)), home: homedir(), claudeConfigDir: process.env.CLAUDE_CONFIG_DIR }); }
catch (error) { process.stderr.write(`pdd: the PDD skills could not be installed in your home folder (${error.code ?? error.message}). pdd still runs.\n`); }
const exitCode = await runPdd(process.argv.slice(2));
process.exitCode = exitCode;

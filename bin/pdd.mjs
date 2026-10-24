#!/usr/bin/env node
// Generated from prompts/cli/bin-entry.prompt.md (sha256: 505f05e1ed67a480fd2ebb6c7df6be48c10087d06892ddd5379e384e94a68e24).
import { runPdd } from '../src/pdd-cli.mjs';

const exitCode = await runPdd(process.argv.slice(2));
process.exitCode = exitCode;

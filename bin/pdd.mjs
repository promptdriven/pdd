#!/usr/bin/env node
import { runPdd } from '../src/pdd-cli.mjs';

const exitCode = await runPdd(process.argv.slice(2));
process.exitCode = exitCode;

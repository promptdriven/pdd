/**
 * commandBuilder.ts
 *
 * SINGLE SOURCE OF TRUTH for building PDD command arguments.
 * Both App.tsx and AddToQueueModal.tsx should use these functions.
 */

import { CommandType } from '../types';
import { PromptInfo } from '../api';
import { COMMANDS } from '../constants';

/**
 * Extract internal file paths and clean options for CLI.
 * Internal keys:
 * - _code, _test: Override auto-detected file paths
 * - _global_*: Global options that apply to all commands
 */
export function cleanOptions(rawOptions: Record<string, any>, prompt: PromptInfo): {
  options: Record<string, any>;
  codeFile: string | undefined;
  testFile: string | undefined;
} {
  const codeFile = rawOptions['_code'] || prompt.code;
  const testFile = rawOptions['_test'] || prompt.test;
  const options: Record<string, any> = {};

  for (const [key, value] of Object.entries(rawOptions)) {
    if (key === '_code' || key === '_test') {
      // Skip internal file path keys
      continue;
    } else if (key.startsWith('_global_')) {
      // Strip _global_ prefix for CLI flags
      const actualKey = key.replace('_global_', '');
      options[actualKey] = value;
    } else {
      options[key] = value;
    }
  }

  return { options, codeFile, testFile };
}

/**
 * Build the args object for a PDD command.
 * This is where ALL command-specific argument logic lives.
 *
 * NOTE: This function may modify the options object (moving some options to args).
 */
export function buildCommandArgs(
  command: CommandType,
  prompt: PromptInfo,
  codeFile: string | undefined,
  testFile: string | undefined,
  options: Record<string, any>
): Record<string, any> {
  const args: Record<string, any> = {};

  switch (command) {
    case CommandType.SYNC:
      // pdd sync BASENAME
      args.basename = prompt.sync_basename;
      // Pass context to ensure sync finds the prompt in the correct location
      if (prompt.context) {
        options['context'] = prompt.context;
      }
      break;

    case CommandType.UPDATE:
      // pdd update [CODE_FILE]
      // - No args: repo-wide mode (scan entire repo)
      // - One arg: single-file mode (update prompt for specific code file)
      // The command finds the corresponding prompt file automatically
      if (codeFile) {
        args.args = [codeFile];
      } else {
        args.args = [];
      }
      break;

    case CommandType.GENERATE:
      // pdd generate PROMPT_FILE
      args.prompt_file = prompt.prompt;
      break;

    case CommandType.TEST:
      // pdd test PROMPT_FILE CODE_FILE
      args.prompt_file = prompt.prompt;
      args.code_file = codeFile;
      break;

    case CommandType.EXAMPLE:
      // pdd example PROMPT_FILE CODE_FILE
      args.prompt_file = prompt.prompt;
      args.code_file = codeFile;
      break;

    case CommandType.FIX:
      // pdd fix PROMPT_FILE CODE_FILE TEST_FILES [ERROR_FILE]
      args.prompt_file = prompt.prompt;
      args.code_file = codeFile;
      args.unit_test_files = testFile;
      // error_file is entered in options modal but is a positional arg
      if (options['error-file']) {
        args.error_file = options['error-file'];
        delete options['error-file'];
      }
      break;

    case CommandType.SPLIT:
      // pdd split INPUT_PROMPT INPUT_CODE EXAMPLE_CODE [--output-sub] [--output-modified]
      args.input_prompt = prompt.prompt;
      args.input_code = codeFile;
      if (options['example-code']) {
        args.example_code = options['example-code'];
        delete options['example-code'];
      }
      break;

    case CommandType.CHANGE:
      // pdd change CHANGE_PROMPT_FILE INPUT_CODE [INPUT_PROMPT_FILE] [--budget] [--output]
      if (options['change-prompt']) {
        args.change_prompt_file = options['change-prompt'];
        delete options['change-prompt'];
      }
      args.input_code = codeFile;
      args.input_prompt_file = prompt.prompt;
      break;

    case CommandType.DETECT:
      // pdd detect [PROMPT_FILES...] CHANGE_FILE [--output]
      // This command doesn't use the selected prompt (requiresPrompt: false)
      // All args come from modal options
      {
        const promptFilesStr = options['prompt-files'] || '';
        const changeFile = options['change-file'] || '';
        const promptFiles = promptFilesStr.split(',').map((f: string) => f.trim()).filter(Boolean);
        args.args = [...promptFiles, changeFile].filter(Boolean);
        delete options['prompt-files'];
        delete options['change-file'];
      }
      break;

    case CommandType.AUTO_DEPS:
      // pdd auto-deps PROMPT_FILE DIRECTORY_PATH [--output] [--csv] [--force-scan]
      args.prompt_file = prompt.prompt;
      if (options['directory-path']) {
        args.directory_path = options['directory-path'];
        delete options['directory-path'];
      }
      break;

    case CommandType.CONFLICTS:
      // pdd conflicts PROMPT1 PROMPT2 [--output]
      args.prompt_file = prompt.prompt;
      if (options['prompt2']) {
        args.prompt2 = options['prompt2'];
        delete options['prompt2'];
      }
      break;

    case CommandType.PREPROCESS:
      // pdd preprocess PROMPT_FILE [--output] [--xml] [--recursive] [--double]
      args.prompt_file = prompt.prompt;
      break;

    case CommandType.CRASH:
      // pdd crash PROMPT_FILE CODE_FILE PROGRAM_FILE ERROR_FILE [options]
      args.prompt_file = prompt.prompt;
      args.code_file = codeFile;
      if (options['program-file']) {
        args.program_file = options['program-file'];
        delete options['program-file'];
      }
      if (options['error-file']) {
        args.error_file = options['error-file'];
        delete options['error-file'];
      }
      break;

    case CommandType.VERIFY:
      // pdd verify PROMPT_FILE CODE_FILE VERIFICATION_PROGRAM [options]
      args.prompt_file = prompt.prompt;
      args.code_file = codeFile;
      if (options['verification-program']) {
        args.verification_program = options['verification-program'];
        delete options['verification-program'];
      }
      break;

    case CommandType.SUBMIT_EXAMPLE:
      // Submit Example uses fix --loop --auto-submit under the hood
      args.prompt_file = prompt.prompt;
      args.code_file = codeFile;
      args.unit_test_files = testFile;
      // Create a placeholder error file path (loop mode doesn't require existing error file)
      args.error_file = '.pdd/submit_example_errors.log';
      // Force loop and auto-submit flags
      options['loop'] = true;
      options['auto-submit'] = true;
      // Move verification-program from options to args
      if (options['verification-program']) {
        args.verification_program = options['verification-program'];
        delete options['verification-program'];
      }
      break;

    case CommandType.BUG:
      // BUG command is handled separately in App.tsx (uses spawnTerminal)
      // This is here for completeness but shouldn't be called through this path
      if (options['args']) {
        args.args = options['args'];
        delete options['args'];
      }
      break;
  }

  return args;
}

/**
 * Build display command string for UI.
 */
export function buildDisplayCommand(
  command: CommandType,
  prompt: PromptInfo,
  options: Record<string, any>
): string {
  const config = COMMANDS[command];
  const displayArg = command === CommandType.SYNC ? prompt.sync_basename : prompt.prompt;

  const optionsStr = Object.keys(options).length > 0
    ? ' ' + Object.entries(options).map(([k, v]) => {
        if (typeof v === 'boolean') return v ? `--${k.replace(/_/g, '-')}` : '';
        return `--${k.replace(/_/g, '-')} ${v}`;
      }).filter(Boolean).join(' ')
    : '';

  return `pdd ${config.backendName} ${displayArg}${optionsStr}`;
}

/**
 * Build complete CommandRequest and display string.
 * This is the main function that both App.tsx and AddToQueueModal.tsx should use.
 */
export function buildCommandRequest(
  command: CommandType,
  prompt: PromptInfo,
  rawOptions: Record<string, any> = {}
): {
  args: Record<string, any>;
  options: Record<string, any>;
  displayCommand: string;
  backendName: string;
} {
  const { options, codeFile, testFile } = cleanOptions(rawOptions, prompt);
  const args = buildCommandArgs(command, prompt, codeFile, testFile, options);
  const displayCommand = buildDisplayCommand(command, prompt, options);
  const config = COMMANDS[command];

  return {
    args,
    options,
    displayCommand,
    backendName: config.backendName,
  };
}

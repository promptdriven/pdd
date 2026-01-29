
import { CommandConfig, CommandType, GlobalOption, GlobalDefaults } from './types';

// Default values matching PDD CLI defaults
export const GLOBAL_DEFAULTS: GlobalDefaults = {
  strength: 1,
  temperature: 0.0,
  time: 0.25,
  verbose: false,
  quiet: false,
  force: false,
  local: false,
  reviewExamples: false,
};

// Global options that apply to all commands
export const GLOBAL_OPTIONS: GlobalOption[] = [
  {
    name: 'strength',
    cliFlag: '--strength',
    type: 'range',
    placeholder: '1',
    description: 'Model strength: <0.5 = cheaper models, 0.5 = base, >0.5 = stronger models',
    defaultValue: GLOBAL_DEFAULTS.strength,
    min: 0,
    max: 1,
    step: 0.05,
  },
  {
    name: 'temperature',
    cliFlag: '--temperature',
    type: 'range',
    placeholder: '0.0',
    description: 'LLM creativity level (0 = deterministic, higher = more creative)',
    defaultValue: GLOBAL_DEFAULTS.temperature,
    min: 0,
    max: 2,
    step: 0.1,
  },
  {
    name: 'time',
    cliFlag: '--time',
    type: 'range',
    placeholder: '0.25',
    description: 'Reasoning allocation for compatible models (0 = minimal, 1 = maximum)',
    defaultValue: GLOBAL_DEFAULTS.time,
    min: 0,
    max: 1,
    step: 0.05,
  },
  {
    name: 'verbose',
    cliFlag: '--verbose',
    type: 'checkbox',
    placeholder: '',
    description: 'Increase output verbosity for debugging',
    defaultValue: GLOBAL_DEFAULTS.verbose,
  },
  {
    name: 'quiet',
    cliFlag: '--quiet',
    type: 'checkbox',
    placeholder: '',
    description: 'Decrease output verbosity',
    defaultValue: GLOBAL_DEFAULTS.quiet,
  },
  {
    name: 'force',
    cliFlag: '--force',
    type: 'checkbox',
    placeholder: '',
    description: 'Skip interactive prompts (useful for automation)',
    defaultValue: GLOBAL_DEFAULTS.force,
  },
  {
    name: 'local',
    cliFlag: '--local',
    type: 'checkbox',
    placeholder: '',
    description: 'Run commands locally instead of in the cloud',
    defaultValue: GLOBAL_DEFAULTS.local,
  },
  {
    name: 'review-examples',
    cliFlag: '--review-examples',
    type: 'checkbox',
    placeholder: '',
    description: 'Review and optionally exclude few-shot examples before execution',
    defaultValue: GLOBAL_DEFAULTS.reviewExamples,
  },
];

// Simplified commands that match actual PDD CLI
export const COMMANDS: Record<CommandType, CommandConfig> = {
  [CommandType.SYNC]: {
    name: CommandType.SYNC,
    backendName: 'sync',
    description: "Synchronize a prompt with its code, tests, and examples. Generates missing files and fixes failing tests.",
    shortDescription: "Sync",
    icon: "🔄",
    requiresPrompt: true,
    group: "sync-update",
    options: [
      { name: 'agentic', type: 'checkbox', placeholder: '', description: 'Use agentic mode (skip iterative loops, trust agent results)', defaultValue: true },
      { name: 'max-attempts', type: 'number', placeholder: '3', description: 'Maximum fix attempts', defaultValue: '3' },
      { name: 'budget', type: 'number', placeholder: '20', description: 'Maximum cost in dollars', defaultValue: '20' },
      { name: 'skip-tests', type: 'checkbox', placeholder: '', description: 'Skip test generation' },
    ]
  },
  [CommandType.UPDATE]: {
    name: CommandType.UPDATE,
    backendName: 'update',
    description: "Update prompts based on code changes. Syncs prompt content with modified code.",
    shortDescription: "Update",
    icon: "📝",
    requiresPrompt: true,
    requiresCode: true,
    group: "sync-update",
    options: [
      { name: 'git', type: 'checkbox', placeholder: '', description: 'Use git history to find original code' },
      { name: 'simple', type: 'checkbox', placeholder: '', description: 'Use legacy 2-stage LLM update' },
    ]
  },
  [CommandType.GENERATE]: {
    name: CommandType.GENERATE,
    backendName: 'generate',
    description: "Generate code from a prompt file. Creates new implementation based on the prompt specification.",
    shortDescription: "Generate code",
    icon: "⚡",
    requiresPrompt: true,
    group: "generate",
    options: [
      { name: 'output', type: 'file', placeholder: 'e.g., src/calculator.py', description: 'Where to save generated code' },
      { name: 'incremental', type: 'checkbox', placeholder: '', description: 'Use incremental patching' },
    ]
  },
  [CommandType.TEST]: {
    name: CommandType.TEST,
    backendName: 'test',
    description: "Generate unit tests for existing code based on its prompt specification.",
    shortDescription: "Generate tests",
    icon: "🧪",
    requiresPrompt: true,
    requiresCode: true,
    group: "generate",
    options: [
      { name: 'output', type: 'file', placeholder: 'e.g., tests/test_calculator.py', description: 'Where to save generated tests' },
      { name: 'target-coverage', type: 'number', placeholder: '80', description: 'Target code coverage %' },
    ]
  },
  [CommandType.EXAMPLE]: {
    name: CommandType.EXAMPLE,
    backendName: 'example',
    description: "Generate example code that demonstrates how to use the implementation.",
    shortDescription: "Generate example",
    icon: "📖",
    requiresPrompt: true,
    requiresCode: true,
    group: "generate",
    options: [
      { name: 'output', type: 'file', placeholder: 'e.g., examples/calculator_example.py', description: 'Where to save generated example' },
    ]
  },
  [CommandType.FIX]: {
    name: CommandType.FIX,
    backendName: 'fix',
    description: "Fix code based on failing tests. Requires an error file with test output.",
    shortDescription: "Fix failing tests",
    icon: "🔧",
    requiresPrompt: true,
    requiresCode: true,
    requiresTest: true,
    options: [
      { name: 'error-file', type: 'file', placeholder: 'e.g., error.log or test_output.txt', description: 'File containing test errors (required)', required: true },
      { name: 'max-attempts', type: 'number', placeholder: '3', description: 'Maximum fix attempts', defaultValue: '3' },
      { name: 'budget', type: 'number', placeholder: '5', description: 'Maximum cost in dollars', defaultValue: '5' },
      { name: 'loop', type: 'checkbox', placeholder: '', description: 'Enable iterative fixing (requires verification-program)' },
      { name: 'verification-program', type: 'file', placeholder: 'verify.py', description: 'Python program that verifies the fix (required for --loop)' },
      { name: 'agentic-fallback', type: 'checkbox', placeholder: '', description: 'Enable agentic fallback if primary fix fails' },
      { name: 'auto-submit', type: 'checkbox', placeholder: '', description: 'Auto-submit if all tests pass' },
    ]
  },
  [CommandType.BUG]: {
    name: CommandType.BUG,
    backendName: 'bug',
    description: "Investigate a bug from a GitHub issue URL (agentic mode) or generate a reproducing test case.",
    shortDescription: "Investigate bug",
    icon: "🐛",
    requiresPrompt: false,
    options: [
      { name: 'issue-url', type: 'text', placeholder: 'https://github.com/org/repo/issues/123', description: 'GitHub issue URL to investigate', required: true },
      { name: 'output', type: 'file', placeholder: 'e.g., tests/test_bug_123.py', description: 'Where to save generated test' },
    ]
  },
  [CommandType.CRASH]: {
    name: CommandType.CRASH,
    backendName: 'crash',
    description: "Fix code based on crash errors. Analyzes error file and proposes fixes.",
    shortDescription: "Crash Fix",
    icon: "💥",
    requiresPrompt: true,
    requiresCode: true,
    options: [
      { name: 'program-file', type: 'file', placeholder: 'program.py', description: 'Program file that crashed', required: true },
      { name: 'error-file', type: 'file', placeholder: 'error.log', description: 'File containing error messages', required: true },
      { name: 'output', type: 'file', placeholder: 'src/fixed_code.py', description: 'Where to save fixed code' },
      { name: 'output-program', type: 'file', placeholder: 'program_fixed.py', description: 'Where to save fixed program' },
      { name: 'loop', type: 'checkbox', placeholder: '', description: 'Enable iterative fixing process' },
      { name: 'max-attempts', type: 'number', placeholder: '3', description: 'Maximum fix attempts', defaultValue: 3 },
      { name: 'budget', type: 'number', placeholder: '5', description: 'Maximum cost in dollars', defaultValue: 5 },
    ]
  },
  [CommandType.VERIFY]: {
    name: CommandType.VERIFY,
    backendName: 'verify',
    description: "Verify code against prompt requirements using a verification program.",
    shortDescription: "Verify",
    icon: "✅",
    requiresPrompt: true,
    requiresCode: true,
    options: [
      { name: 'verification-program', type: 'file', placeholder: 'verify.py', description: 'Verification program to run', required: true },
      { name: 'output-code', type: 'file', placeholder: 'src/verified_code.py', description: 'Where to save verified code' },
      { name: 'output-program', type: 'file', placeholder: 'verify_fixed.py', description: 'Where to save fixed verification program' },
      { name: 'output-results', type: 'file', placeholder: 'results.log', description: 'Where to save verification results' },
      { name: 'max-attempts', type: 'number', placeholder: '3', description: 'Maximum verification attempts', defaultValue: 3 },
      { name: 'budget', type: 'number', placeholder: '5', description: 'Maximum cost in dollars', defaultValue: 5 },
      { name: 'agentic-fallback', type: 'checkbox', placeholder: '', description: 'Enable agentic fallback if primary fix fails', defaultValue: true },
    ]
  },
  [CommandType.SUBMIT_EXAMPLE]: {
    name: CommandType.SUBMIT_EXAMPLE,
    backendName: 'fix',  // Uses fix command under the hood
    description: "Submit a successful fix as a few-shot example to PDD Cloud. Runs fix --loop --auto-submit with verification to iteratively fix and submit the example.",
    shortDescription: "Submit Example",
    icon: "🚀",
    requiresPrompt: true,
    requiresCode: true,
    requiresTest: true,
    options: [
      { name: 'verification-program', type: 'file', placeholder: 'examples/calculator_example.py', description: 'Verification program to check the fix (required). The example file typically serves as the verification program.', required: true },
      { name: 'max-attempts', type: 'number', placeholder: '5', description: 'Maximum fix attempts before giving up', defaultValue: 5 },
      { name: 'budget', type: 'number', placeholder: '10', description: 'Maximum cost in dollars', defaultValue: 10 },
    ]
  },

  // Advanced Operations
  [CommandType.SPLIT]: {
    name: CommandType.SPLIT,
    backendName: 'split',
    description: "Split a large prompt file into smaller, manageable sub-prompts for better organization and modularity.",
    shortDescription: "Split Prompt",
    icon: "›",
    requiresPrompt: true,
    requiresCode: true,  // Uses _code field for INPUT_CODE positional arg
    isAdvanced: true,
    options: [
      // Note: INPUT_PROMPT comes from selected prompt, INPUT_CODE comes from _code field
      { name: 'example-code', type: 'file', placeholder: 'examples/interface.py', description: 'Example code as interface to sub-module', required: true },
      { name: 'output-sub', type: 'file', placeholder: 'prompts/sub_module.prompt', description: 'Output path for the sub-prompt file' },
      { name: 'output-modified', type: 'file', placeholder: 'prompts/modified.prompt', description: 'Output path for the modified prompt file' },
    ]
  },
  [CommandType.CHANGE]: {
    name: CommandType.CHANGE,
    backendName: 'change',
    description: "Modify a prompt based on change instructions from a change prompt file.",
    shortDescription: "Change Prompt",
    icon: "›",
    requiresPrompt: true,
    requiresCode: true,  // Uses _code field for INPUT_CODE positional arg
    isAdvanced: true,
    options: [
      // Note: INPUT_CODE comes from _code field, INPUT_PROMPT comes from selected prompt
      { name: 'change-prompt', type: 'file', placeholder: 'changes.prompt', description: 'File containing change instructions', required: true },
      { name: 'budget', type: 'number', placeholder: '5', description: 'Maximum cost in dollars', defaultValue: '5' },
      { name: 'output', type: 'file', placeholder: 'prompts/modified.prompt', description: 'Output path for modified prompt' },
    ]
  },
  [CommandType.DETECT]: {
    name: CommandType.DETECT,
    backendName: 'detect',
    description: "Analyze prompts to determine which ones need changes based on a change description file.",
    shortDescription: "Detect Changes",
    icon: "›",
    requiresPrompt: false,
    isAdvanced: true,
    options: [
      { name: 'prompt-files', type: 'text', placeholder: 'file1.prompt, file2.prompt', description: 'Comma-separated list of prompt files to analyze', required: true },
      { name: 'change-file', type: 'file', placeholder: 'changes.prompt', description: 'File describing the changes to detect', required: true },
      { name: 'output', type: 'file', placeholder: 'detect_results.csv', description: 'Output CSV file for analysis results' },
    ]
  },
  [CommandType.AUTO_DEPS]: {
    name: CommandType.AUTO_DEPS,
    backendName: 'auto-deps',
    description: "Analyze project dependencies and update the prompt file with discovered dependencies.",
    shortDescription: "Auto Dependencies",
    icon: "›",
    requiresPrompt: true,
    isAdvanced: true,
    options: [
      { name: 'directory-path', type: 'text', placeholder: 'src/', description: 'Directory to scan for dependencies', required: true },
      { name: 'output', type: 'file', placeholder: 'prompts/updated.prompt', description: 'Where to save modified prompt' },
      { name: 'csv', type: 'file', placeholder: 'deps.csv', description: 'CSV file for dependency info' },
      { name: 'force-scan', type: 'checkbox', placeholder: '', description: 'Force rescan all files' },
    ]
  },
  [CommandType.CONFLICTS]: {
    name: CommandType.CONFLICTS,
    backendName: 'conflicts',
    description: "Check for conflicts between two prompt files.",
    shortDescription: "Check Conflicts",
    icon: "›",
    requiresPrompt: true,
    isAdvanced: true,
    options: [
      { name: 'prompt2', type: 'file', placeholder: 'prompts/other.prompt', description: 'Second prompt file to compare', required: true },
      { name: 'output', type: 'file', placeholder: 'conflicts.csv', description: 'Where to save conflict analysis' },
    ]
  },
  [CommandType.PREPROCESS]: {
    name: CommandType.PREPROCESS,
    backendName: 'preprocess',
    description: "Preprocess a prompt file to prepare it for LLM use.",
    shortDescription: "Preprocess",
    icon: "›",
    requiresPrompt: true,
    isAdvanced: true,
    options: [
      { name: 'output', type: 'file', placeholder: 'prompts/preprocessed.prompt', description: 'Where to save preprocessed prompt' },
      { name: 'xml', type: 'checkbox', placeholder: '', description: 'Insert XML delimiters for structure' },
      { name: 'recursive', type: 'checkbox', placeholder: '', description: 'Recursively preprocess includes' },
      { name: 'double', type: 'checkbox', placeholder: '', description: 'Double curly brackets' },
    ]
  },
};

// Get command by backend name
export function getCommandByBackendName(backendName: string): CommandConfig | undefined {
  return Object.values(COMMANDS).find(cmd => cmd.backendName === backendName);
}

// Supported languages for prompt creation
export const SUPPORTED_LANGUAGES = [
  { value: 'python', label: 'Python' },
  { value: 'typescript', label: 'TypeScript' },
  { value: 'javascript', label: 'JavaScript' },
  { value: 'java', label: 'Java' },
  { value: 'go', label: 'Go' },
  { value: 'rust', label: 'Rust' },
] as const;

// Generate template content for new prompts
export function getPromptTemplate(name: string, language: string, description?: string): string {
  const desc = description?.trim() || `[describe what ${name} should do]`;
  return `Write a ${language} module "${name}" that ${desc}.

## Requirements

- [Add your requirements here]

## Inputs

- [Define input parameters]

## Outputs

- [Define expected outputs]
`;
}

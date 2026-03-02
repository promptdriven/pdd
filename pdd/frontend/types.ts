// Simplified command types that match actual PDD CLI commands
export enum CommandType {
  SYNC = 'sync',
  UPDATE = 'update',
  GENERATE = 'generate',
  TEST = 'test',
  EXAMPLE = 'example',
  FIX = 'fix',
  BUG = 'bug',
  CRASH = 'crash',
  VERIFY = 'verify',
  SUBMIT_EXAMPLE = 'submit-example',
  // Advanced operations
  SPLIT = 'split',
  CHANGE = 'change',
  DETECT = 'detect',
  AUTO_DEPS = 'auto-deps',
  CONFLICTS = 'conflicts',
  PREPROCESS = 'preprocess',
}

export interface CommandOption {
  name: string;
  type: 'text' | 'textarea' | 'file' | 'number' | 'checkbox' | 'range';
  placeholder: string;
  description: string;
  required?: boolean;
  defaultValue?: string | number | boolean;
  // For range type
  min?: number;
  max?: number;
  step?: number;
}

// Global options that apply to all commands
export interface GlobalOption extends CommandOption {
  cliFlag: string;  // The actual CLI flag (e.g., '--strength')
}

// Default values for global options
export interface GlobalDefaults {
  strength: number;
  temperature: number;
  time: number;
  verbose: boolean;
  quiet: boolean;
  force: boolean;
  local: boolean;
  reviewExamples: boolean;
}

export interface CommandConfig {
  name: CommandType;
  backendName: string;  // The actual CLI command name
  description: string;
  shortDescription: string;  // For button labels
  icon: string;  // Emoji or simple character icon
  options: CommandOption[];
  // What files this command needs
  requiresPrompt: boolean;
  requiresCode?: boolean;
  requiresTest?: boolean;
  // Group related commands (e.g., sync and update share a dropdown)
  group?: string;
  // If true, shown in "Advanced Operations" section
  isAdvanced?: boolean;
}

// A prompt file with its related dev-unit files
export interface PromptInfo {
  prompt: string;      // Path to .prompt file
  basename: string;    // Base name (e.g., "calculator" from "calculator.prompt")
  code?: string;       // Path to source code file if exists
  test?: string;       // Path to test file if exists
  example?: string;    // Path to example file if exists
}

export interface DevUnit {
  prompt: string;
  code: string;
  example: string;
  test: string;
}

export interface MockPrompt {
  id: string;
  includes: string[];
  devUnit: DevUnit;
}

// Architecture types for PRD-driven project building
export interface ArchitectureInterface {
  type: 'page' | 'component' | 'module' | 'api' | 'graphql' | 'cli' | 'job' | 'message' | 'config';
  page?: {
    route: string;
    params?: { name: string; type: string; description?: string }[];
    dataSources?: { kind: string; source: string; method?: string; description?: string }[];
  };
  component?: {
    props: { name: string; type: string; required?: boolean; description?: string }[];
    emits?: string[];
    context?: string[];
  };
  module?: {
    functions: { name: string; signature: string; returns?: string; errors?: string[]; sideEffects?: string[] }[];
  };
  api?: {
    endpoints: { method: string; path: string; auth?: string; requestSchema?: any; responseSchema?: any }[];
  };
  graphql?: {
    sdl?: string;
    queries?: string[];
    mutations?: string[];
    subscriptions?: string[];
  };
  cli?: {
    commands: { name: string; args?: string[]; flags?: string[]; exitCodes?: number[] }[];
    io?: { stdin?: string; stdout?: string };
  };
  job?: {
    trigger: { schedule?: string; event?: string };
    inputs?: string[];
    outputs?: string[];
    retryPolicy?: string;
  };
  message?: {
    topics: { name: string; direction: 'publish' | 'subscribe'; schema?: any; qos?: string }[];
  };
  config?: {
    keys: { name: string; type: string; default?: any; required?: boolean; source: 'env' | 'file' | 'secret' }[];
  };
}

export interface ArchitectureModule {
  reason: string;
  description: string;
  dependencies: string[];
  priority: number;
  filename: string;
  filepath: string;
  tags?: string[];
  interface?: ArchitectureInterface;
  // Graph position (optional, saved when user drags nodes)
  position?: {
    x: number;
    y: number;
  };
  // Optional group name for graph layout hierarchy
  group?: string;
}

export interface ProjectArchitecture {
  appName?: string;
  prdPath?: string;
  techStackPath?: string;
  modules: ArchitectureModule[];
}

// .pddrc configuration types
export interface PddrcContextDefaults {
  generate_output_path?: string;
  test_output_path?: string;
  example_output_path?: string;
  prompts_dir?: string;
  default_language?: string;
  strength?: number;
  temperature?: number;
  budget?: number;
  max_attempts?: number;
}

export interface PddrcContext {
  paths: string[];
  defaults: PddrcContextDefaults;
}

export interface PddrcConfig {
  version?: string;
  contexts: Record<string, PddrcContext>;
}

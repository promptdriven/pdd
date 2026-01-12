/**
 * PDD Server API Client
 *
 * Communicates with the PDD REST API backend for command execution,
 * file operations, and real-time streaming.
 */

import YAML from 'yaml';
import type { PddrcConfig } from './types';

// API Configuration
// In development with Vite proxy, use relative URLs
// In production or when connecting directly, use the full URL
const API_BASE_URL = import.meta.env.VITE_API_URL || '';
const WS_BASE_URL = API_BASE_URL
  ? API_BASE_URL.replace('http', 'ws')
  : `ws://${window.location.host}`;

// Types
export interface ServerStatus {
  version: string;
  project_root: string;
  uptime_seconds: number;
  active_jobs: number;
  connected_clients: number;
}

export interface CommandInfo {
  name: string;
  description: string;
}

export interface JobHandle {
  job_id: string;
  status: 'queued' | 'running' | 'completed' | 'failed' | 'cancelled';
  created_at: string;
}

export interface JobResult {
  job_id: string;
  status: 'queued' | 'running' | 'completed' | 'failed' | 'cancelled';
  result: any;
  error: string | null;
  cost: number;
  duration_seconds: number;
  completed_at: string | null;
}

export interface FileTreeNode {
  name: string;
  path: string;
  type: 'file' | 'directory';
  children?: FileTreeNode[];
  size?: number;
  mtime?: string;
}

export interface FileContent {
  path: string;
  content: string;
  encoding: 'utf-8' | 'base64';
  size: number;
  is_binary: boolean;
  checksum?: string;
}

export interface PromptInfo {
  prompt: string;           // Full path: "prompts/calculator_python.prompt"
  sync_basename: string;    // For sync command: "calculator" (without language suffix)
  language?: string;        // Detected language: "python"
  context?: string;         // Matched .pddrc context name
  code?: string;
  test?: string;
  example?: string;
}

export interface CommandRequest {
  command: string;
  args?: Record<string, any>;
  options?: Record<string, any>;
}

export interface RunResult {
  success: boolean;
  message: string;
  exit_code: number;
  stdout?: string | null;
  stderr?: string | null;
  error_details?: string | null;
}

export interface CancelResult {
  cancelled: boolean;
  message: string;
}

export interface CommandStatus {
  running: boolean;
  command: string | null;
}

export interface SpawnTerminalResponse {
  success: boolean;
  message: string;
  command: string;
  platform: string;
  job_id?: string;
}

export interface SpawnedJobStatus {
  job_id: string;
  command: string;
  status: 'running' | 'completed' | 'failed' | 'unknown';
  started_at: string;
  completed_at?: string;
  exit_code?: number;
}

// Token metrics types
export interface CostEstimate {
  input_cost: number;
  model: string;
  tokens: number;
  cost_per_million: number;
  currency: string;
}

export interface TokenMetrics {
  token_count: number;
  context_limit: number;
  context_usage_percent: number;
  cost_estimate: CostEstimate | null;
}

export interface PromptAnalyzeRequest {
  path: string;
  model?: string;
  preprocess?: boolean;
  content?: string;  // Optional content to analyze instead of reading from file
}

export interface PromptAnalyzeResponse {
  raw_content: string;
  processed_content: string | null;
  raw_metrics: TokenMetrics;
  processed_metrics: TokenMetrics | null;
  preprocessing_succeeded: boolean;
  preprocessing_error: string | null;
}

// Sync status types
export type SyncStatusType = 'in_sync' | 'prompt_changed' | 'code_changed' | 'conflict' | 'never_synced';

export interface SyncStatus {
  status: SyncStatusType;
  last_sync_timestamp: string | null;
  last_sync_command: string | null;
  prompt_modified: boolean;
  code_modified: boolean;
  fingerprint_exists: boolean;
  prompt_exists: boolean;
  code_exists: boolean;
}

// Model information types
export interface ModelInfo {
  model: string;           // Full model identifier (e.g., "gpt-5.1-codex-mini")
  provider: string;        // Model provider (e.g., "OpenAI", "Anthropic")
  input_cost: number;      // Input cost per million tokens (USD)
  output_cost: number;     // Output cost per million tokens (USD)
  elo: number;             // Coding arena ELO rating
  context_limit: number;   // Maximum context window size in tokens
  max_thinking_tokens: number;  // Maximum thinking/reasoning tokens (0 if not supported)
  reasoning_type: string;  // "none", "effort", or "budget"
  structured_output: boolean;  // Whether the model supports structured output
}

export interface ModelsResponse {
  models: ModelInfo[];
  default_model: string;
}

// Match check types
export interface MatchCheckRequest {
  prompt_content: string;
  code_content: string;
  strength?: number;  // 0-1
}

export interface MatchCheckResult {
  match_score: number;
  summary: string;
  missing?: string[];
  extra?: string[];
  suggestions?: string[];
}

export interface MatchCheckResponse {
  result: MatchCheckResult;
  cost: number;
  model: string;
}

// Architecture types (re-exported for convenience)
export interface ArchitectureModule {
  reason: string;
  description: string;
  dependencies: string[];
  priority: number;
  filename: string;
  filepath: string;
  tags?: string[];
  interface?: {
    type: string;
    [key: string]: any;
  };
}

export interface ArchitectureCheckResult {
  exists: boolean;
  path?: string;
}

// Auth types
export interface AuthStatus {
  authenticated: boolean;
  cached: boolean;
  expires_at: number | null;
}

export interface LogoutResult {
  success: boolean;
  message: string;
}

export interface LoginResponse {
  success: boolean;
  user_code?: string;
  verification_uri?: string;
  expires_in?: number;
  poll_id?: string;
  error?: string;
}

export interface LoginPollResponse {
  status: 'pending' | 'completed' | 'expired' | 'error';
  message?: string;
}

// Global options that can be passed to any generation command
export interface GenerationGlobalOptions {
  strength?: number;      // 0-1, model strength
  temperature?: number;   // 0-2, LLM creativity
  time?: number;          // 0-1, reasoning allocation
  verbose?: boolean;
  quiet?: boolean;
  force?: boolean;
  local?: boolean;        // Run locally instead of cloud
}

export interface GenerateArchitectureRequest {
  prdPath?: string;        // Path to existing PRD file
  prdContent?: string;     // Or provide content directly
  techStackPath?: string;
  techStackContent?: string;
  appName?: string;
  outputPath?: string;
  globalOptions?: GenerationGlobalOptions;
}

// Generate prompt from architecture types
export interface GeneratePromptFromArchRequest {
  module: string;           // e.g., "orders"
  langOrFramework: string;  // e.g., "Python"
  architectureFile?: string; // default: "architecture.json"
  prdFile?: string;         // optional PRD for context
  techStackFile?: string;   // optional tech stack
  outputPath?: string;      // default: prompts/${module}_${lang}.prompt
  globalOptions?: GenerationGlobalOptions;
}

export interface BatchGeneratePromptsRequest {
  modules: Array<{ module: string; langOrFramework: string }>;
  architectureFile?: string;
  prdFile?: string;
  techStackFile?: string;
  globalOptions?: GenerationGlobalOptions;
}

export interface PromptGenerationResult {
  module: string;
  success: boolean;
  error?: string;
}

// API Client
class PDDApiClient {
  private baseUrl: string;
  private wsBaseUrl: string;

  constructor(baseUrl: string = API_BASE_URL) {
    this.baseUrl = baseUrl;
    this.wsBaseUrl = baseUrl.replace('http', 'ws');
  }

  // Helper for fetch requests
  private async request<T>(endpoint: string, options?: RequestInit): Promise<T> {
    const response = await fetch(`${this.baseUrl}${endpoint}`, {
      ...options,
      headers: {
        'Content-Type': 'application/json',
        ...options?.headers,
      },
    });

    if (!response.ok) {
      const error = await response.json().catch(() => ({ detail: response.statusText }));
      throw new Error(error.detail || `API Error: ${response.status}`);
    }

    return response.json();
  }

  // Status
  async getStatus(): Promise<ServerStatus> {
    return this.request<ServerStatus>('/api/v1/status');
  }

  // Auth
  async getAuthStatus(): Promise<AuthStatus> {
    return this.request<AuthStatus>('/api/v1/auth/status');
  }

  async logout(): Promise<LogoutResult> {
    return this.request<LogoutResult>('/api/v1/auth/logout', {
      method: 'POST',
    });
  }

  async startLogin(): Promise<LoginResponse> {
    return this.request<LoginResponse>('/api/v1/auth/login', {
      method: 'POST',
    });
  }

  async pollLoginStatus(pollId: string): Promise<LoginPollResponse> {
    return this.request<LoginPollResponse>(`/api/v1/auth/login/poll/${encodeURIComponent(pollId)}`);
  }

  // Commands
  async getAvailableCommands(): Promise<CommandInfo[]> {
    return this.request<CommandInfo[]>('/api/v1/commands/available');
  }

  async executeCommand(request: CommandRequest): Promise<JobHandle> {
    return this.request<JobHandle>('/api/v1/commands/execute', {
      method: 'POST',
      body: JSON.stringify(request),
    });
  }

  /**
   * Run a command in terminal mode.
   * Output goes directly to the terminal where the server is running.
   * This method blocks until the command completes.
   */
  async runCommand(request: CommandRequest): Promise<RunResult> {
    return this.request<RunResult>('/api/v1/commands/run', {
      method: 'POST',
      body: JSON.stringify(request),
    });
  }

  /**
   * Cancel the currently running command.
   */
  async cancelCommand(): Promise<CancelResult> {
    return this.request<CancelResult>('/api/v1/commands/cancel', {
      method: 'POST',
    });
  }

  /**
   * Get the status of the current running command.
   */
  async getCommandStatus(): Promise<CommandStatus> {
    return this.request<CommandStatus>('/api/v1/commands/status');
  }

  async getJobStatus(jobId: string): Promise<JobResult> {
    return this.request<JobResult>(`/api/v1/commands/jobs/${jobId}`);
  }

  async cancelJob(jobId: string): Promise<{ cancelled: boolean; message: string }> {
    return this.request(`/api/v1/commands/jobs/${jobId}/cancel`, {
      method: 'POST',
    });
  }

  async getJobHistory(limit: number = 50, offset: number = 0): Promise<JobResult[]> {
    return this.request<JobResult[]>(`/api/v1/commands/history?limit=${limit}&offset=${offset}`);
  }

  /**
   * Spawn a command in a new terminal window.
   * The command runs in complete isolation from the server.
   */
  async spawnTerminal(request: CommandRequest): Promise<SpawnTerminalResponse> {
    return this.request<SpawnTerminalResponse>('/api/v1/commands/spawn-terminal', {
      method: 'POST',
      body: JSON.stringify(request),
    });
  }

  /**
   * Get the status of a spawned job.
   * Used for polling to check if spawned terminal commands have completed.
   */
  async getSpawnedJobStatus(jobId: string): Promise<SpawnedJobStatus> {
    return this.request<SpawnedJobStatus>(`/api/v1/commands/spawned-jobs/${jobId}/status`);
  }

  // Files
  async getFileTree(path: string = '', depth: number = 3): Promise<FileTreeNode> {
    const params = new URLSearchParams();
    if (path) params.set('path', path);
    params.set('depth', depth.toString());
    return this.request<FileTreeNode>(`/api/v1/files/tree?${params}`);
  }

  async getFileContent(path: string): Promise<FileContent> {
    return this.request<FileContent>(`/api/v1/files/content?path=${encodeURIComponent(path)}`);
  }

  async writeFile(path: string, content: string, encoding: 'utf-8' | 'base64' = 'utf-8'): Promise<{ success: boolean; path: string; mtime?: string; error?: string }> {
    return this.request('/api/v1/files/write', {
      method: 'POST',
      body: JSON.stringify({ path, content, encoding }),
    });
  }

  /**
   * Read .pddrc configuration file.
   * Returns null if file doesn't exist.
   */
  async getPddrc(): Promise<PddrcConfig | null> {
    try {
      const content = await this.getFileContent('.pddrc');
      return YAML.parse(content.content) as PddrcConfig;
    } catch {
      return null;
    }
  }

  /**
   * Save .pddrc configuration file.
   */
  async savePddrc(config: PddrcConfig): Promise<{ success: boolean; error?: string }> {
    const yamlContent = YAML.stringify(config);
    return this.writeFile('.pddrc', yamlContent);
  }

  // List all prompt files in the project with related dev-unit files
  async listPrompts(): Promise<PromptInfo[]> {
    return this.request<PromptInfo[]>('/api/v1/files/prompts');
  }

  /**
   * Analyze a prompt file: get preprocessed content and token metrics.
   * Does not execute any commands - purely for preview and cost estimation.
   */
  async analyzePrompt(request: PromptAnalyzeRequest): Promise<PromptAnalyzeResponse> {
    return this.request<PromptAnalyzeResponse>('/api/v1/prompts/analyze', {
      method: 'POST',
      body: JSON.stringify(request),
    });
  }

  /**
   * Analyze a single file for token metrics.
   * Convenience method for analyzing include files without preprocessing.
   */
  async analyzeFile(path: string, model?: string): Promise<TokenMetrics> {
    const response = await this.analyzePrompt({
      path,
      model: model || 'claude-sonnet-4-20250514',
      preprocess: false,  // Don't preprocess - just count tokens in the raw file
    });
    return response.raw_metrics;
  }

  /**
   * Get the sync status for a prompt/code pair.
   * Returns whether the prompt and code are in sync, or if either has been modified.
   */
  async getSyncStatus(basename: string, language: string): Promise<SyncStatus> {
    return this.request<SyncStatus>(
      `/api/v1/prompts/sync-status?basename=${encodeURIComponent(basename)}&language=${encodeURIComponent(language)}`
    );
  }

  /**
   * Get list of available LLM models with their capabilities.
   * Returns model information including context limits, pricing, and thinking capacity.
   */
  async getModels(): Promise<ModelsResponse> {
    return this.request<ModelsResponse>('/api/v1/prompts/models');
  }

  /**
   * Check how well code matches the prompt requirements using LLM judge.
   * Returns a match score, summary, missing requirements, and suggestions.
   */
  async checkMatch(request: MatchCheckRequest): Promise<MatchCheckResponse> {
    return this.request<MatchCheckResponse>('/api/v1/prompts/check-match', {
      method: 'POST',
      body: JSON.stringify(request),
    });
  }

  // Architecture operations

  /**
   * Check if architecture.json exists in the project.
   */
  async checkArchitectureExists(): Promise<ArchitectureCheckResult> {
    try {
      // Try to get the file content - if it exists, return true
      await this.getFileContent('architecture.json');
      return { exists: true, path: 'architecture.json' };
    } catch {
      return { exists: false };
    }
  }

  /**
   * Load architecture.json from the project.
   * Returns the array of architecture modules.
   */
  async getArchitecture(): Promise<ArchitectureModule[]> {
    const content = await this.getFileContent('architecture.json');
    return JSON.parse(content.content) as ArchitectureModule[];
  }

  /**
   * List markdown files in the project for PRD/tech stack browser.
   * Searches common documentation directories.
   */
  async listMarkdownFiles(): Promise<string[]> {
    const files: string[] = [];

    // Get file tree and find .md files
    try {
      const tree = await this.getFileTree('', 4);
      const collectMdFiles = (node: FileTreeNode, currentPath: string = '') => {
        const path = currentPath ? `${currentPath}/${node.name}` : node.name;
        if (node.type === 'file' && node.name.endsWith('.md')) {
          files.push(path);
        }
        if (node.children) {
          for (const child of node.children) {
            collectMdFiles(child, path);
          }
        }
      };
      collectMdFiles(tree);
    } catch (e) {
      console.error('Failed to list markdown files:', e);
    }

    return files;
  }

  /**
   * Generate architecture.json from a PRD using the built-in template.
   * This runs the pdd generate command with the architecture template.
   */
  async generateArchitecture(request: GenerateArchitectureRequest): Promise<RunResult> {
    const env: Record<string, string> = {};

    // Set PRD file/content
    if (request.prdPath) {
      env['PRD_FILE'] = request.prdPath;
    } else if (request.prdContent) {
      // Write content to a temp file first
      const tempPath = '.pdd/temp_prd.md';
      await this.writeFile(tempPath, request.prdContent);
      env['PRD_FILE'] = tempPath;
    }

    // Set tech stack if provided
    if (request.techStackPath) {
      env['TECH_STACK_FILE'] = request.techStackPath;
    } else if (request.techStackContent) {
      const tempPath = '.pdd/temp_tech_stack.md';
      await this.writeFile(tempPath, request.techStackContent);
      env['TECH_STACK_FILE'] = tempPath;
    }

    // Set app name if provided
    if (request.appName) {
      env['APP_NAME'] = request.appName;
    }

    // Set output path
    const outputPath = request.outputPath || 'architecture.json';

    // Build env as array of "KEY=VALUE" strings for --env flag
    // The CLI expects: --env PRD_FILE=path --env APP_NAME=name (or -e shorthand)
    const envArgs: string[] = [];
    for (const [key, value] of Object.entries(env)) {
      envArgs.push(`${key}=${value}`);
    }

    // Build options object with global options
    const options: Record<string, any> = {
      output: outputPath,
      template: 'architecture/architecture_json',
      env: envArgs,  // Array of "KEY=VALUE" strings for --env flag
    };

    // Add global options if provided
    if (request.globalOptions) {
      const { strength, temperature, time, verbose, quiet, force } = request.globalOptions;
      if (strength !== undefined) options.strength = strength;
      if (temperature !== undefined) options.temperature = temperature;
      if (time !== undefined) options.time = time;
      if (verbose) options.verbose = true;
      if (quiet) options.quiet = true;
      if (force) options.force = true;
    }

    // Run the generate command with the architecture template
    // Note: When using --template, do NOT provide prompt_file (they are mutually exclusive)
    return this.runCommand({
      command: 'generate',
      args: {},  // No prompt_file when using template
      options,
    });
  }

  /**
   * Generate a single prompt file from architecture.json using the generic/generate_prompt template.
   */
  async generatePromptFromArchitecture(request: GeneratePromptFromArchRequest): Promise<RunResult> {
    const { module, langOrFramework, architectureFile, prdFile, techStackFile, outputPath, globalOptions } = request;

    const envArgs: string[] = [
      `MODULE=${module}`,
      `LANG_OR_FRAMEWORK=${langOrFramework}`,
      `ARCHITECTURE_FILE=${architectureFile || 'architecture.json'}`,
    ];

    if (prdFile) envArgs.push(`PRD_FILE=${prdFile}`);
    if (techStackFile) envArgs.push(`TECH_STACK_FILE=${techStackFile}`);

    // Build options object with global options
    const options: Record<string, any> = {
      template: 'generic/generate_prompt',
      env: envArgs,
      output: outputPath || `prompts/${module}_${langOrFramework}.prompt`,
    };

    // Add global options if provided
    if (globalOptions) {
      const { strength, temperature, time, verbose, quiet, force } = globalOptions;
      if (strength !== undefined) options.strength = strength;
      if (temperature !== undefined) options.temperature = temperature;
      if (time !== undefined) options.time = time;
      if (verbose) options.verbose = true;
      if (quiet) options.quiet = true;
      if (force) options.force = true;
    }

    return this.runCommand({
      command: 'generate',
      args: {},
      options,
    });
  }

  /**
   * Generate multiple prompts sequentially from architecture.json.
   * Calls generatePromptFromArchitecture for each module and reports progress.
   * Can be cancelled via shouldCancel callback.
   */
  async batchGeneratePrompts(
    request: BatchGeneratePromptsRequest,
    onProgress?: (current: number, total: number, module: string) => void,
    shouldCancel?: () => boolean
  ): Promise<PromptGenerationResult[]> {
    const results: PromptGenerationResult[] = [];
    const { modules, architectureFile, prdFile, techStackFile, globalOptions } = request;

    for (let i = 0; i < modules.length; i++) {
      // Check for cancellation before each module
      if (shouldCancel?.()) {
        break;
      }

      const { module, langOrFramework } = modules[i];
      onProgress?.(i + 1, modules.length, module);

      try {
        const result = await this.generatePromptFromArchitecture({
          module,
          langOrFramework,
          architectureFile,
          prdFile,
          techStackFile,
          globalOptions,
        });
        results.push({
          module: `${module}_${langOrFramework}`,
          success: result.success,
          error: result.success ? undefined : result.message,
        });
      } catch (e) {
        results.push({
          module: `${module}_${langOrFramework}`,
          success: false,
          error: e instanceof Error ? e.message : String(e),
        });
      }
    }

    return results;
  }

  // WebSocket for job streaming
  connectToJobStream(jobId: string, callbacks: {
    onMessage?: (type: string, data: any) => void;
    onStdout?: (text: string) => void;
    onStderr?: (text: string) => void;
    onProgress?: (current: number, total: number, message: string) => void;
    onComplete?: (success: boolean, result: any, cost: number) => void;
    onError?: (error: Error) => void;
    onClose?: () => void;
  }): WebSocket {
    const ws = new WebSocket(`${this.wsBaseUrl}/ws/jobs/${jobId}/stream`);

    ws.onmessage = (event) => {
      try {
        const message = JSON.parse(event.data);
        callbacks.onMessage?.(message.type, message.data);

        switch (message.type) {
          case 'stdout':
            callbacks.onStdout?.(message.data);
            break;
          case 'stderr':
            callbacks.onStderr?.(message.data);
            break;
          case 'progress':
            callbacks.onProgress?.(message.current, message.total, message.message);
            break;
          case 'complete':
            callbacks.onComplete?.(message.data?.success, message.data?.result, message.data?.cost || 0);
            break;
        }
      } catch (e) {
        console.error('Failed to parse WebSocket message:', e);
      }
    };

    ws.onerror = (event) => {
      callbacks.onError?.(new Error('WebSocket error'));
    };

    ws.onclose = () => {
      callbacks.onClose?.();
    };

    return ws;
  }

  // Cancel via WebSocket
  sendCancelRequest(ws: WebSocket): void {
    if (ws.readyState === WebSocket.OPEN) {
      ws.send(JSON.stringify({ type: 'cancel' }));
    }
  }
}

// Export singleton instance
export const api = new PDDApiClient();

// Export class for custom instances
export { PDDApiClient };

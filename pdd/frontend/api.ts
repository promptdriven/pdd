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
  expected_outputs?: string[];  // e.g., ["code"] for JSON/YAML, ["code","example","test"] for Python
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

// Diff analysis types (detailed prompt-code comparison)
export interface PromptRange {
  startLine: number;
  endLine: number;
  text: string;
}

export interface CodeRange {
  startLine: number;
  endLine: number;
  text: string;
}

export interface DiffSection {
  id: string;
  promptRange: PromptRange;
  codeRanges: CodeRange[];
  status: 'matched' | 'partial' | 'missing' | 'extra';
  matchConfidence: number;
  semanticLabel: string;
  notes: string;  // Required explanation of WHY this status exists
}

export interface LineMapping {
  promptLine: number;
  codeLines: number[];
  matchType: 'exact' | 'semantic' | 'partial' | 'none';
}

export interface HiddenKnowledge {
  type: 'magic_value' | 'algorithm_choice' | 'edge_case' | 'error_handling' | 'api_contract' | 'optimization' | 'business_logic' | 'assumption';
  location: { startLine: number; endLine: number };
  description: string;           // What the code knows that the prompt doesn't say
  regenerationImpact: 'would_differ' | 'would_fail' | 'might_work';
  suggestedPromptAddition: string;  // What to add to the prompt to capture this
}

export interface DiffStats {
  totalRequirements: number;
  matchedRequirements: number;
  missingRequirements: number;
  totalCodeFeatures: number;
  documentedFeatures: number;
  undocumentedFeatures: number;
  promptToCodeCoverage: number;  // % of prompt implemented in code
  codeToPromptCoverage: number;  // % of code documented in prompt
  hiddenKnowledgeCount: number;  // Number of hidden knowledge items found
  criticalGaps: number;          // Number of critical gaps that would cause regeneration failure
}

export interface DiffAnalysisResult {
  overallScore: number;           // Overall regeneration capability score 0-100
  canRegenerate: boolean;         // Conservative: could this prompt produce working code?
  regenerationRisk: 'low' | 'medium' | 'high' | 'critical';
  promptToCodeScore: number;      // How well code implements prompt
  codeToPromptScore: number;      // How well prompt describes code
  summary: string;                // Summary of regeneration viability
  sections: DiffSection[];        // Prompt requirements → code mappings
  codeSections: DiffSection[];    // Code features → prompt mappings
  hiddenKnowledge: HiddenKnowledge[];  // Undocumented code knowledge
  lineMappings: LineMapping[];
  stats: DiffStats;
  missing: string[];              // Requirements in prompt but not in code
  extra: string[];                // Code features that would be LOST on regeneration
  suggestions: string[];          // Specific additions to enable regeneration
}

export interface DiffAnalysisRequest {
  prompt_content: string;
  code_content: string;
  strength?: number;
  mode?: 'quick' | 'detailed';
  include_tests?: boolean;        // Include test content in analysis
  prompt_path?: string;           // Prompt path for auto-detecting tests
  code_path?: string;             // Code path for finding associated tests
}

export interface DiffAnalysisResponse {
  result: DiffAnalysisResult;
  cost: number;
  model: string;
  analysisMode: string;
  cached: boolean;
  tests_included: boolean;        // Whether tests were included in analysis
  test_files: string[];           // Test files included in analysis
}

// Prompt Version History types
export interface PromptVersionInfo {
  commit_hash: string;
  commit_date: string;
  commit_message: string;
  author: string;
  prompt_content: string;
}

export interface PromptHistoryRequest {
  prompt_path: string;
  limit?: number;
}

export interface PromptHistoryResponse {
  versions: PromptVersionInfo[];
  current_content: string;
  has_uncommitted_changes: boolean;
}

export interface LinguisticChange {
  change_type: 'added' | 'removed' | 'modified';
  category: 'requirement' | 'constraint' | 'behavior' | 'format';
  description: string;
  old_text?: string;
  new_text?: string;
  impact: 'breaking' | 'enhancement' | 'clarification';
}

export interface PromptDiffRequest {
  prompt_path: string;
  version_a: string;  // commit hash, 'HEAD', or 'working'
  version_b: string;
  code_path?: string;
  strength?: number;  // Model strength 0-1 for analysis quality
}

export interface PromptDiffResponse {
  prompt_a_content: string;
  prompt_b_content: string;
  text_diff: string;
  linguistic_changes: LinguisticChange[];
  code_diff?: string;
  summary: string;
  cost: number;
  model: string;
  version_a_label: string;  // Label for the older version
  version_b_label: string;  // Label for the newer version
  versions_swapped: boolean;  // Whether versions were auto-swapped to ensure old→new
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
  // Graph position (optional, saved when user drags nodes)
  position?: {
    x: number;
    y: number;
  };
  // Optional group name for graph layout hierarchy
  group?: string;
}

export interface ArchitectureCheckResult {
  exists: boolean;
  path?: string;
}

// Architecture validation types
export interface ArchitectureValidationError {
  type: 'circular_dependency' | 'missing_dependency' | 'invalid_field';
  message: string;
  modules: string[];
}

export interface ArchitectureValidationWarning {
  type: 'duplicate_dependency' | 'orphan_module';
  message: string;
  modules: string[];
}

export interface ArchitectureValidationResult {
  valid: boolean;
  errors: ArchitectureValidationError[];
  warnings: ArchitectureValidationWarning[];
}

// Architecture sync types
export interface ArchitectureSyncRequest {
  filenames?: string[] | null;  // null = sync all prompts
  dry_run?: boolean;
}

export interface ArchitectureSyncModuleResult {
  filename: string;
  success: boolean;
  updated: boolean;
  changes: {
    reason?: { old: string; new: string };
    interface?: { old: any; new: any };
    dependencies?: { old: string[]; new: string[] };
  };
  error?: string;
}

export interface ArchitectureSyncResult {
  success: boolean;
  updated_count: number;
  skipped_count: number;
  results: ArchitectureSyncModuleResult[];
  validation: ArchitectureValidationResult;
  errors: string[];
}

export interface GenerateTagsResult {
  success: boolean;
  tags: string | null;  // Generated XML tags or null if not found
  has_existing_tags: boolean;  // True if prompt already has PDD tags
  architecture_entry: Record<string, any> | null;  // The full architecture entry
  error: string | null;
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

// Remote session types
export interface RemoteSessionInfo {
  sessionId: string;
  cloudUrl: string;
  projectName: string;
  projectPath: string;
  createdAt: string;
  lastHeartbeat: string;
  status: 'active' | 'stale';
  metadata: {
    hostname: string;
    platform: string;
    pythonVersion: string;
  };
}

export interface RemoteCommandRequest {
  sessionId: string;
  type: string; // "generate", "fix", "test", etc.
  payload: {
    args?: Record<string, any>;
    options?: Record<string, any>;
  };
}

export interface RemoteCommandStatus {
  commandId: string;
  type: string;
  status: 'pending' | 'processing' | 'completed' | 'failed' | 'cancelled';
  createdAt: string;
  updatedAt?: string;
  response?: {
    success?: boolean;
    message?: string;
    exit_code?: number;
    stdout?: string;
    stderr?: string;
    files_created?: string[];
    cost?: number;
    streaming?: boolean;  // True when this is a streaming update (intermediate output)
    error?: string;
  };
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
  private cachedCloudUrl: string | null = null;

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

  async startLogin(options?: { no_browser?: boolean }): Promise<LoginResponse> {
    return this.request<LoginResponse>('/api/v1/auth/login', {
      method: 'POST',
      body: JSON.stringify(options || {}),
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
   * Get list of prompt files changed on the current branch compared to base.
   * Uses git diff to find .prompt files that are new or modified.
   *
   * @param baseBranch - Base branch to compare against (default: "main")
   * @returns List of changed prompt file paths
   */
  async getChangedPrompts(baseBranch: string = 'main'): Promise<{ changed_prompts: string[]; base_branch: string }> {
    return this.request<{ changed_prompts: string[]; base_branch: string }>(
      `/api/v1/files/prompts/changed?base_branch=${encodeURIComponent(baseBranch)}`
    );
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
   * Perform detailed diff analysis between prompt and code.
   * Returns semantic sections with line-level mappings showing how each
   * requirement in the prompt corresponds to code implementation.
   *
   * @param request.prompt_content - The prompt/requirements content
   * @param request.code_content - The code content to analyze
   * @param request.strength - Model strength (0-1), default 0.5
   * @param request.mode - Analysis mode: 'quick' (faster) or 'detailed' (more accurate)
   */
  async analyzeDiff(request: DiffAnalysisRequest): Promise<DiffAnalysisResponse> {
    return this.request<DiffAnalysisResponse>('/api/v1/prompts/diff-analysis', {
      method: 'POST',
      body: JSON.stringify(request),
    });
  }

  /**
   * Get git history for a prompt file.
   * Returns a list of versions with their content and commit info.
   *
   * @param request.prompt_path - Path to the prompt file
   * @param request.limit - Maximum number of versions to retrieve (default 10)
   */
  async getPromptHistory(request: PromptHistoryRequest): Promise<PromptHistoryResponse> {
    return this.request<PromptHistoryResponse>('/api/v1/prompts/git-history', {
      method: 'POST',
      body: JSON.stringify(request),
    });
  }

  /**
   * Compare two prompt versions with LLM-powered linguistic analysis.
   * Analyzes semantic differences and categorizes changes by type and impact.
   *
   * @param request.prompt_path - Path to the prompt file
   * @param request.version_a - First version: commit hash, 'HEAD', or 'working'
   * @param request.version_b - Second version: commit hash, 'HEAD', or 'working'
   * @param request.code_path - Optional code path for related code diff
   */
  async getPromptDiff(request: PromptDiffRequest): Promise<PromptDiffResponse> {
    return this.request<PromptDiffResponse>('/api/v1/prompts/prompt-diff', {
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
   * Save architecture.json to the project.
   * Writes the array of architecture modules as formatted JSON.
   */
  async saveArchitecture(modules: ArchitectureModule[]): Promise<{ success: boolean; path: string; error?: string }> {
    const content = JSON.stringify(modules, null, 2);
    return this.writeFile('architecture.json', content);
  }

  /**
   * Validate architecture for structural issues.
   * Returns validation result with errors and warnings.
   * Errors block saving, warnings are informational.
   */
  async validateArchitecture(modules: ArchitectureModule[]): Promise<ArchitectureValidationResult> {
    return this.request<ArchitectureValidationResult>('/api/v1/architecture/validate', {
      method: 'POST',
      body: JSON.stringify({ modules }),
    });
  }

  /**
   * Sync architecture.json from prompt file metadata tags.
   * Reads <pdd-reason>, <pdd-interface>, <pdd-dependency> tags from prompts
   * and updates the corresponding architecture.json entries.
   *
   * @param request - Sync request with optional filenames and dry_run flag
   * @returns Sync result with updated modules and validation status
   */
  async syncArchitectureFromPrompts(request: ArchitectureSyncRequest = {}): Promise<ArchitectureSyncResult> {
    return this.request<ArchitectureSyncResult>('/api/v1/architecture/sync-from-prompts', {
      method: 'POST',
      body: JSON.stringify(request),
    });
  }

  /**
   * Generate PDD metadata tags for a prompt from architecture.json.
   * This is the reverse direction: architecture.json -> prompt tags.
   *
   * @param promptFilename - The prompt filename (e.g., "llm_invoke_python.prompt")
   * @returns Generated tags and architecture entry info
   */
  async generateTagsForPrompt(promptFilename: string): Promise<GenerateTagsResult> {
    return this.request<GenerateTagsResult>('/api/v1/architecture/generate-tags-for-prompt', {
      method: 'POST',
      body: JSON.stringify({ prompt_filename: promptFilename }),
    });
  }

  /**
   * Re-arrange graph positions using the agentic swimlane layout algorithm.
   * The agent reads the specified architecture file and any PRD from the project root,
   * reasons about the architecture's logical structure, and writes updated positions in-place.
   *
   * @param architecturePath - Relative path to the architecture file (e.g. 'architecture.json')
   * Note: This call may take 30–120 seconds while the agent runs.
   */
  async rearrangeGraphLayout(
    architecturePath: string = 'architecture.json'
  ): Promise<{
    success: boolean;
    modules?: ArchitectureModule[];
    message?: string;
    error?: string;
  }> {
    return this.request<{
      success: boolean;
      modules?: ArchitectureModule[];
      message?: string;
      error?: string;
    }>('/api/v1/architecture/rearrange', {
      method: 'POST',
      body: JSON.stringify({ architecture_path: architecturePath }),
    });
  }

  /**
   * Generate architecture from a GitHub issue URL.
   * Spawns the agentic architecture workflow in a terminal.
   *
   * @param issueUrl - GitHub issue URL (e.g., https://github.com/owner/repo/issues/42)
   * @param options - Optional verbose/quiet flags
   * @returns Result with job_id for tracking the spawned process
   */
  async generateArchitectureFromIssue(
    issueUrl: string,
    options: { verbose?: boolean; quiet?: boolean } = {}
  ): Promise<{ success: boolean; message: string; job_id?: string }> {
    return this.request<{ success: boolean; message: string; job_id?: string }>(
      '/api/v1/architecture/generate-from-issue',
      {
        method: 'POST',
        body: JSON.stringify({
          issue_url: issueUrl,
          verbose: options.verbose ?? false,
          quiet: options.quiet ?? false,
        }),
      }
    );
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
   * Generate .pddrc configuration file from architecture.json using the generic/generate_pddrc template.
   * This should be called before generating prompts to ensure correct context detection.
   */
  async generatePddrcFromArchitecture(request: {
    architectureFile?: string;
    outputPath?: string;
    globalOptions?: GenerationGlobalOptions;
  }): Promise<RunResult> {
    const { architectureFile, outputPath, globalOptions } = request;

    const envArgs: string[] = [
      `ARCHITECTURE_FILE=${architectureFile || 'architecture.json'}`,
    ];

    const options: Record<string, any> = {
      template: 'generic/generate_pddrc',
      env: envArgs,
      output: outputPath || '.pddrc',
    };

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

  // Remote session operations

  /**
   * Get JWT token from local cache.
   * Returns null if not authenticated.
   */
  private async getJWTToken(): Promise<string | null> {
    try {
      // Call local server to get JWT token from cache
      const response = await this.request<{ jwt: string | null }>('/api/v1/auth/jwt-token');
      return response.jwt;
    } catch {
      return null;
    }
  }

  /**
   * Fetch cloud functions URL from server config.
   * This ensures frontend uses the same cloud URL as CLI.
   */
  private async fetchCloudUrl(): Promise<string> {
    try {
      const response = await this.request<{ cloud_url: string; environment: string }>('/api/v1/config/cloud-url');
      return response.cloud_url;
    } catch (error) {
      console.warn('Failed to fetch cloud URL from server, using default:', error);
      // Fallback to environment variable or staging default
      return import.meta.env.VITE_CLOUD_URL || 'https://us-central1-prompt-driven-development.cloudfunctions.net';
    }
  }

  /**
   * Get cloud functions URL (cached or fetch from server).
   */
  private async getCloudUrl(): Promise<string> {
    if (!this.cachedCloudUrl) {
      this.cachedCloudUrl = await this.fetchCloudUrl();
    }
    return this.cachedCloudUrl;
  }

  /**
   * List remote sessions for authenticated user.
   * Fetches from cloud, requires JWT token.
   */
  async listRemoteSessions(): Promise<RemoteSessionInfo[]> {
    const token = await this.getJWTToken();
    if (!token) {
      throw new Error('Not authenticated. Please run: pdd auth login');
    }

    const cloudUrl = await this.getCloudUrl();
    const response = await fetch(`${cloudUrl}/listSessions`, {
      method: 'GET',
      headers: {
        'Authorization': `Bearer ${token}`,
        'Content-Type': 'application/json',
      },
    });

    if (!response.ok) {
      const error = await response.json().catch(() => ({ error: response.statusText }));
      throw new Error(error.error || `Failed to list sessions: ${response.status}`);
    }

    const data = await response.json();
    return data.sessions || [];
  }

  /**
   * Submit command to remote session.
   * Returns command ID for polling status.
   */
  async submitRemoteCommand(request: RemoteCommandRequest): Promise<{ commandId: string; status: string }> {
    const token = await this.getJWTToken();
    if (!token) {
      throw new Error('Not authenticated. Please run: pdd auth login');
    }

    const cloudUrl = await this.getCloudUrl();
    const response = await fetch(`${cloudUrl}/submitCommand`, {
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${token}`,
        'Content-Type': 'application/json',
      },
      body: JSON.stringify(request),
    });

    if (!response.ok) {
      const error = await response.json().catch(() => ({ error: response.statusText }));
      throw new Error(error.error || `Failed to submit command: ${response.status}`);
    }

    return await response.json();
  }

  /**
   * Poll command status for remote session.
   * Fetches status of a single command by ID (any status, not just pending).
   */
  async getRemoteCommandStatus(
    sessionId: string,
    commandId: string
  ): Promise<RemoteCommandStatus | null> {
    const token = await this.getJWTToken();
    if (!token) {
      throw new Error('Not authenticated. Please run: pdd auth login');
    }

    const cloudUrl = await this.getCloudUrl();
    const response = await fetch(
      `${cloudUrl}/getCommandStatus?sessionId=${encodeURIComponent(sessionId)}&commandId=${encodeURIComponent(commandId)}`,
      {
        method: 'GET',
        headers: {
          'Authorization': `Bearer ${token}`,
          'Content-Type': 'application/json',
        },
      }
    );

    if (!response.ok) {
      if (response.status === 404) {
        return null; // Command not found
      }
      const error = await response.json().catch(() => ({ error: response.statusText }));
      throw new Error(error.error || `Failed to get command status: ${response.status}`);
    }

    const data = await response.json();
    const command = data.command;

    if (!command) {
      return null;
    }

    // Map cloud response to RemoteCommandStatus
    return {
      commandId: command.commandId,
      type: command.type,
      status: command.status,
      createdAt: command.createdAt,
      updatedAt: command.updatedAt,
      response: command.response,
    };
  }

  /**
   * Cancel a pending or processing remote command.
   *
   * @param sessionId - The remote session ID
   * @param commandId - The command ID to cancel
   * @returns Success response with cancellation confirmation
   */
  async cancelRemoteCommand(params: {
    sessionId: string;
    commandId: string;
  }): Promise<{ success: boolean; message: string }> {
    const token = await this.getJWTToken();
    if (!token) {
      throw new Error('Not authenticated. Please run: pdd auth login');
    }

    const cloudUrl = await this.getCloudUrl();
    const response = await fetch(`${cloudUrl}/cancelCommand`, {
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${token}`,
        'Content-Type': 'application/json',
      },
      body: JSON.stringify(params),
    });

    if (!response.ok) {
      const error = await response.json().catch(() => ({ error: response.statusText }));
      throw new Error(error.error || `Failed to cancel command: ${response.status}`);
    }

    return response.json();
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

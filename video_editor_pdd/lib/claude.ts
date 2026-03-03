// server-only check
try {
  require("server-only");
} catch (e) {
  // In development or test environments, server-only might not be available
  if (process.env.NODE_ENV === "production") {
    console.warn(
      "Warning: server-only module not found. Ensure this module is not bundled into client-side code."
    );
  }
}

import { spawn } from "child_process";

const TIMEOUT_MS = 300_000; // 5 minutes
const DEFAULT_MODEL = "claude-opus-4-6";

// ---------------------------------------------------------------------------
// JSON Fallback Parsing
// ---------------------------------------------------------------------------

/**
 * Attempts to parse JSON from CLI stdout using multiple strategies:
 * 1. Direct JSON.parse
 * 2. Extraction from Markdown code fences (```json ... ```)
 * 3. Manual brace matching (first `{` to last `}`)
 */
export function parseJsonWithFallback(stdout: string): unknown {
  const trimmed = stdout.trim();

  // Strategy 1: Direct parse
  try {
    return JSON.parse(trimmed);
  } catch {
    // fall through
  }

  // Strategy 2: Markdown code fence extraction
  const fenceRegex = /```(?:json)?\s*\n?([\s\S]*?)\n?\s*```/;
  const fenceMatch = trimmed.match(fenceRegex);
  if (fenceMatch && fenceMatch[1]) {
    console.warn(
      "parseJsonWithFallback: Direct parse failed. Attempting extraction from Markdown code fence."
    );
    try {
      return JSON.parse(fenceMatch[1].trim());
    } catch {
      // fall through
    }
  }

  // Strategy 3: Manual brace matching
  const firstBrace = trimmed.indexOf("{");
  const lastBrace = trimmed.lastIndexOf("}");
  if (firstBrace !== -1 && lastBrace !== -1 && lastBrace > firstBrace) {
    console.warn(
      "parseJsonWithFallback: Code fence extraction failed or not found. Attempting manual brace matching."
    );
    const candidate = trimmed.substring(firstBrace, lastBrace + 1);
    try {
      return JSON.parse(candidate);
    } catch {
      // fall through
    }
  }

  throw new Error(
    'Unable to parse JSON from Claude CLI output'
  );
}

// ---------------------------------------------------------------------------
// Core Execution Engine
// ---------------------------------------------------------------------------

interface RunClaudeOptions {
  args: string[];
  onLog?: (line: string) => void;
  cwd?: string;
}

function runClaude(options: RunClaudeOptions): Promise<unknown> {
  const { args, onLog, cwd } = options;

  return new Promise((resolve, reject) => {
    let stdoutBuffer = "";
    let stderrBuffer = "";
    let settled = false;
    let timeoutId: ReturnType<typeof setTimeout> | null = null;

    const child = spawn("claude", args, {
      stdio: ["ignore", "pipe", "pipe"],
      cwd: cwd || process.cwd(),
      env: {
        ...process.env,
      },
    });

    // Timeout management
    timeoutId = setTimeout(() => {
      if (!settled) {
        settled = true;
        child.kill("SIGTERM");
        reject(
          new Error(
            'Claude CLI timeout after 300s'
          )
        );
      }
    }, TIMEOUT_MS);

    // Accumulate stdout
    child.stdout.on("data", (chunk: Buffer) => {
      stdoutBuffer += chunk.toString("utf-8");
    });

    // Stream stderr line-by-line
    let stderrPartial = "";
    child.stderr.on("data", (chunk: Buffer) => {
      const text = chunk.toString("utf-8");
      stderrBuffer += text;

      if (onLog) {
        stderrPartial += text;
        const lines = stderrPartial.split("\n");
        // Keep the last partial line in the buffer
        stderrPartial = lines.pop() || "";
        for (const line of lines) {
          if (line.length > 0) {
            onLog(line);
          }
        }
      }
    });

    child.on("error", (err: Error) => {
      if (!settled) {
        settled = true;
        if (timeoutId) clearTimeout(timeoutId);
        reject(
          new Error(`Failed to spawn Claude CLI process: ${err.message}`)
        );
      }
    });

    child.on("close", (code: number | null, signal: string | null) => {
      if (settled) return;
      settled = true;
      if (timeoutId) clearTimeout(timeoutId);

      // Flush any remaining stderr partial line
      if (onLog && stderrPartial.length > 0) {
        onLog(stderrPartial);
        stderrPartial = "";
      }

      // Non-zero exit code → process execution error
      if (code !== null && code !== 0) {
        const errorMessage = stderrBuffer.trim() || `Process exited with code ${code}`;
        reject(
          new Error(
            `Claude CLI failed: ${errorMessage}`
          )
        );
        return;
      }

      if (signal) {
        reject(
          new Error(`Claude CLI was killed by signal: ${signal}`)
        );
        return;
      }

      // Parse the output
      try {
        const parsed = parseJsonWithFallback(stdoutBuffer);
        resolve(parsed);
      } catch (parseError: unknown) {
        const msg =
          parseError instanceof Error ? parseError.message : String(parseError);
        reject(
          new Error(
            `Claude CLI completed successfully but output parsing failed: ${msg}`
          )
        );
      }
    });
  });
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/**
 * Runs a read-only analysis using the Claude CLI.
 * Uses a restricted toolset (Read, Glob) to prevent any file modifications.
 */
export async function runClaudeAnalysis(
  prompt: string,
  onLog?: (line: string) => void
): Promise<unknown> {
  const args = [
    '-p',
    prompt,
    '--model',
    DEFAULT_MODEL,
    '--output-format',
    'json',
    '--no-session-persistence',
    '--allowedTools',
    'Read,Glob',
  ];

  return runClaude({ args, onLog });
}

/**
 * Runs a fix/edit operation using the Claude CLI.
 * Uses a broader toolset (Read, Write, Edit, Glob, Grep) and operates
 * within the specified working directory.
 */
export async function runClaudeFix(
  prompt: string,
  scopeDir: string,
  onLog?: (line: string) => void
): Promise<unknown> {
  const args = [
    '-p',
    prompt,
    '--model',
    DEFAULT_MODEL,
    '--output-format',
    'json',
    '--no-session-persistence',
    '--allowedTools',
    'Read,Write,Edit,Glob,Grep',
  ];

  return runClaude({ args, onLog, cwd: scopeDir });
}

/**
 * Runs a dry-run fix operation using the Claude CLI.
 * Injects instructions to prevent actual file modifications and instead
 * requests a structured JSON response with proposed changes.
 */
export async function runClaudeFixDryRun(
  prompt: string,
  scopeDir: string,
  onLog?: (line: string) => void
): Promise<unknown> {
  const dryRunPrompt = `IMPORTANT: This is a DRY RUN. Do NOT modify, write, or edit any files. Instead, analyze the requested changes and respond with a JSON object describing what changes WOULD be made.

Your response MUST be a valid JSON object with the following schema:
{
  "fixType": "string - the category/type of fix being proposed (e.g., 'bug-fix', 'refactor', 'style', 'performance', 'security')",
  "filesModified": ["string[] - list of file paths that would be modified"],
  "changeDescription": "string - a detailed human-readable description of all changes that would be made",
  "confidence": "number - a confidence score from 0.0 to 1.0 indicating how confident you are in the proposed fix",
  "proposedDiff": "string - a unified diff showing the exact changes that would be made"
}

Only use Read, Glob, and Grep tools to analyze the codebase. Do NOT use Write or Edit tools.

Original request:
${prompt}`;

  const args = [
    '-p',
    dryRunPrompt,
    '--model',
    DEFAULT_MODEL,
    '--output-format',
    'json',
    '--no-session-persistence',
    '--allowedTools',
    'Read,Glob,Grep',
  ];

  return runClaude({ args, onLog, cwd: scopeDir });
}
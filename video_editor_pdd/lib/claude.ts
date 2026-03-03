try { require('server-only'); } catch { /* running outside Next.js bundler */ }

import { spawn } from 'child_process';
import type { AnnotationAnalysis, ClaudeFixResult } from './types';

const TIMEOUT_MS = 600_000;

/**
 * Attempts to parse JSON from the Claude CLI output using multiple strategies.
 * Handles cases where the LLM might include conversational text or markdown fences.
 */
export function parseJsonWithFallback(stdout: string): any {
  // (a) direct parse
  try {
    return JSON.parse(stdout);
  } catch {}

  // (b) code fence ```json ... ```
  const fenceMatch = stdout.match(/```json\s*([\s\S]*?)```/);
  if (fenceMatch && fenceMatch[1]) {
    console.warn('Claude CLI output not pure JSON, using code-fence extraction fallback.');
    try {
      return JSON.parse(fenceMatch[1]);
    } catch {}
  }

  // (c) brace matching from first { to last }
  const end = stdout.lastIndexOf('}');
  if (end !== -1) {
    console.warn('Claude CLI output not pure JSON, using brace-matching fallback.');
    // Try each '{' position from right to left; first successful parse wins
    for (let i = end; i >= 0; i--) {
      if (stdout[i] === '{') {
        try {
          return JSON.parse(stdout.slice(i, end + 1));
        } catch {}
      }
    }
  }

  // (d) bracket matching from first [ to last ]
  const endBracket = stdout.lastIndexOf(']');
  if (endBracket !== -1) {
    console.warn('Claude CLI output not pure JSON, using bracket-matching fallback.');
    for (let i = endBracket; i >= 0; i--) {
      if (stdout[i] === '[') {
        try { return JSON.parse(stdout.slice(i, endBracket + 1)); } catch {}
      }
    }
  }

  throw new Error('Unable to parse JSON from Claude CLI output');
}

/**
 * Spawns the Claude CLI process and handles communication and timeouts.
 */
function runClaude(
  prompt: string,
  args: string[],
  options: { cwd?: string },
  onLog?: (line: string) => void
): Promise<any> {
  return new Promise((resolve, reject) => {
    const proc = spawn('claude', ['-p', prompt, ...args], {
      cwd: options.cwd,
      stdio: ['ignore', 'pipe', 'pipe'],
    });

    let stdout = '';
    let stderr = '';
    let stderrBuf = '';

    const timeout = setTimeout(() => {
      proc.kill('SIGTERM');
      reject(new Error('Claude CLI timeout after 600s'));
    }, TIMEOUT_MS);

    proc.stdout.on('data', (chunk) => {
      stdout += chunk.toString();
    });

    proc.stderr.on('data', (chunk) => {
      const text = chunk.toString();
      stderr += text;

      // Stream stderr lines to onLog in real time
      if (onLog) {
        stderrBuf += text;
        let idx: number;
        while ((idx = stderrBuf.indexOf('\n')) !== -1) {
          const line = stderrBuf.slice(0, idx).replace(/\r$/, '');
          stderrBuf = stderrBuf.slice(idx + 1);
          if (line.length > 0) onLog(line);
        }
      }
    });

    proc.on('close', (code) => {
      clearTimeout(timeout);

      // Flush any remaining stderr buffer
      if (onLog && stderrBuf.trim().length > 0) {
        onLog(stderrBuf.trim());
      }

      try {
        const outer = parseJsonWithFallback(stdout);

        // The Claude CLI's --output-format json wraps the response in an
        // envelope: { type: "result", result: "<claude text>", is_error: ... }
        // If we detect this envelope, extract and parse the inner payload.
        if (
          outer &&
          typeof outer === 'object' &&
          typeof outer.result === 'string' &&
          outer.result.trim().length > 0
        ) {
          if (outer.is_error) {
            reject(new Error(`Claude CLI returned error: ${outer.result}`));
            return;
          }
          try {
            const inner = parseJsonWithFallback(outer.result);
            resolve(inner);
            return;
          } catch {
            // Inner text is not JSON; fall through and return the envelope as-is
          }
        }

        resolve(outer);
      } catch (err) {
        if (code !== 0) {
          reject(new Error(`Claude CLI failed: ${stderr}`));
          return;
        }
        reject(err);
      }
    });

    proc.on('error', (err) => {
      clearTimeout(timeout);
      reject(err);
    });
  });
}

/**
 * Runs an analysis task using Claude.
 */
export async function runClaudeAnalysis(
  prompt: string,
  onLog?: (line: string) => void
): Promise<AnnotationAnalysis> {
  const args = [
    '--model',
    'claude-opus-4-6',
    '--output-format',
    'json',
    '--allowedTools',
    'Read,Glob',
    '--no-session-persistence',
  ];

  return runClaude(prompt, args, {}, onLog) as Promise<AnnotationAnalysis>;
}

/**
 * Runs a read-only extraction task using Claude with a generic return type.
 */
export async function runClaudeExtract<T>(
  prompt: string,
  onLog?: (line: string) => void
): Promise<T> {
  const args = [
    '--model',
    'claude-opus-4-6',
    '--output-format',
    'json',
    '--allowedTools',
    'Read,Glob',
    '--no-session-persistence',
  ];

  return runClaude(prompt, args, {}, onLog) as Promise<T>;
}

/**
 * Runs a fix/edit task using Claude with file system write permissions.
 */
export async function runClaudeFix(
  prompt: string,
  scopeDir: string,
  onLog?: (line: string) => void
): Promise<ClaudeFixResult> {
  const args = [
    '--model',
    'claude-opus-4-6',
    '--output-format',
    'json',
    '--allowedTools',
    'Read,Write,Edit,Glob,Grep',
    '--no-session-persistence',
  ];

  return runClaude(prompt, args, { cwd: scopeDir }, onLog) as Promise<ClaudeFixResult>;
}

/**
 * Runs Claude in read-only mode to preview what a fix would change,
 * without actually modifying files.
 */
export async function runClaudeFixDryRun(
  prompt: string,
  scopeDir: string,
  onLog?: (line: string) => void
): Promise<ClaudeFixResult & { proposedDiff: string }> {
  const dryRunPrompt = `${prompt}

IMPORTANT: This is a DRY RUN / PREVIEW. Do NOT modify any files.
Instead, describe what changes you would make. Return JSON:
{
  "fixType": "remotion",
  "filesModified": ["list of files you would modify"],
  "changeDescription": "detailed description of what you would change",
  "confidence": 0.0-1.0,
  "proposedDiff": "unified diff format showing the proposed changes"
}`;

  const args = [
    '--model',
    'claude-opus-4-6',
    '--output-format',
    'json',
    '--allowedTools',
    'Read,Glob,Grep',
    '--no-session-persistence',
  ];

  return runClaude(dryRunPrompt, args, { cwd: scopeDir }, onLog) as Promise<ClaudeFixResult & { proposedDiff: string }>;
}
/**
 * Tests for lib/claude.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/lib_claude_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. Export runClaudeAnalysis(prompt, onLog?) → Promise<AnnotationAnalysis>
 *   2. Export runClaudeFix(prompt, scopeDir, onLog?) → Promise<ClaudeFixResult>
 *   3. Both stream stderr lines to onLog callback in real time
 *   4. JSON parsing: (a) direct, (b) code fence, (c) brace-matching fallback
 *   5. Hard timeout: 600s → kill + reject
 *   6. Non-zero exit + no parseable JSON → reject with stderr
 *   7. server-only guard
 *   8. Uses child_process.spawn (not exec)
 *   9. Prompt passed as -p argument value
 *  10. console.warn on fallback parse strategies (b) and (c)
 */

import fs from "fs";
import path from "path";
import { EventEmitter } from "events";

import { parseJsonWithFallback } from "../lib/claude";

// ---------------------------------------------------------------------------
// Mock child_process.spawn
// ---------------------------------------------------------------------------

type MockProc = EventEmitter & {
  stdout: EventEmitter;
  stderr: EventEmitter;
  kill: jest.Mock;
};

function createMockProc(): MockProc {
  const proc = new EventEmitter() as MockProc;
  proc.stdout = new EventEmitter();
  proc.stderr = new EventEmitter();
  proc.kill = jest.fn();
  return proc;
}

let lastSpawnArgs: { command: string; args: string[]; options: any } | null =
  null;
let mockProc: MockProc;

jest.mock("child_process", () => ({
  spawn: (command: string, args: string[], options: any) => {
    lastSpawnArgs = { command, args, options };
    return mockProc;
  },
}));

// Must import after jest.mock
import { runClaudeAnalysis, runClaudeFix } from "../lib/claude";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Emit stdout data then close with given exit code. */
function emitAndClose(
  proc: MockProc,
  stdout: string,
  stderr: string,
  code: number
) {
  if (stdout) proc.stdout.emit("data", Buffer.from(stdout));
  if (stderr) proc.stderr.emit("data", Buffer.from(stderr));
  proc.emit("close", code);
}

const sampleAnalysis = {
  severity: "major" as const,
  fixType: "remotion" as const,
  technicalAssessment: "The composition has timing issues.",
  suggestedFixes: ["Adjust duration", "Re-render"],
  confidence: 0.85,
};

const sampleFixResult = {
  fixType: "veo" as const,
  filesModified: ["src/comp.tsx", "src/styles.ts"],
  changeDescription: "Updated timing parameters",
  confidence: 0.92,
};

// ---------------------------------------------------------------------------
// 1. parseJsonWithFallback — strategy (a): direct JSON.parse
// ---------------------------------------------------------------------------

describe("parseJsonWithFallback — direct parse", () => {
  it("parses valid JSON string directly", () => {
    const input = JSON.stringify(sampleAnalysis);
    const result = parseJsonWithFallback(input);
    expect(result).toEqual(sampleAnalysis);
  });

  it("parses simple object", () => {
    const result = parseJsonWithFallback('{"key":"value"}');
    expect(result).toEqual({ key: "value" });
  });

  it("parses JSON array", () => {
    const result = parseJsonWithFallback("[1,2,3]");
    expect(result).toEqual([1, 2, 3]);
  });

  it("parses JSON with whitespace", () => {
    const input = '  \n  {"a": 1}  \n  ';
    // Direct JSON.parse handles leading/trailing whitespace
    const result = parseJsonWithFallback(input);
    expect(result).toEqual({ a: 1 });
  });
});

// ---------------------------------------------------------------------------
// 2. parseJsonWithFallback — strategy (b): code fence extraction
// ---------------------------------------------------------------------------

describe("parseJsonWithFallback — code fence fallback", () => {
  it("extracts JSON from ```json ... ``` fence", () => {
    const warnSpy = jest.spyOn(console, "warn").mockImplementation();
    const input = 'Here is the result:\n```json\n{"severity":"minor"}\n```\n';
    const result = parseJsonWithFallback(input);
    expect(result).toEqual({ severity: "minor" });
    expect(warnSpy).toHaveBeenCalledWith(
      expect.stringContaining("code-fence extraction fallback")
    );
    warnSpy.mockRestore();
  });

  it("handles code fence with extra whitespace", () => {
    const warnSpy = jest.spyOn(console, "warn").mockImplementation();
    const input = '```json\n  {"key": "value"}  \n```';
    const result = parseJsonWithFallback(input);
    expect(result).toEqual({ key: "value" });
    warnSpy.mockRestore();
  });

  it("handles code fence with nested objects", () => {
    const warnSpy = jest.spyOn(console, "warn").mockImplementation();
    const nested = {
      severity: "critical",
      fixType: "tts",
      technicalAssessment: "Audio mismatch",
      suggestedFixes: ["Re-generate TTS"],
      confidence: 0.95,
    };
    const input = `Some preamble\n\`\`\`json\n${JSON.stringify(nested)}\n\`\`\`\nSome epilogue`;
    const result = parseJsonWithFallback(input);
    expect(result).toEqual(nested);
    warnSpy.mockRestore();
  });

  it("logs console.warn when using code fence fallback", () => {
    const warnSpy = jest.spyOn(console, "warn").mockImplementation();
    parseJsonWithFallback('text\n```json\n{"a":1}\n```');
    expect(warnSpy).toHaveBeenCalledTimes(1);
    warnSpy.mockRestore();
  });
});

// ---------------------------------------------------------------------------
// 3. parseJsonWithFallback — strategy (c): brace matching
// ---------------------------------------------------------------------------

describe("parseJsonWithFallback — brace matching fallback", () => {
  it("extracts JSON using first { and last }", () => {
    const warnSpy = jest.spyOn(console, "warn").mockImplementation();
    const input = 'Some text before {"result": true} some text after';
    const result = parseJsonWithFallback(input);
    expect(result).toEqual({ result: true });
    warnSpy.mockRestore();
  });

  it("handles text with nested braces", () => {
    const warnSpy = jest.spyOn(console, "warn").mockImplementation();
    const obj = { outer: { inner: "value" } };
    const input = `Here is the output: ${JSON.stringify(obj)} done`;
    const result = parseJsonWithFallback(input);
    expect(result).toEqual(obj);
    warnSpy.mockRestore();
  });

  it("logs console.warn when using brace-matching fallback", () => {
    const warnSpy = jest.spyOn(console, "warn").mockImplementation();
    // Input that fails direct parse and code-fence, but has braces
    parseJsonWithFallback('output: {"x": 1} end');
    expect(warnSpy).toHaveBeenCalledWith(
      expect.stringContaining("brace-matching fallback")
    );
    warnSpy.mockRestore();
  });

  it("handles brace-in-text before actual JSON", () => {
    const warnSpy = jest.spyOn(console, "warn").mockImplementation();
    const output = 'I\'ll use { braces } to explain:\n{"result": true}';
    expect(parseJsonWithFallback(output)).toEqual({ result: true });
    warnSpy.mockRestore();
  });
});

// ---------------------------------------------------------------------------
// 4. parseJsonWithFallback — error case
// ---------------------------------------------------------------------------

describe("parseJsonWithFallback — error", () => {
  it("throws when no JSON can be extracted", () => {
    expect(() => parseJsonWithFallback("no json here at all")).toThrow(
      "Unable to parse JSON from Claude CLI output"
    );
  });

  it("throws for empty string", () => {
    expect(() => parseJsonWithFallback("")).toThrow(
      "Unable to parse JSON from Claude CLI output"
    );
  });

  it("throws when braces contain invalid JSON", () => {
    expect(() =>
      parseJsonWithFallback("prefix {not: valid: json} suffix")
    ).toThrow();
  });

  it("throws when only opening brace exists", () => {
    expect(() => parseJsonWithFallback("text { no closing")).toThrow();
  });
});

// ---------------------------------------------------------------------------
// 5. runClaudeAnalysis — correct spawn arguments
// ---------------------------------------------------------------------------

describe("runClaudeAnalysis — spawn arguments", () => {
  beforeEach(() => {
    mockProc = createMockProc();
    lastSpawnArgs = null;
  });

  it("spawns 'claude' command with -p flag and prompt", () => {
    const prompt = "Analyze this annotation";
    const promise = runClaudeAnalysis(prompt);
    emitAndClose(mockProc, JSON.stringify(sampleAnalysis), "", 0);

    return promise.then(() => {
      expect(lastSpawnArgs!.command).toBe("claude");
      expect(lastSpawnArgs!.args[0]).toBe("-p");
      expect(lastSpawnArgs!.args[1]).toBe(prompt);
    });
  });

  it("includes --model claude-opus-4-6", () => {
    const promise = runClaudeAnalysis("test");
    emitAndClose(mockProc, JSON.stringify(sampleAnalysis), "", 0);

    return promise.then(() => {
      const args = lastSpawnArgs!.args;
      const modelIdx = args.indexOf("--model");
      expect(modelIdx).toBeGreaterThan(-1);
      expect(args[modelIdx + 1]).toBe("claude-opus-4-6");
    });
  });

  it("includes --output-format json", () => {
    const promise = runClaudeAnalysis("test");
    emitAndClose(mockProc, JSON.stringify(sampleAnalysis), "", 0);

    return promise.then(() => {
      const args = lastSpawnArgs!.args;
      const idx = args.indexOf("--output-format");
      expect(idx).toBeGreaterThan(-1);
      expect(args[idx + 1]).toBe("json");
    });
  });

  it("includes --allowedTools Read,Glob for analysis", () => {
    const promise = runClaudeAnalysis("test");
    emitAndClose(mockProc, JSON.stringify(sampleAnalysis), "", 0);

    return promise.then(() => {
      const args = lastSpawnArgs!.args;
      const idx = args.indexOf("--allowedTools");
      expect(idx).toBeGreaterThan(-1);
      expect(args[idx + 1]).toBe("Read,Glob");
    });
  });

  it("includes --no-session-persistence", () => {
    const promise = runClaudeAnalysis("test");
    emitAndClose(mockProc, JSON.stringify(sampleAnalysis), "", 0);

    return promise.then(() => {
      expect(lastSpawnArgs!.args).toContain("--no-session-persistence");
    });
  });

  it("sets stdio to ['ignore', 'pipe', 'pipe']", () => {
    const promise = runClaudeAnalysis("test");
    emitAndClose(mockProc, JSON.stringify(sampleAnalysis), "", 0);

    return promise.then(() => {
      expect(lastSpawnArgs!.options.stdio).toEqual(["ignore", "pipe", "pipe"]);
    });
  });

  it("does not set cwd for analysis", () => {
    const promise = runClaudeAnalysis("test");
    emitAndClose(mockProc, JSON.stringify(sampleAnalysis), "", 0);

    return promise.then(() => {
      expect(lastSpawnArgs!.options.cwd).toBeUndefined();
    });
  });
});

// ---------------------------------------------------------------------------
// 6. runClaudeAnalysis — returns parsed AnnotationAnalysis
// ---------------------------------------------------------------------------

describe("runClaudeAnalysis — returns parsed result", () => {
  beforeEach(() => {
    mockProc = createMockProc();
  });

  it("resolves with parsed AnnotationAnalysis JSON", async () => {
    const promise = runClaudeAnalysis("test");
    emitAndClose(mockProc, JSON.stringify(sampleAnalysis), "", 0);

    const result = await promise;
    expect(result).toEqual(sampleAnalysis);
    expect(result.severity).toBe("major");
    expect(result.fixType).toBe("remotion");
    expect(result.technicalAssessment).toBe(
      "The composition has timing issues."
    );
    expect(result.suggestedFixes).toEqual(["Adjust duration", "Re-render"]);
    expect(result.confidence).toBe(0.85);
  });

  it("handles code-fence wrapped response", async () => {
    const warnSpy = jest.spyOn(console, "warn").mockImplementation();
    const promise = runClaudeAnalysis("test");
    const fenced = `Here is my analysis:\n\`\`\`json\n${JSON.stringify(sampleAnalysis)}\n\`\`\``;
    emitAndClose(mockProc, fenced, "", 0);

    const result = await promise;
    expect(result).toEqual(sampleAnalysis);
    warnSpy.mockRestore();
  });
});

// ---------------------------------------------------------------------------
// 7. runClaudeFix — correct spawn arguments
// ---------------------------------------------------------------------------

describe("runClaudeFix — spawn arguments", () => {
  beforeEach(() => {
    mockProc = createMockProc();
    lastSpawnArgs = null;
  });

  it("spawns with -p flag and prompt", () => {
    const promise = runClaudeFix("fix this", "/project/dir");
    emitAndClose(mockProc, JSON.stringify(sampleFixResult), "", 0);

    return promise.then(() => {
      expect(lastSpawnArgs!.args[0]).toBe("-p");
      expect(lastSpawnArgs!.args[1]).toBe("fix this");
    });
  });

  it("includes --allowedTools Read,Write,Edit,Glob,Grep for fix", () => {
    const promise = runClaudeFix("fix", "/dir");
    emitAndClose(mockProc, JSON.stringify(sampleFixResult), "", 0);

    return promise.then(() => {
      const args = lastSpawnArgs!.args;
      const idx = args.indexOf("--allowedTools");
      expect(idx).toBeGreaterThan(-1);
      expect(args[idx + 1]).toBe("Read,Write,Edit,Glob,Grep");
    });
  });

  it("sets cwd to scopeDir", () => {
    const promise = runClaudeFix("fix", "/my/project");
    emitAndClose(mockProc, JSON.stringify(sampleFixResult), "", 0);

    return promise.then(() => {
      expect(lastSpawnArgs!.options.cwd).toBe("/my/project");
    });
  });

  it("includes --model and --output-format flags", () => {
    const promise = runClaudeFix("fix", "/dir");
    emitAndClose(mockProc, JSON.stringify(sampleFixResult), "", 0);

    return promise.then(() => {
      const args = lastSpawnArgs!.args;
      expect(args).toContain("--model");
      expect(args).toContain("claude-opus-4-6");
      expect(args).toContain("--output-format");
      expect(args).toContain("json");
    });
  });

  it("includes --no-session-persistence", () => {
    const promise = runClaudeFix("fix", "/dir");
    emitAndClose(mockProc, JSON.stringify(sampleFixResult), "", 0);

    return promise.then(() => {
      expect(lastSpawnArgs!.args).toContain("--no-session-persistence");
    });
  });
});

// ---------------------------------------------------------------------------
// 8. runClaudeFix — returns parsed ClaudeFixResult
// ---------------------------------------------------------------------------

describe("runClaudeFix — returns parsed result", () => {
  beforeEach(() => {
    mockProc = createMockProc();
  });

  it("resolves with parsed ClaudeFixResult JSON", async () => {
    const promise = runClaudeFix("fix", "/dir");
    emitAndClose(mockProc, JSON.stringify(sampleFixResult), "", 0);

    const result = await promise;
    expect(result).toEqual(sampleFixResult);
    expect(result.fixType).toBe("veo");
    expect(result.filesModified).toEqual(["src/comp.tsx", "src/styles.ts"]);
    expect(result.changeDescription).toBe("Updated timing parameters");
    expect(result.confidence).toBe(0.92);
  });
});

// ---------------------------------------------------------------------------
// 9. stderr streaming — onLog callback
// ---------------------------------------------------------------------------

describe("stderr streaming via onLog", () => {
  beforeEach(() => {
    mockProc = createMockProc();
  });

  it("streams stderr lines to onLog in real time", async () => {
    const logs: string[] = [];
    const promise = runClaudeAnalysis("test", (line) => logs.push(line));

    mockProc.stderr.emit("data", Buffer.from("Processing step 1\n"));
    mockProc.stderr.emit("data", Buffer.from("Processing step 2\n"));
    mockProc.stdout.emit("data", Buffer.from(JSON.stringify(sampleAnalysis)));
    mockProc.emit("close", 0);

    await promise;
    expect(logs).toContain("Processing step 1");
    expect(logs).toContain("Processing step 2");
  });

  it("handles multi-line stderr chunks", async () => {
    const logs: string[] = [];
    const promise = runClaudeAnalysis("test", (line) => logs.push(line));

    mockProc.stderr.emit(
      "data",
      Buffer.from("Line A\nLine B\nLine C\n")
    );
    mockProc.stdout.emit("data", Buffer.from(JSON.stringify(sampleAnalysis)));
    mockProc.emit("close", 0);

    await promise;
    expect(logs).toEqual(["Line A", "Line B", "Line C"]);
  });

  it("handles partial line buffering", async () => {
    const logs: string[] = [];
    const promise = runClaudeAnalysis("test", (line) => logs.push(line));

    // Send partial line, then rest
    mockProc.stderr.emit("data", Buffer.from("Hel"));
    mockProc.stderr.emit("data", Buffer.from("lo World\n"));
    mockProc.stdout.emit("data", Buffer.from(JSON.stringify(sampleAnalysis)));
    mockProc.emit("close", 0);

    await promise;
    expect(logs).toContain("Hello World");
  });

  it("flushes remaining stderr buffer on close", async () => {
    const logs: string[] = [];
    const promise = runClaudeAnalysis("test", (line) => logs.push(line));

    // Partial line without trailing newline
    mockProc.stderr.emit("data", Buffer.from("Final partial"));
    mockProc.stdout.emit("data", Buffer.from(JSON.stringify(sampleAnalysis)));
    mockProc.emit("close", 0);

    await promise;
    expect(logs).toContain("Final partial");
  });

  it("strips \\r from stderr lines", async () => {
    const logs: string[] = [];
    const promise = runClaudeAnalysis("test", (line) => logs.push(line));

    mockProc.stderr.emit("data", Buffer.from("Windows line\r\n"));
    mockProc.stdout.emit("data", Buffer.from(JSON.stringify(sampleAnalysis)));
    mockProc.emit("close", 0);

    await promise;
    expect(logs).toContain("Windows line");
    expect(logs).not.toContain("Windows line\r");
  });

  it("skips empty stderr lines", async () => {
    const logs: string[] = [];
    const promise = runClaudeAnalysis("test", (line) => logs.push(line));

    mockProc.stderr.emit("data", Buffer.from("Line 1\n\n\nLine 2\n"));
    mockProc.stdout.emit("data", Buffer.from(JSON.stringify(sampleAnalysis)));
    mockProc.emit("close", 0);

    await promise;
    expect(logs).toEqual(["Line 1", "Line 2"]);
  });

  it("does not crash when onLog is not provided", async () => {
    const promise = runClaudeAnalysis("test");

    mockProc.stderr.emit("data", Buffer.from("Some log\n"));
    mockProc.stdout.emit("data", Buffer.from(JSON.stringify(sampleAnalysis)));
    mockProc.emit("close", 0);

    const result = await promise;
    expect(result).toEqual(sampleAnalysis);
  });
});

// ---------------------------------------------------------------------------
// 10. Timeout behavior
// ---------------------------------------------------------------------------

describe("timeout behavior", () => {
  beforeEach(() => {
    jest.useFakeTimers();
    mockProc = createMockProc();
  });

  afterEach(() => {
    jest.useRealTimers();
  });

  it("rejects with timeout error after 600s", async () => {
    const promise = runClaudeAnalysis("test");

    jest.advanceTimersByTime(600_000);

    await expect(promise).rejects.toThrow("Claude CLI timeout after 600s");
  });

  it("kills the process with SIGTERM on timeout", async () => {
    const promise = runClaudeAnalysis("test");

    jest.advanceTimersByTime(600_000);

    try {
      await promise;
    } catch {
      // expected
    }
    expect(mockProc.kill).toHaveBeenCalledWith("SIGTERM");
  });

  it("does not timeout before 600s", async () => {
    const promise = runClaudeAnalysis("test");

    jest.advanceTimersByTime(599_999);

    // Process completes just in time
    mockProc.stdout.emit("data", Buffer.from(JSON.stringify(sampleAnalysis)));
    mockProc.emit("close", 0);

    const result = await promise;
    expect(result).toEqual(sampleAnalysis);
  });

  it("clears timeout on normal close", async () => {
    const clearSpy = jest.spyOn(global, "clearTimeout");
    const promise = runClaudeAnalysis("test");

    mockProc.stdout.emit("data", Buffer.from(JSON.stringify(sampleAnalysis)));
    mockProc.emit("close", 0);

    await promise;
    expect(clearSpy).toHaveBeenCalled();
    clearSpy.mockRestore();
  });
});

// ---------------------------------------------------------------------------
// 11. Error handling — non-zero exit code
// ---------------------------------------------------------------------------

describe("error handling", () => {
  beforeEach(() => {
    mockProc = createMockProc();
  });

  it("rejects with stderr when exit code is non-zero and no parseable JSON", async () => {
    const promise = runClaudeAnalysis("test");

    mockProc.stderr.emit("data", Buffer.from("Error: CLI crashed"));
    mockProc.emit("close", 1);

    await expect(promise).rejects.toThrow("Claude CLI failed: Error: CLI crashed");
  });

  it("resolves with JSON even if exit code is non-zero but stdout has valid JSON", async () => {
    const promise = runClaudeAnalysis("test");

    mockProc.stdout.emit("data", Buffer.from(JSON.stringify(sampleAnalysis)));
    mockProc.stderr.emit("data", Buffer.from("Some warning"));
    mockProc.emit("close", 1);

    const result = await promise;
    expect(result).toEqual(sampleAnalysis);
  });

  it("rejects with spawn error", async () => {
    const promise = runClaudeAnalysis("test");

    mockProc.emit("error", new Error("spawn ENOENT"));

    await expect(promise).rejects.toThrow("spawn ENOENT");
  });

  it("clears timeout on spawn error", async () => {
    const clearSpy = jest.spyOn(global, "clearTimeout");
    const promise = runClaudeAnalysis("test");

    mockProc.emit("error", new Error("spawn ENOENT"));

    try {
      await promise;
    } catch {
      // expected
    }
    expect(clearSpy).toHaveBeenCalled();
    clearSpy.mockRestore();
  });

  it("rejects with parse error when exit code 0 but stdout is unparseable", async () => {
    const promise = runClaudeAnalysis("test");

    mockProc.stdout.emit("data", Buffer.from("not json at all"));
    mockProc.emit("close", 0);

    await expect(promise).rejects.toThrow(
      "Unable to parse JSON from Claude CLI output"
    );
  });
});

// ---------------------------------------------------------------------------
// 12. stdout collection — multiple chunks
// ---------------------------------------------------------------------------

describe("stdout collection", () => {
  beforeEach(() => {
    mockProc = createMockProc();
  });

  it("concatenates multiple stdout chunks before parsing", async () => {
    const promise = runClaudeAnalysis("test");
    const fullJson = JSON.stringify(sampleAnalysis);
    const mid = Math.floor(fullJson.length / 2);

    mockProc.stdout.emit("data", Buffer.from(fullJson.slice(0, mid)));
    mockProc.stdout.emit("data", Buffer.from(fullJson.slice(mid)));
    mockProc.emit("close", 0);

    const result = await promise;
    expect(result).toEqual(sampleAnalysis);
  });
});

// ---------------------------------------------------------------------------
// 13. Source file structure checks
// ---------------------------------------------------------------------------

describe("lib/claude.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    sourceCode = fs.readFileSync(
      path.join(__dirname, "..", "lib", "claude.ts"),
      "utf-8"
    );
  });

  it("has server-only guard", () => {
    expect(sourceCode).toMatch(/server-only/);
  });

  it("uses child_process.spawn (not exec)", () => {
    expect(sourceCode).toMatch(/spawn/);
    expect(sourceCode).not.toMatch(/\bexec\b/);
  });

  it("exports runClaudeAnalysis function", () => {
    expect(sourceCode).toMatch(/export\s+(async\s+)?function\s+runClaudeAnalysis/);
  });

  it("exports runClaudeFix function", () => {
    expect(sourceCode).toMatch(/export\s+(async\s+)?function\s+runClaudeFix/);
  });

  it("exports parseJsonWithFallback function", () => {
    expect(sourceCode).toMatch(/export\s+function\s+parseJsonWithFallback/);
  });

  it("uses SIGTERM for killing the process", () => {
    expect(sourceCode).toMatch(/SIGTERM/);
  });

  it("has 600-second timeout constant", () => {
    expect(sourceCode).toMatch(/600[_,]?000/);
  });

  it("uses code fence regex for fallback extraction", () => {
    expect(sourceCode).toMatch(/```json/);
  });

  it("uses brace matching for final fallback", () => {
    expect(sourceCode).toMatch(/lastIndexOf\s*\(\s*['"]?\}/);
    // Scans '{' positions right-to-left for robust extraction
    expect(sourceCode).toMatch(/stdout\[i\]\s*===\s*['"]?\{/);
  });

  it("calls console.warn for fallback strategies", () => {
    expect(sourceCode).toMatch(/console\.warn/);
  });

  it("uses setTimeout and clearTimeout for timeout management", () => {
    expect(sourceCode).toMatch(/setTimeout/);
    expect(sourceCode).toMatch(/clearTimeout/);
  });

  it("sets stdio to ignore stdin and pipe stdout/stderr", () => {
    expect(sourceCode).toMatch(/stdio.*ignore.*pipe.*pipe/);
  });
});

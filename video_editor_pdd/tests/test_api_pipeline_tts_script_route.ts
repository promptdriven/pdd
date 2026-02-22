/**
 * Tests for app/api/pipeline/tts-script/run/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_pipeline_tts_script_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. POST /api/pipeline/tts-script/run — creates job via runPipelineStage('tts-script', {}, send)
 *   2. Returns Response with status 202 immediately (non-blocking SSE stream)
 *   3. Uses SSE streaming: ReadableStream with correct headers
 *   4. Sends { type: 'started', jobId } and { type: 'complete', jobId } events on success
 *   5. On error: calls error(message) on the SSE stream
 *   6. registerExecutor('tts-script', ...) called at module load time
 *   7. Executor calls runClaudeFix with TTS_SCRIPT_PROMPT scoped to narrative/
 *   8. TTS_SCRIPT_PROMPT includes [TONE:], [PACE:], [PAUSE:], [EMOTION:] annotation markers
 *   9. TTS_SCRIPT_PROMPT references main_script.md and tts_script.md
 *  10. export const dynamic = 'force-dynamic'
 *  11. No authentication required
 */

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockSend = jest.fn();
const mockDone = jest.fn();
const mockError = jest.fn();

jest.mock("@/lib/sse", () => ({
  createSseStream: () => ({
    stream: new ReadableStream(),
    send: mockSend,
    done: mockDone,
    error: mockError,
  }),
}));

const mockRegisterExecutor = jest.fn();
const mockRunPipelineStage = jest.fn();

jest.mock("@/lib/jobs", () => ({
  registerExecutor: (...args: unknown[]) => mockRegisterExecutor(...args),
  runPipelineStage: (...args: unknown[]) => mockRunPipelineStage(...args),
}));

const mockRunClaudeFix = jest.fn();

jest.mock("@/lib/claude", () => ({
  runClaudeFix: (...args: unknown[]) => mockRunClaudeFix(...args),
}));

// Import after mocking
import { POST, dynamic } from "../app/api/pipeline/tts-script/run/route";

// Capture executor factory registered at module load (before beforeEach clears call history)
const registerCallArgs = {
  stage: mockRegisterExecutor.mock.calls[0]?.[0] as string,
  factory: mockRegisterExecutor.mock.calls[0]?.[1] as (
    params: Record<string, unknown>,
    send: Function
  ) => (onLog: (msg: string) => void) => Promise<void>,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function makeRequest(): Request {
  return new Request("http://localhost/api/pipeline/tts-script/run", {
    method: "POST",
  });
}

/** Flush microtask queue so fire-and-forget IIFE completes. */
function flushPromises(): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, 0));
}

// ---------------------------------------------------------------------------
// Setup
// ---------------------------------------------------------------------------

beforeEach(() => {
  mockSend.mockClear();
  mockDone.mockClear();
  mockError.mockClear();
  mockRunPipelineStage.mockReset();
  mockRunClaudeFix.mockReset();
  mockRunPipelineStage.mockResolvedValue("test-job-id");
});

// ---------------------------------------------------------------------------
// 1. dynamic export
// ---------------------------------------------------------------------------

describe("dynamic export", () => {
  it("exports dynamic = 'force-dynamic' to prevent static optimization", () => {
    expect(dynamic).toBe("force-dynamic");
  });
});

// ---------------------------------------------------------------------------
// 2. registerExecutor — module load side effect
// ---------------------------------------------------------------------------

describe("registerExecutor at module load", () => {
  it("registers executor for 'tts-script' stage", () => {
    expect(registerCallArgs.stage).toBe("tts-script");
  });

  it("passes an executor factory function", () => {
    expect(typeof registerCallArgs.factory).toBe("function");
  });
});

// ---------------------------------------------------------------------------
// 3. Executor factory — calls runClaudeFix
// ---------------------------------------------------------------------------

describe("tts-script executor", () => {
  it("returns an async function when called with params and send", () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    expect(typeof executor).toBe("function");
  });

  it("calls runClaudeFix with the prompt and narrative/ scope directory", async () => {
    const onLog = jest.fn();
    const executor = registerCallArgs.factory({}, jest.fn());
    mockRunClaudeFix.mockResolvedValue(undefined);
    await executor(onLog);

    expect(mockRunClaudeFix).toHaveBeenCalledTimes(1);
    const [prompt, scopeDir, logFn] = mockRunClaudeFix.mock.calls[0];
    expect(typeof prompt).toBe("string");
    expect(scopeDir).toBe(require("path").join(process.cwd(), "narrative"));
    expect(logFn).toBe(onLog);
  });

  it("passes prompt that references main_script.md", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    mockRunClaudeFix.mockResolvedValue(undefined);
    await executor(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0];
    expect(prompt).toContain("main_script.md");
  });

  it("passes prompt that references tts_script.md", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    mockRunClaudeFix.mockResolvedValue(undefined);
    await executor(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0];
    expect(prompt).toContain("tts_script.md");
  });

  it("passes prompt with [TONE:] annotation marker", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    mockRunClaudeFix.mockResolvedValue(undefined);
    await executor(jest.fn());

    expect(mockRunClaudeFix.mock.calls[0][0]).toContain("[TONE:");
  });

  it("passes prompt with [PACE:] annotation marker", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    mockRunClaudeFix.mockResolvedValue(undefined);
    await executor(jest.fn());

    expect(mockRunClaudeFix.mock.calls[0][0]).toContain("[PACE:");
  });

  it("passes prompt with [PAUSE:] annotation marker", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    mockRunClaudeFix.mockResolvedValue(undefined);
    await executor(jest.fn());

    expect(mockRunClaudeFix.mock.calls[0][0]).toContain("[PAUSE:");
  });

  it("passes prompt with [EMOTION:] annotation marker", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    mockRunClaudeFix.mockResolvedValue(undefined);
    await executor(jest.fn());

    expect(mockRunClaudeFix.mock.calls[0][0]).toContain("[EMOTION:");
  });

  it("passes prompt mentioning NARRATOR blocks", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    mockRunClaudeFix.mockResolvedValue(undefined);
    await executor(jest.fn());

    expect(mockRunClaudeFix.mock.calls[0][0]).toContain("NARRATOR");
  });

  it("scopes runClaudeFix to process.cwd()/narrative", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    mockRunClaudeFix.mockResolvedValue(undefined);
    await executor(jest.fn());

    const path = require("path");
    expect(mockRunClaudeFix.mock.calls[0][1]).toBe(
      path.join(process.cwd(), "narrative")
    );
  });

  it("propagates runClaudeFix errors", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    mockRunClaudeFix.mockRejectedValue(new Error("Claude failed"));

    await expect(executor(jest.fn())).rejects.toThrow("Claude failed");
  });
});

// ---------------------------------------------------------------------------
// 4. POST — response shape
// ---------------------------------------------------------------------------

describe("POST response shape", () => {
  it("returns a Response object", async () => {
    const response = await POST(makeRequest());
    expect(response).toBeInstanceOf(Response);
  });

  it("returns status 202", async () => {
    const response = await POST(makeRequest());
    expect(response.status).toBe(202);
  });

  it("sets Content-Type to text/event-stream", async () => {
    const response = await POST(makeRequest());
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("sets Cache-Control to no-cache", async () => {
    const response = await POST(makeRequest());
    expect(response.headers.get("Cache-Control")).toBe("no-cache");
  });

  it("sets Connection to keep-alive", async () => {
    const response = await POST(makeRequest());
    expect(response.headers.get("Connection")).toBe("keep-alive");
  });

  it("returns a ReadableStream body", async () => {
    const response = await POST(makeRequest());
    expect(response.body).toBeInstanceOf(ReadableStream);
  });
});

// ---------------------------------------------------------------------------
// 5. POST — success flow
// ---------------------------------------------------------------------------

describe("POST — success flow", () => {
  beforeEach(() => {
    mockRunPipelineStage.mockResolvedValue("test-job-42");
  });

  it("calls runPipelineStage with 'tts-script', empty params, and send", async () => {
    await POST(makeRequest());
    await flushPromises();

    expect(mockRunPipelineStage).toHaveBeenCalledWith(
      "tts-script",
      {},
      mockSend
    );
  });

  it("sends started event with jobId", async () => {
    await POST(makeRequest());
    await flushPromises();

    expect(mockSend).toHaveBeenCalledWith({
      type: "started",
      jobId: "test-job-42",
    });
  });

  it("sends complete event with jobId", async () => {
    await POST(makeRequest());
    await flushPromises();

    expect(mockSend).toHaveBeenCalledWith({
      type: "complete",
      jobId: "test-job-42",
    });
  });

  it("sends started before complete", async () => {
    await POST(makeRequest());
    await flushPromises();

    const sendCalls = mockSend.mock.calls.map((c: any[]) => c[0]);
    const startedIdx = sendCalls.findIndex((c: any) => c.type === "started");
    const completeIdx = sendCalls.findIndex((c: any) => c.type === "complete");
    expect(startedIdx).toBeGreaterThanOrEqual(0);
    expect(completeIdx).toBeGreaterThan(startedIdx);
  });

  it("calls done() to close the stream", async () => {
    await POST(makeRequest());
    await flushPromises();

    expect(mockDone).toHaveBeenCalledTimes(1);
  });

  it("does not call error() on success", async () => {
    await POST(makeRequest());
    await flushPromises();

    expect(mockError).not.toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 6. POST — error flow
// ---------------------------------------------------------------------------

describe("POST — error flow", () => {
  it("calls error() with message when runPipelineStage rejects with Error", async () => {
    mockRunPipelineStage.mockRejectedValue(new Error("Pipeline failed"));

    await POST(makeRequest());
    await flushPromises();

    expect(mockError).toHaveBeenCalledWith("Pipeline failed");
  });

  it("calls error() with generic message for non-Error throws", async () => {
    mockRunPipelineStage.mockRejectedValue("string error");

    await POST(makeRequest());
    await flushPromises();

    expect(mockError).toHaveBeenCalledWith(
      "Unknown error running tts-script"
    );
  });

  it("does not call done() on error", async () => {
    mockRunPipelineStage.mockRejectedValue(new Error("fail"));

    await POST(makeRequest());
    await flushPromises();

    expect(mockDone).not.toHaveBeenCalled();
  });

  it("does not send started or complete events on error", async () => {
    mockRunPipelineStage.mockRejectedValue(new Error("fail"));

    await POST(makeRequest());
    await flushPromises();

    const sendCalls = mockSend.mock.calls.map((c: any[]) => c[0]);
    expect(sendCalls.find((c: any) => c.type === "started")).toBeUndefined();
    expect(sendCalls.find((c: any) => c.type === "complete")).toBeUndefined();
  });

  it("still returns 202 even when pipeline will error asynchronously", async () => {
    mockRunPipelineStage.mockRejectedValue(new Error("will fail"));

    const response = await POST(makeRequest());
    // Response returned before async IIFE rejects
    expect(response.status).toBe(202);
  });
});

// ---------------------------------------------------------------------------
// 7. POST — no authentication
// ---------------------------------------------------------------------------

describe("POST — no authentication required", () => {
  it("does not require authorization headers", async () => {
    const request = new Request("http://localhost/api/pipeline/tts-script/run", {
      method: "POST",
      headers: { Authorization: "Bearer fake-token" },
    });

    const response = await POST(request);
    expect(response.status).toBe(202);
  });

  it("works with minimal request (no body, no auth)", async () => {
    const response = await POST(makeRequest());
    expect(response.status).toBe(202);
  });
});

// ---------------------------------------------------------------------------
// 8. Source file structure checks
// ---------------------------------------------------------------------------

describe("source file structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    const fs = require("fs");
    const path = require("path");
    sourceCode = fs.readFileSync(
      path.join(
        __dirname,
        "..",
        "app",
        "api",
        "pipeline",
        "tts-script",
        "run",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async function POST", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+POST/);
  });

  it("exports dynamic = 'force-dynamic'", () => {
    expect(sourceCode).toMatch(
      /export\s+const\s+dynamic\s*=\s*["']force-dynamic["']/
    );
  });

  it("imports createSseStream from @/lib/sse", () => {
    expect(sourceCode).toMatch(/@\/lib\/sse/);
    expect(sourceCode).toMatch(/createSseStream/);
  });

  it("imports registerExecutor and runPipelineStage from @/lib/jobs", () => {
    expect(sourceCode).toMatch(/@\/lib\/jobs/);
    expect(sourceCode).toMatch(/registerExecutor/);
    expect(sourceCode).toMatch(/runPipelineStage/);
  });

  it("imports runClaudeFix from @/lib/claude", () => {
    expect(sourceCode).toMatch(/@\/lib\/claude/);
    expect(sourceCode).toMatch(/runClaudeFix/);
  });

  it("imports path from 'path'", () => {
    expect(sourceCode).toMatch(/import\s+path\s+from\s+["']path["']/);
  });

  it("defines TTS_SCRIPT_PROMPT as a module-level constant", () => {
    expect(sourceCode).toMatch(/const\s+TTS_SCRIPT_PROMPT\s*=/);
  });

  it("calls registerExecutor('tts-script', ...)", () => {
    expect(sourceCode).toMatch(
      /registerExecutor\s*\(\s*["']tts-script["']/
    );
  });

  it("calls runPipelineStage('tts-script', ...)", () => {
    expect(sourceCode).toMatch(/runPipelineStage\s*\(\s*["']tts-script["']/);
  });

  it("uses new Response(stream, ...) for SSE streaming", () => {
    expect(sourceCode).toMatch(/new\s+Response\s*\(\s*stream/);
  });

  it("sets Content-Type to text/event-stream in response headers", () => {
    expect(sourceCode).toMatch(/text\/event-stream/);
  });

  it("references NARRATOR blocks in the prompt", () => {
    expect(sourceCode).toMatch(/NARRATOR/);
  });

  it("scopes runClaudeFix to narrative/ directory via path.join", () => {
    expect(sourceCode).toMatch(
      /path\.join\s*\(\s*process\.cwd\(\)\s*,\s*["']narrative["']\s*\)/
    );
  });
});

/**
 * Tests for app/api/pipeline/audio-sync/run/route.ts
 * and app/api/pipeline/audio-sync/timestamps/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_pipeline_audio_sync_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. POST /api/pipeline/audio-sync/run — triggers sync_audio_pipeline.py subprocess, returns SSE stream with { jobId }
 *   2. Reads sectionGroups from project.json via loadProject()
 *   3. Streams per-section progress events: { type: 'section', sectionId, status: 'done' | 'error' }
 *   4. GET /api/pipeline/audio-sync/timestamps?section=X — returns word timestamps JSON, 404 if missing
 *   5. No authentication required
 *   6. registerExecutor('audio-sync', ...) called at module load time
 *   7. Spawns python3 sync_audio_pipeline.py with cwd: process.cwd()
 *   8. Passes SECTION_GROUPS as env var to spawned process
 *   9. SSE headers: Content-Type text/event-stream, Cache-Control no-cache, Connection keep-alive
 *  10. Word timestamp format: { words: [{ word, start, end, segmentId }], validation?: { ... } }
 */

import path from "path";

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockRegisterExecutor = jest.fn();
const mockRunPipelineStage = jest.fn();
const mockRunPipelineStageDirect = jest.fn();

jest.mock("@/lib/jobs", () => ({
  registerExecutor: (...args: unknown[]) => mockRegisterExecutor(...args),
  runPipelineStage: (...args: unknown[]) => mockRunPipelineStage(...args),
  runPipelineStageDirect: (...args: unknown[]) => mockRunPipelineStageDirect(...args),
}));

// Mock child_process.spawn
const mockOn = jest.fn();
const mockStdoutOn = jest.fn();
const mockStderrOn = jest.fn();
const mockSpawn = jest.fn(() => ({
  stdout: { on: mockStdoutOn },
  stderr: { on: mockStderrOn },
  on: mockOn,
}));

jest.mock("child_process", () => ({
  spawn: (...args: unknown[]) => mockSpawn(...args),
}));

// Mock loadProject
const mockLoadProject = jest.fn();

jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
}));

const mockResolvePythonRunSpec = jest.fn(() => ({
  command: "python3",
  argsPrefix: [] as string[],
  env: { ...process.env },
}));

jest.mock("@/app/api/pipeline/_lib/python-runtime", () => ({
  resolvePythonRunSpec: (...args: unknown[]) => mockResolvePythonRunSpec(...args),
}));

jest.mock("@/lib/projects", () => ({
  getProjectDir: () => process.cwd(),
  getAppScriptsDir: () => path.join(process.cwd(), "scripts"),
  getAppRemotionPublicDir: () => path.join(process.cwd(), "remotion", "public"),
}));

// Mock fs/promises for timestamps route
const mockReadFile = jest.fn();
const mockReaddir = jest.fn();
const mockStat = jest.fn();

jest.mock("fs/promises", () => ({
  __esModule: true,
  default: {
    readFile: (...args: unknown[]) => mockReadFile(...args),
    readdir: (...args: unknown[]) => mockReaddir(...args),
    stat: (...args: unknown[]) => mockStat(...args),
  },
  readFile: (...args: unknown[]) => mockReadFile(...args),
  readdir: (...args: unknown[]) => mockReaddir(...args),
  stat: (...args: unknown[]) => mockStat(...args),
}));

// Import after mocking
import { POST } from "../app/api/pipeline/audio-sync/run/route";
import { GET } from "../app/api/pipeline/audio-sync/timestamps/route";

// Capture executor factory registered at module load
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

function makePostRequest(body?: Record<string, unknown>): Request {
  return new Request("http://localhost/api/pipeline/audio-sync/run", {
    method: "POST",
    headers: body ? { "Content-Type": "application/json" } : undefined,
    body: body ? JSON.stringify(body) : undefined,
  });
}

function makeGetRequest(section?: string): Request {
  const url = section
    ? `http://localhost/api/pipeline/audio-sync/timestamps?section=${section}`
    : "http://localhost/api/pipeline/audio-sync/timestamps";
  return new Request(url, { method: "GET" });
}

/** Flush microtask queue so fire-and-forget IIFE completes. */
function flushPromises(): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, 50));
}

/** Parse SSE events from a ReadableStream. */
async function readSseEvents(stream: ReadableStream<Uint8Array>): Promise<object[]> {
  const reader = stream.getReader();
  const decoder = new TextDecoder();
  let buffer = "";
  const events: object[] = [];

  try {
    while (true) {
      const { done, value } = await reader.read();
      if (done) break;
      buffer += decoder.decode(value, { stream: true });
      const parts = buffer.split("\n\n");
      buffer = parts.pop() ?? "";
      for (const part of parts) {
        const dataLine = part.replace(/^data:\s*/, "");
        if (dataLine) {
          try {
            events.push(JSON.parse(dataLine));
          } catch {
            // skip non-JSON
          }
        }
      }
    }
  } catch {
    // stream closed
  }

  return events;
}

// ---------------------------------------------------------------------------
// Setup
// ---------------------------------------------------------------------------

beforeEach(() => {
  mockSpawn.mockClear();
  mockOn.mockReset();
  mockStdoutOn.mockReset();
  mockStderrOn.mockReset();
  mockRunPipelineStage.mockReset();
  mockRunPipelineStageDirect.mockReset();
  mockLoadProject.mockReset();
  mockReadFile.mockReset();
  mockReaddir.mockReset();
  mockStat.mockReset();
  mockResolvePythonRunSpec.mockClear();
  mockResolvePythonRunSpec.mockReturnValue({
    command: "python3",
    argsPrefix: [],
    env: { ...process.env },
  });

  // Default: loadProject returns config with sectionGroups
  mockLoadProject.mockReturnValue({
    audioSync: {
      sectionGroups: {
        narration: ["intro", "main"],
      },
    },
  });

  // Default: runPipelineStage resolves with a job ID
  mockRunPipelineStage.mockResolvedValue("test-job-id-1234");
  mockRunPipelineStageDirect.mockResolvedValue("test-job-id-1234");
  mockReaddir.mockResolvedValue([]);
  mockStat.mockResolvedValue({ mtimeMs: 1000 });

  // Default: spawn completes successfully
  mockSpawn.mockImplementation(() => {
    const proc = {
      stdout: { on: mockStdoutOn },
      stderr: { on: mockStderrOn },
      on: mockOn,
    };
    // Auto-resolve close with code 0 on next tick
    setTimeout(() => {
      const closeHandler = mockOn.mock.calls.find(
        (c: any[]) => c[0] === "close"
      )?.[1];
      if (closeHandler) closeHandler(0);
    }, 5);
    return proc;
  });
});

// ---------------------------------------------------------------------------
// 1. registerExecutor — module load side effect
// ---------------------------------------------------------------------------

describe("registerExecutor at module load", () => {
  it("registers executor for 'audio-sync' stage", () => {
    expect(registerCallArgs.stage).toBe("audio-sync");
  });

  it("passes an executor factory function", () => {
    expect(typeof registerCallArgs.factory).toBe("function");
  });
});

// ---------------------------------------------------------------------------
// 2. POST — response shape and SSE headers
// ---------------------------------------------------------------------------

describe("POST response shape", () => {
  it("returns a Response object", async () => {
    const response = await POST(makePostRequest() as any);
    expect(response).toBeInstanceOf(Response);
  });

  it("sets Content-Type to text/event-stream", async () => {
    const response = await POST(makePostRequest() as any);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("sets Cache-Control to no-cache", async () => {
    const response = await POST(makePostRequest() as any);
    expect(response.headers.get("Cache-Control")).toBe("no-cache");
  });

  it("sets Connection to keep-alive", async () => {
    const response = await POST(makePostRequest() as any);
    expect(response.headers.get("Connection")).toBe("keep-alive");
  });

  it("returns a ReadableStream body", async () => {
    const response = await POST(makePostRequest() as any);
    expect(response.body).toBeInstanceOf(ReadableStream);
  });
});

// ---------------------------------------------------------------------------
// 3. POST — SSE events include jobId
// ---------------------------------------------------------------------------

describe("POST — SSE events", () => {
  it("emits a job event containing jobId", async () => {
    const response = await POST(makePostRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const jobEvent = events.find((e: any) => e.type === "job");
    expect(jobEvent).toBeDefined();
    expect((jobEvent as any).jobId).toBe("test-job-id-1234");
  });

  it("emits a complete event with jobId on success", async () => {
    const response = await POST(makePostRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const completeEvent = events.find((e: any) => e.type === "complete");
    expect(completeEvent).toBeDefined();
    expect((completeEvent as any).jobId).toBe("test-job-id-1234");
  });

  it("calls runPipelineStage with 'audio-sync' stage", async () => {
    await POST(makePostRequest() as any);
    await flushPromises();

    expect(mockRunPipelineStage).toHaveBeenCalledWith(
      "audio-sync",
      {},
      expect.any(Function)
    );
  });

  it("passes requested sections into runPipelineStage params", async () => {
    await POST(makePostRequest({ sections: ["intro"] }) as any);
    await flushPromises();

    expect(mockRunPipelineStageDirect).toHaveBeenCalledWith(
      "audio-sync",
      { sections: ["intro"] },
      expect.any(Function)
    );
  });

  it("runs isolated audio-sync jobs when validation-tolerant retry mode is enabled", async () => {
    await POST(
      makePostRequest({
        sections: ["part4_precision_tradeoff"],
        allowValidationFailures: true,
        skipDependencies: true,
      }) as any
    );
    await flushPromises();

    expect(mockRunPipelineStageDirect).toHaveBeenCalledWith(
      "audio-sync",
      {
        sections: ["part4_precision_tradeoff"],
        allowValidationFailures: true,
      },
      expect.any(Function)
    );
  });
});

// ---------------------------------------------------------------------------
// 4. POST — error handling
// ---------------------------------------------------------------------------

describe("POST — error handling", () => {
  it("emits error event when runPipelineStage rejects with Error", async () => {
    mockRunPipelineStage.mockRejectedValue(new Error("Pipeline failed"));

    const response = await POST(makePostRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const errorEvent = events.find((e: any) => e.type === "error");
    expect(errorEvent).toBeDefined();
    expect((errorEvent as any).error).toBe("Pipeline failed");
  });

  it("emits 'Unknown error' when runPipelineStage rejects with non-Error", async () => {
    mockRunPipelineStage.mockRejectedValue("string error");

    const response = await POST(makePostRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const errorEvent = events.find((e: any) => e.type === "error");
    expect(errorEvent).toBeDefined();
    expect((errorEvent as any).error).toBe("Unknown error");
  });

  it("still returns SSE response even when pipeline will fail", async () => {
    mockRunPipelineStage.mockRejectedValue(new Error("fail"));

    const response = await POST(makePostRequest() as any);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });
});

// ---------------------------------------------------------------------------
// 5. POST — no authentication required
// ---------------------------------------------------------------------------

describe("POST — no authentication required", () => {
  it("does not require authorization headers", async () => {
    const request = new Request("http://localhost/api/pipeline/audio-sync/run", {
      method: "POST",
      headers: { Authorization: "Bearer fake-token" },
    });

    const response = await POST(request as any);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("works with minimal request (no body, no auth)", async () => {
    const response = await POST(makePostRequest() as any);
    expect(response).toBeInstanceOf(Response);
  });
});

// ---------------------------------------------------------------------------
// 6. POST — SSE event format
// ---------------------------------------------------------------------------

describe("POST — SSE event format", () => {
  it("formats events as 'data: <JSON>\\n\\n'", async () => {
    const response = await POST(makePostRequest() as any);
    await flushPromises();

    const reader = response.body!.getReader();
    const decoder = new TextDecoder();
    let raw = "";
    try {
      while (true) {
        const { done, value } = await reader.read();
        if (done) break;
        raw += decoder.decode(value, { stream: true });
      }
    } catch {
      // stream closed
    }

    // Each event should start with "data: " and end with "\n\n"
    const eventBlocks = raw.split("\n\n").filter((b) => b.trim().length > 0);
    for (const block of eventBlocks) {
      expect(block).toMatch(/^data:\s*\{/);
    }
  });
});

// ---------------------------------------------------------------------------
// 7. Executor factory — loads project and spawns sync_audio_pipeline.py
// ---------------------------------------------------------------------------

describe("audio-sync executor factory", () => {
  it("returns an async function when called with params and send", () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    expect(typeof executor).toBe("function");
  });

  it("calls loadProject() to read sectionGroups", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());
    await flushPromises();

    expect(mockLoadProject).toHaveBeenCalled();
  });

  it("spawns the resolved python command with sync_audio_pipeline.py", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());
    await flushPromises();

    expect(mockSpawn).toHaveBeenCalled();
    const [cmd, args] = mockSpawn.mock.calls[0];
    expect(cmd).toBe("python3");
    expect(args).toEqual([
      path.join(process.cwd(), "scripts", "sync_audio_pipeline.py"),
      "--project-dir",
      process.cwd(),
      "--remotion-public",
      path.join(process.cwd(), "remotion", "public"),
    ]);
  });

  it("resolves the Stage 5 python runtime from the preferred conda env", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());
    await flushPromises();

    expect(mockResolvePythonRunSpec).toHaveBeenCalledWith({
      preferredCondaEnv: "video_editor",
    });
  });

  it("spawns with cwd set to the active project directory", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());
    await flushPromises();

    const [, , options] = mockSpawn.mock.calls[0];
    expect(options).toHaveProperty("cwd", process.cwd());
  });

  it("passes SECTION_GROUPS as env var", async () => {
    mockLoadProject.mockReturnValue({
      audioSync: {
        sectionGroups: { narration: ["intro", "main"] },
      },
    });

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());
    await flushPromises();

    const [, , options] = mockSpawn.mock.calls[0];
    expect(options.env.SECTION_GROUPS).toBe(
      JSON.stringify({ narration: ["intro", "main"] })
    );
  });

  it("filters SECTION_GROUPS when params.sections is provided", async () => {
    mockLoadProject.mockReturnValue({
      audioSync: {
        sectionGroups: { intro: ["intro_001"], outro: ["outro_001"] },
      },
    });

    const executor = registerCallArgs.factory({ sections: ["outro"] }, jest.fn());
    await executor(jest.fn());
    await flushPromises();

    const [, , options] = mockSpawn.mock.calls[0];
    expect(options.env.SECTION_GROUPS).toBe(
      JSON.stringify({ outro: ["outro_001"] })
    );
  });

  it("prunes obsolete sectionGroups that no longer exist in project.sections", async () => {
    mockLoadProject.mockReturnValue({
      sections: [{ id: "cold_open" }, { id: "part3_mold_parts" }],
      audioSync: {
        sectionGroups: {
          cold_open: ["cold_open_001"],
          part3_mold_has_three_parts: ["part3_mold_has_three_parts_001"],
          part3_mold_parts: ["part3_mold_parts_001"],
        },
      },
    });

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());
    await flushPromises();

    const [, , options] = mockSpawn.mock.calls[0];
    expect(options.env.SECTION_GROUPS).toBe(
      JSON.stringify({
        cold_open: ["cold_open_001"],
        part3_mold_parts: ["part3_mold_parts_001"],
      })
    );
  });

  it("defaults to empty object when audioSync.sectionGroups is missing", async () => {
    mockLoadProject.mockReturnValue({});

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());
    await flushPromises();

    const [, , options] = mockSpawn.mock.calls[0];
    expect(options.env.SECTION_GROUPS).toBe("{}");
  });

  it("sends section events from stdout JSON lines via send()", async () => {
    const mockSend = jest.fn();

    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const dataHandler = mockStdoutOn.mock.calls.find(
          (c: any[]) => c[0] === "data"
        )?.[1];
        if (dataHandler) {
          dataHandler(
            Buffer.from(
              '{"type":"section","sectionId":"intro","status":"done"}\n'
            )
          );
        }

        const closeHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "close"
        )?.[1];
        if (closeHandler) closeHandler(0);
      }, 5);
      return proc;
    });

    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());
    await flushPromises();

    const sectionCalls = mockSend.mock.calls.filter(
      (c: any[]) => c[0]?.type === "section"
    );
    expect(sectionCalls.length).toBeGreaterThanOrEqual(1);
    expect(sectionCalls[0][0]).toEqual({
      type: "section",
      sectionId: "intro",
      status: "done",
    });
  });

  it("sends section error events via send()", async () => {
    const mockSend = jest.fn();

    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const dataHandler = mockStdoutOn.mock.calls.find(
          (c: any[]) => c[0] === "data"
        )?.[1];
        if (dataHandler) {
          dataHandler(
            Buffer.from(
              '{"type":"section","sectionId":"main","status":"error"}\n'
            )
          );
        }

        const closeHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "close"
        )?.[1];
        if (closeHandler) closeHandler(0);
      }, 5);
      return proc;
    });

    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());
    await flushPromises();

    const sectionCalls = mockSend.mock.calls.filter(
      (c: any[]) => c[0]?.type === "section"
    );
    expect(sectionCalls[0][0]).toEqual({
      type: "section",
      sectionId: "main",
      status: "error",
    });
  });

  it("logs non-section JSON lines via onLog", async () => {
    const mockSend = jest.fn();
    const mockOnLog = jest.fn();

    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const dataHandler = mockStdoutOn.mock.calls.find(
          (c: any[]) => c[0] === "data"
        )?.[1];
        if (dataHandler) {
          dataHandler(
            Buffer.from('{"type":"progress","percent":50}\n')
          );
        }

        const closeHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "close"
        )?.[1];
        if (closeHandler) closeHandler(0);
      }, 5);
      return proc;
    });

    const executor = registerCallArgs.factory({}, mockSend);
    await executor(mockOnLog);
    await flushPromises();

    // Non-section JSON should be passed to onLog, not send
    expect(mockSend).not.toHaveBeenCalledWith(
      expect.objectContaining({ type: "progress" })
    );
    expect(mockOnLog).toHaveBeenCalledWith('{"type":"progress","percent":50}');
  });

  it("logs non-JSON stdout lines via onLog", async () => {
    const mockSend = jest.fn();
    const mockOnLog = jest.fn();

    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const dataHandler = mockStdoutOn.mock.calls.find(
          (c: any[]) => c[0] === "data"
        )?.[1];
        if (dataHandler) {
          dataHandler(Buffer.from("Processing section intro...\n"));
        }

        const closeHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "close"
        )?.[1];
        if (closeHandler) closeHandler(0);
      }, 5);
      return proc;
    });

    const executor = registerCallArgs.factory({}, mockSend);
    await executor(mockOnLog);
    await flushPromises();

    expect(mockOnLog).toHaveBeenCalledWith("Processing section intro...");
  });

  it("logs stderr lines via onLog with [stderr] prefix", async () => {
    const mockSend = jest.fn();
    const mockOnLog = jest.fn();

    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const stderrHandler = mockStderrOn.mock.calls.find(
          (c: any[]) => c[0] === "data"
        )?.[1];
        if (stderrHandler) {
          stderrHandler(Buffer.from("WARNING: low quality"));
        }

        const closeHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "close"
        )?.[1];
        if (closeHandler) closeHandler(0);
      }, 5);
      return proc;
    });

    const executor = registerCallArgs.factory({}, mockSend);
    await executor(mockOnLog);
    await flushPromises();

    expect(mockOnLog).toHaveBeenCalledWith("[stderr] WARNING: low quality");
  });

  it("rejects when sync_audio_pipeline.py exits with non-zero code", async () => {
    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const closeHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "close"
        )?.[1];
        if (closeHandler) closeHandler(1);
      }, 5);
      return proc;
    });

    const executor = registerCallArgs.factory({}, jest.fn());
    await expect(executor(jest.fn())).rejects.toThrow(
      "sync_audio_pipeline.py exited with code 1"
    );
  });

  it("passes retry-mode validation tolerance through the subprocess env", async () => {
    const executor = registerCallArgs.factory(
      { sections: ["part4_precision_tradeoff"], allowValidationFailures: true },
      jest.fn()
    );

    await executor(jest.fn());

    expect(mockSpawn).toHaveBeenCalledWith(
      "python3",
      expect.any(Array),
      expect.objectContaining({
        env: expect.objectContaining({
          SYNC_AUDIO_ALLOW_VALIDATION_FAILURES: "1",
        }),
      })
    );
  });

  it("rejects when spawn emits error event", async () => {
    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const errorHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "error"
        )?.[1];
        if (errorHandler) errorHandler(new Error("ENOENT: python3 not found"));
      }, 5);
      return proc;
    });

    const executor = registerCallArgs.factory({}, jest.fn());
    await expect(executor(jest.fn())).rejects.toThrow(
      "ENOENT: python3 not found"
    );
  });

  it("handles multiple stdout lines in a single data chunk", async () => {
    const mockSend = jest.fn();

    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const dataHandler = mockStdoutOn.mock.calls.find(
          (c: any[]) => c[0] === "data"
        )?.[1];
        if (dataHandler) {
          dataHandler(
            Buffer.from(
              '{"type":"section","sectionId":"intro","status":"done"}\n{"type":"section","sectionId":"main","status":"done"}\n'
            )
          );
        }

        const closeHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "close"
        )?.[1];
        if (closeHandler) closeHandler(0);
      }, 5);
      return proc;
    });

    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());
    await flushPromises();

    const sectionCalls = mockSend.mock.calls.filter(
      (c: any[]) => c[0]?.type === "section"
    );
    expect(sectionCalls).toHaveLength(2);
    expect(sectionCalls[0][0].sectionId).toBe("intro");
    expect(sectionCalls[1][0].sectionId).toBe("main");
  });

  it("handles split data chunks (buffering partial lines)", async () => {
    const mockSend = jest.fn();

    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const dataHandler = mockStdoutOn.mock.calls.find(
          (c: any[]) => c[0] === "data"
        )?.[1];
        if (dataHandler) {
          // Send partial line first
          dataHandler(Buffer.from('{"type":"section","sectionI'));
          // Then complete it
          dataHandler(Buffer.from('d":"intro","status":"done"}\n'));
        }

        const closeHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "close"
        )?.[1];
        if (closeHandler) closeHandler(0);
      }, 5);
      return proc;
    });

    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());
    await flushPromises();

    const sectionCalls = mockSend.mock.calls.filter(
      (c: any[]) => c[0]?.type === "section"
    );
    expect(sectionCalls).toHaveLength(1);
    expect(sectionCalls[0][0].sectionId).toBe("intro");
  });

  it("skips empty lines in stdout", async () => {
    const mockSend = jest.fn();
    const mockOnLog = jest.fn();

    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const dataHandler = mockStdoutOn.mock.calls.find(
          (c: any[]) => c[0] === "data"
        )?.[1];
        if (dataHandler) {
          dataHandler(Buffer.from("\n\n\n"));
        }

        const closeHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "close"
        )?.[1];
        if (closeHandler) closeHandler(0);
      }, 5);
      return proc;
    });

    const executor = registerCallArgs.factory({}, mockSend);
    await executor(mockOnLog);
    await flushPromises();

    // Empty lines should be skipped, not logged
    expect(mockOnLog).not.toHaveBeenCalledWith("");
    expect(mockSend).not.toHaveBeenCalled();
  });

  it("logs initial sectionGroups message via onLog", async () => {
    const mockOnLog = jest.fn();
    mockLoadProject.mockReturnValue({
      audioSync: {
        sectionGroups: { narration: ["intro"] },
      },
    });

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(mockOnLog);
    await flushPromises();

    expect(mockOnLog).toHaveBeenCalledWith(
      expect.stringContaining("[audio-sync] Loaded sectionGroups:")
    );
  });
});

// ---------------------------------------------------------------------------
// 8. GET /api/pipeline/audio-sync/timestamps — word timestamps
// ---------------------------------------------------------------------------

describe("GET /api/pipeline/audio-sync/timestamps", () => {
  it("returns 400 when section param is missing", async () => {
    const response = await GET(makeGetRequest() as any);
    expect(response.status).toBe(400);

    const body = await response.json();
    expect(body).toHaveProperty("error");
  });

  it("returns word timestamps for a valid section", async () => {
    const timestamps = {
      words: [
        { word: "hello", start: 0.0, end: 0.5, segmentId: "seg1" },
        { word: "world", start: 0.6, end: 1.0, segmentId: "seg1" },
      ],
    };
    mockReadFile.mockImplementation(async (filePath: string) => {
      if (filePath.includes("word_timestamps.json")) {
        return JSON.stringify(timestamps);
      }

      return JSON.stringify({
        segments: [],
        summary: { passCount: 0, warnCount: 0, failCount: 0, skipCount: 0 },
      });
    });

    const response = await GET(makeGetRequest("intro") as any);
    expect(response.status).toBe(200);

    const body = await response.json();
    expect(body).toHaveProperty("words");
    expect(body.words).toHaveLength(2);
    expect(body.words[0]).toEqual({
      word: "hello",
      start: 0.0,
      end: 0.5,
      segmentId: "seg1",
    });
    expect(body.validation.summary.failCount).toBe(0);
  });

  it("reads from correct path: outputs/tts/{sectionId}/word_timestamps.json", async () => {
    mockReadFile.mockResolvedValue('{"words":[]}');

    await GET(makeGetRequest("intro") as any);

    const path = require("path");
    expect(mockReadFile).toHaveBeenCalledWith(
      path.join(process.cwd(), "outputs", "tts", "intro", "word_timestamps.json"),
      "utf-8"
    );
  });

  it("returns 404 when timestamps file does not exist", async () => {
    const enoentError = new Error("ENOENT") as NodeJS.ErrnoException;
    enoentError.code = "ENOENT";
    mockReadFile.mockRejectedValue(enoentError);

    const response = await GET(makeGetRequest("nonexistent") as any);
    expect(response.status).toBe(404);

    const body = await response.json();
    expect(body).toHaveProperty("error");
  });

  it("returns 500 on unexpected read errors", async () => {
    mockReadFile.mockRejectedValue(new Error("EACCES: permission denied"));

    const response = await GET(makeGetRequest("intro") as any);
    expect(response.status).toBe(500);

    const body = await response.json();
    expect(body.error).toBe("Internal Server Error");
  });

  it("returns WordTimestamp format: { word, start, end, segmentId }", async () => {
    const timestamps = {
      words: [
        { word: "test", start: 1.0, end: 1.5, segmentId: "seg2" },
      ],
    };
    mockReadFile.mockResolvedValue(JSON.stringify(timestamps));

    const response = await GET(makeGetRequest("section1") as any);
    const body = await response.json();

    expect(body.words[0]).toHaveProperty("word");
    expect(body.words[0]).toHaveProperty("start");
    expect(body.words[0]).toHaveProperty("end");
    expect(body.words[0]).toHaveProperty("segmentId");
    expect(typeof body.words[0].word).toBe("string");
    expect(typeof body.words[0].start).toBe("number");
    expect(typeof body.words[0].end).toBe("number");
    expect(typeof body.words[0].segmentId).toBe("string");
  });

  it("returns empty words array when file has no words", async () => {
    mockReadFile.mockImplementation(async (filePath: string) => {
      if (filePath.includes("word_timestamps.json")) {
        return '{"words":[]}';
      }

      return JSON.stringify({
        segments: [],
        summary: { passCount: 0, warnCount: 0, failCount: 0, skipCount: 0 },
      });
    });

    const response = await GET(makeGetRequest("empty_section") as any);
    expect(response.status).toBe(200);

    const body = await response.json();
    expect(body.words).toEqual([]);
  });

  it("no authentication required for GET", async () => {
    mockReadFile.mockImplementation(async (filePath: string) => {
      if (filePath.includes("word_timestamps.json")) {
        return '{"words":[]}';
      }

      return JSON.stringify({
        segments: [],
        summary: { passCount: 0, warnCount: 0, failCount: 0, skipCount: 0 },
      });
    });

    const request = new Request(
      "http://localhost/api/pipeline/audio-sync/timestamps?section=intro",
      {
        method: "GET",
        headers: { Authorization: "Bearer fake-token" },
      }
    );

    const response = await GET(request as any);
    expect(response.status).toBe(200);
  });

  it("returns validation details when segment_validation.json exists", async () => {
    mockReadFile.mockImplementation(async (filePath: string) => {
      if (filePath.includes("word_timestamps.json")) {
        return '{"words":[{"word":"hello","start":0,"end":0.5,"segmentId":"seg1"}]}';
      }

      return JSON.stringify({
        segments: [
          {
            segmentId: "seg1",
            expectedText: "hello world",
            actualText: "hello there",
            status: "warn",
            matchRatio: 0.82,
          },
        ],
        summary: { passCount: 0, warnCount: 1, failCount: 0, skipCount: 0 },
      });
    });

    const response = await GET(makeGetRequest("intro") as any);
    expect(response.status).toBe(200);

    const body = await response.json();
    expect(body.validation.segments[0]).toMatchObject({
      segmentId: "seg1",
      status: "warn",
      matchRatio: 0.82,
    });
    expect(body.validation.summary.warnCount).toBe(1);
  });

  it("returns stale artifact metadata when section audio is newer than sync outputs", async () => {
    mockReadFile.mockImplementation(async (filePath: string) => {
      if (filePath.includes("word_timestamps.json")) {
        return '{"words":[{"word":"hello","start":0,"end":0.5,"segmentId":"intro_001"}]}';
      }

      return JSON.stringify({
        segments: [],
        summary: { passCount: 0, warnCount: 0, failCount: 0, skipCount: 0 },
      });
    });
    mockReaddir.mockResolvedValue(["intro_001.wav", "ignore.txt"]);
    mockStat.mockImplementation(async (filePath: string) => {
      if (String(filePath).endsWith("intro_001.wav")) {
        return { mtimeMs: 5000 };
      }
      return { mtimeMs: 1000 };
    });

    const response = await GET(makeGetRequest("intro") as any);
    expect(response.status).toBe(200);

    const body = await response.json();
    expect(body.artifactState).toMatchObject({
      stale: true,
      latestAudioUpdatedAtMs: 5000,
      syncUpdatedAtMs: 1000,
    });
    expect(body.artifactState.message).toMatch(/stale relative to the current TTS audio/i);
  });

  it("prefers newer failed audio-sync artifacts over stale accepted ones", async () => {
    mockReadFile.mockImplementation(async (filePath: string) => {
      if (filePath.includes("word_timestamps.failed.json")) {
        return '{"words":[{"word":"fresh","start":0,"end":0.5,"segmentId":"intro_001"}]}';
      }
      if (filePath.includes("word_timestamps.json")) {
        return '{"words":[{"word":"stale","start":0,"end":0.5,"segmentId":"intro_001"}]}';
      }
      if (filePath.includes("segment_validation.failed.json")) {
        return JSON.stringify({
          segments: [{ segmentId: "intro_001", expectedText: "fresh", actualText: "fresh", status: "pass" }],
          summary: { passCount: 1, warnCount: 0, failCount: 0, skipCount: 0 },
        });
      }
      return JSON.stringify({
        segments: [{ segmentId: "intro_001", expectedText: "stale", actualText: "stale", status: "warn" }],
        summary: { passCount: 0, warnCount: 1, failCount: 0, skipCount: 0 },
      });
    });
    mockReaddir.mockResolvedValue(["intro_001.wav"]);
    mockStat.mockImplementation(async (filePath: string) => {
      const normalized = String(filePath);
      if (normalized.endsWith("word_timestamps.failed.json") || normalized.endsWith("segment_validation.failed.json")) {
        return { mtimeMs: 5000 };
      }
      if (normalized.endsWith("word_timestamps.json") || normalized.endsWith("segment_validation.json")) {
        return { mtimeMs: 1000 };
      }
      if (normalized.endsWith("intro_001.wav")) {
        return { mtimeMs: 4000 };
      }
      return { mtimeMs: 1000 };
    });

    const response = await GET(makeGetRequest("intro") as any);
    expect(response.status).toBe(200);

    const body = await response.json();
    expect(body.words[0].word).toBe("fresh");
    expect(body.validation.summary.passCount).toBe(1);
    expect(body.artifactState.source).toBe("failed");
    expect(body.artifactState.stale).toBe(false);
  });

  it("returns empty validation when segment_validation.json is missing", async () => {
    mockReadFile.mockImplementation(async (filePath: string) => {
      if (filePath.includes("word_timestamps.json")) {
        return '{"words":[]}';
      }

      const enoentError = new Error("ENOENT") as NodeJS.ErrnoException;
      enoentError.code = "ENOENT";
      throw enoentError;
    });

    const response = await GET(makeGetRequest("intro") as any);
    expect(response.status).toBe(200);

    const body = await response.json();
    expect(body.validation).toEqual({
      segments: [],
      summary: { passCount: 0, warnCount: 0, failCount: 0, skipCount: 0 },
    });
  });
});

// ---------------------------------------------------------------------------
// 9. Source file structure checks — run route
// ---------------------------------------------------------------------------

describe("app/api/pipeline/audio-sync/run/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    const realFs = jest.requireActual("fs") as typeof import("fs");
    const pathMod = require("path");
    sourceCode = realFs.readFileSync(
      pathMod.join(
        __dirname,
        "..",
        "app",
        "api",
        "pipeline",
        "audio-sync",
        "run",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async function POST", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+POST/);
  });

  it("imports spawn from child_process", () => {
    expect(sourceCode).toMatch(/child_process/);
    expect(sourceCode).toMatch(/spawn/);
  });

  it("imports registerExecutor and runPipelineStage from @/lib/jobs", () => {
    expect(sourceCode).toMatch(/@\/lib\/jobs/);
    expect(sourceCode).toMatch(/registerExecutor/);
    expect(sourceCode).toMatch(/runPipelineStage/);
    expect(sourceCode).toMatch(/runPipelineStageDirect/);
  });

  it("imports loadProject from @/lib/project", () => {
    expect(sourceCode).toMatch(/@\/lib\/project/);
    expect(sourceCode).toMatch(/loadProject/);
  });

  it("imports SseSend from @/lib/types", () => {
    expect(sourceCode).toMatch(/@\/lib\/types/);
    expect(sourceCode).toMatch(/SseSend/);
  });

  it("calls registerExecutor('audio-sync', ...)", () => {
    expect(sourceCode).toMatch(
      /registerExecutor\s*\(\s*["']audio-sync["']/
    );
  });

  it("resolves a python runtime before spawning sync_audio_pipeline.py", () => {
    expect(sourceCode).toMatch(/resolvePythonRunSpec/);
    expect(sourceCode).toMatch(/sync_audio_pipeline\.py/);
  });

  it("uses getProjectDir() for spawn cwd", () => {
    expect(sourceCode).toMatch(/cwd:\s*getProjectDir\(\)/);
  });

  it("passes SECTION_GROUPS via env", () => {
    expect(sourceCode).toMatch(/SECTION_GROUPS/);
  });

  it("creates SSE stream with correct Content-Type header", () => {
    expect(sourceCode).toMatch(/text\/event-stream/);
  });

  it("sets Cache-Control to no-cache", () => {
    expect(sourceCode).toMatch(/no-cache/);
  });

  it("sets Connection to keep-alive", () => {
    expect(sourceCode).toMatch(/keep-alive/);
  });

  it("uses new Response(stream, ...) for SSE streaming", () => {
    expect(sourceCode).toMatch(/new\s+Response\s*\(\s*stream/);
  });

  it("reads audioSync.sectionGroups from project", () => {
    expect(sourceCode).toMatch(/audioSync/);
    expect(sourceCode).toMatch(/sectionGroups/);
  });

  it("pipes both stdout and stderr from spawn", () => {
    expect(sourceCode).toMatch(/proc\.stdout/);
    expect(sourceCode).toMatch(/proc\.stderr/);
  });

  it("parses JSON lines from stdout for section events", () => {
    expect(sourceCode).toMatch(/JSON\.parse/);
    expect(sourceCode).toMatch(/type.*===.*["']section["']/);
  });
});

// ---------------------------------------------------------------------------
// 10. Source file structure checks — timestamps route
// ---------------------------------------------------------------------------

describe("app/api/pipeline/audio-sync/timestamps/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    const realFs = jest.requireActual("fs") as typeof import("fs");
    const pathMod = require("path");
    sourceCode = realFs.readFileSync(
      pathMod.join(
        __dirname,
        "..",
        "app",
        "api",
        "pipeline",
        "audio-sync",
        "timestamps",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async function GET", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+GET/);
  });

  it("defines WordTimestamp interface with word, start, end, segmentId", () => {
    expect(sourceCode).toMatch(/interface\s+WordTimestamp/);
    expect(sourceCode).toMatch(/word:\s*string/);
    expect(sourceCode).toMatch(/start:\s*number/);
    expect(sourceCode).toMatch(/end:\s*number/);
    expect(sourceCode).toMatch(/segmentId:\s*string/);
  });

  it("reads section param from URL query", () => {
    expect(sourceCode).toMatch(/searchParams/);
    expect(sourceCode).toMatch(/section/);
  });

  it("constructs path using outputs/tts/{sectionId}/word_timestamps.json", () => {
    expect(sourceCode).toMatch(/outputs/);
    expect(sourceCode).toMatch(/tts/);
    expect(sourceCode).toMatch(/word_timestamps\.json/);
  });

  it("uses path.join for file path construction", () => {
    expect(sourceCode).toMatch(/path\.join/);
  });

  it("returns 404 when file does not exist (ENOENT)", () => {
    expect(sourceCode).toMatch(/ENOENT/);
    expect(sourceCode).toMatch(/404/);
  });

  it("returns words array in response body", () => {
    expect(sourceCode).toMatch(/words/);
  });

  it("imports NextResponse from next/server", () => {
    expect(sourceCode).toMatch(/import.*NextResponse.*from\s+["']next\/server["']/);
  });
});

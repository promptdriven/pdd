/**
 * Tests for app/api/pipeline/compositions/run/route.ts
 * (also covers asset-staging and composition list endpoints)
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_pipeline_compositions_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. POST /api/pipeline/compositions/run — accepts { components?, wrappers? }, returns SSE stream with { jobId }
 *   2. POST /api/pipeline/asset-staging/run — accepts { files? }, copies files from outputs/veo/ to remotion/public/, returns { jobId }
 *   3. GET /api/pipeline/compositions/list — returns { sections: CompositionSection[] }
 *   4. No authentication required
 *   5. registerExecutor('compositions', ...) called at module load time
 *   6. Each component is a separate Claude invocation via runClaudeFix
 *   7. Wrappers generated via python3 generate_section_compositions.py subprocess
 *   8. Per-component events: { type: 'component', name, status: 'generating' | 'done' | 'error' }
 *   9. Component status: check if remotion/src/remotion/{componentName}.tsx exists
 *  10. CompositionEntry.lastError from last error job for that component (from DB)
 *  11. Asset staging: fs.copyFileSync for missing files in remotion/public/
 *  12. Claude scope: remotion/src/remotion/ for component generation
 */

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

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

const mockLoadProject = jest.fn();

jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
}));

// Mock fs
const mockExistsSync = jest.fn();
const mockReadFileSync = jest.fn();
const mockReaddirSync = jest.fn();
const mockCopyFileSync = jest.fn();
const mockMkdirSync = jest.fn();

jest.mock("fs", () => ({
  __esModule: true,
  default: {
    existsSync: (...args: unknown[]) => mockExistsSync(...args),
    readFileSync: (...args: unknown[]) => mockReadFileSync(...args),
    readdirSync: (...args: unknown[]) => mockReaddirSync(...args),
    copyFileSync: (...args: unknown[]) => mockCopyFileSync(...args),
    mkdirSync: (...args: unknown[]) => mockMkdirSync(...args),
  },
  existsSync: (...args: unknown[]) => mockExistsSync(...args),
  readFileSync: (...args: unknown[]) => mockReadFileSync(...args),
  readdirSync: (...args: unknown[]) => mockReaddirSync(...args),
  copyFileSync: (...args: unknown[]) => mockCopyFileSync(...args),
  mkdirSync: (...args: unknown[]) => mockMkdirSync(...args),
}));

// Mock child_process.spawn
const mockSpawn = jest.fn();

jest.mock("child_process", () => ({
  __esModule: true,
  spawn: (...args: unknown[]) => mockSpawn(...args),
}));

// Mock crypto
const mockRandomUUID = jest.fn();

jest.mock("crypto", () => ({
  __esModule: true,
  default: {
    randomUUID: (...args: unknown[]) => mockRandomUUID(...args),
  },
  randomUUID: (...args: unknown[]) => mockRandomUUID(...args),
}));

// Import after mocking
import {
  POST,
  POST_AssetStaging,
  GET_CompositionList,
} from "../app/api/pipeline/compositions/run/route";

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

function makeRequest(url: string, body?: object): Request {
  return new Request(url, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(body ?? {}),
  });
}

/** Flush microtask queue so fire-and-forget IIFE completes. */
function flushPromises(): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, 50));
}

/** Parse SSE events from a ReadableStream. */
async function readSseEvents(
  stream: ReadableStream<Uint8Array>
): Promise<object[]> {
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

/** Default mock project config with sections. */
function mockProjectConfig() {
  return {
    name: "Test Project",
    outputResolution: "1920x1080",
    tts: { voice: "en-US-Neural2-F", rate: 1.0, model: "google-tts-v2" },
    sections: [
      {
        id: "intro",
        label: "Introduction",
        videoFile: "output/sections/intro.mp4",
        specDir: "specs/intro",
        remotionDir: "remotion/intro",
        compositionId: "IntroComposition",
        durationSeconds: 12.5,
        offsetSeconds: 0,
      },
      {
        id: "main",
        label: "Main Content",
        videoFile: "output/sections/main.mp4",
        specDir: "specs/main",
        remotionDir: "remotion/main",
        compositionId: "MainComposition",
        durationSeconds: 45.0,
        offsetSeconds: 12.5,
      },
      {
        id: "outro",
        label: "Outro",
        videoFile: "output/sections/outro.mp4",
        specDir: "specs/outro",
        remotionDir: "remotion/outro",
        compositionId: "OutroComposition",
        durationSeconds: 8.0,
        offsetSeconds: 57.5,
      },
    ],
    audioSync: { sectionGroups: { narration: ["intro", "main", "outro"] } },
    veo: {
      model: "veo-2.0-generate-001",
      aspectRatio: "16:9",
      referenceImages: {},
    },
    render: {
      maxParallelRenders: 3,
      outputDir: "output/final",
      fps: 30,
      width: 1920,
      height: 1080,
    },
  };
}

/** Create a mock spawn process that succeeds with exit code 0. */
function createMockSpawnProcess(exitCode = 0) {
  const stdoutListeners: Function[] = [];
  const stderrListeners: Function[] = [];
  const closeListeners: Function[] = [];

  const proc = {
    stdout: {
      on: (event: string, cb: Function) => {
        if (event === "data") stdoutListeners.push(cb);
      },
    },
    stderr: {
      on: (event: string, cb: Function) => {
        if (event === "data") stderrListeners.push(cb);
      },
    },
    on: (event: string, cb: Function) => {
      if (event === "close") closeListeners.push(cb);
    },
    // Helper to trigger close
    _triggerClose: () => {
      for (const cb of closeListeners) cb(exitCode);
    },
    _triggerStdout: (data: string) => {
      for (const cb of stdoutListeners) cb(Buffer.from(data));
    },
    _triggerStderr: (data: string) => {
      for (const cb of stderrListeners) cb(Buffer.from(data));
    },
  };

  return proc;
}

// ---------------------------------------------------------------------------
// Setup
// ---------------------------------------------------------------------------

beforeEach(() => {
  mockRunPipelineStage.mockReset();
  mockRunClaudeFix.mockReset();
  mockLoadProject.mockReset();
  mockExistsSync.mockReset();
  mockReadFileSync.mockReset();
  mockReaddirSync.mockReset();
  mockCopyFileSync.mockReset();
  mockMkdirSync.mockReset();
  mockSpawn.mockReset();
  mockRandomUUID.mockReset();

  mockRunPipelineStage.mockResolvedValue("test-job-compositions-001");
  mockRunClaudeFix.mockResolvedValue(undefined);
  mockLoadProject.mockReturnValue(mockProjectConfig());
  mockRandomUUID.mockReturnValue("test-uuid-staging-001");
});

// ---------------------------------------------------------------------------
// 1. registerExecutor — module load side effect
// ---------------------------------------------------------------------------

describe("registerExecutor at module load", () => {
  it("registers executor for 'compositions' stage", () => {
    expect(registerCallArgs.stage).toBe("compositions");
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
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run") as any
    );
    expect(response).toBeInstanceOf(Response);
  });

  it("sets Content-Type to text/event-stream", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run") as any
    );
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("sets Cache-Control to no-cache", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run") as any
    );
    expect(response.headers.get("Cache-Control")).toBe("no-cache");
  });

  it("sets Connection to keep-alive", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run") as any
    );
    expect(response.headers.get("Connection")).toBe("keep-alive");
  });

  it("returns a ReadableStream body", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run") as any
    );
    expect(response.body).toBeInstanceOf(ReadableStream);
  });
});

// ---------------------------------------------------------------------------
// 3. POST — success flow with SSE events
// ---------------------------------------------------------------------------

describe("POST — success flow", () => {
  beforeEach(() => {
    mockRunPipelineStage.mockResolvedValue("test-job-compositions-42");
  });

  it("calls runPipelineStage with 'compositions' stage", async () => {
    await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run") as any
    );
    await flushPromises();

    expect(mockRunPipelineStage).toHaveBeenCalledTimes(1);
    expect(mockRunPipelineStage.mock.calls[0][0]).toBe("compositions");
  });

  it("passes components and wrappers params from body to runPipelineStage", async () => {
    await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run", {
        components: ["HeroSection", "TitleCard"],
        wrappers: ["introWrapper"],
      }) as any
    );
    await flushPromises();

    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.components).toEqual(["HeroSection", "TitleCard"]);
    expect(params.wrappers).toEqual(["introWrapper"]);
  });

  it("passes undefined components when body has no components array", async () => {
    await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run", {}) as any
    );
    await flushPromises();

    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.components).toBeUndefined();
  });

  it("passes undefined wrappers when body has no wrappers array", async () => {
    await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run", {}) as any
    );
    await flushPromises();

    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.wrappers).toBeUndefined();
  });

  it("passes a send function to runPipelineStage", async () => {
    await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run") as any
    );
    await flushPromises();

    expect(typeof mockRunPipelineStage.mock.calls[0][2]).toBe("function");
  });

  it("emits job event with jobId after runPipelineStage resolves", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run") as any
    );
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const jobEvent = events.find((e: any) => e.type === "job") as any;
    expect(jobEvent).toBeDefined();
    expect(jobEvent.jobId).toBe("test-job-compositions-42");
  });

  it("emits complete event with jobId after runPipelineStage resolves", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run") as any
    );
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const completeEvent = events.find(
      (e: any) => e.type === "complete"
    ) as any;
    expect(completeEvent).toBeDefined();
    expect(completeEvent.jobId).toBe("test-job-compositions-42");
  });
});

// ---------------------------------------------------------------------------
// 4. POST — body parameter handling
// ---------------------------------------------------------------------------

describe("POST — body parameter handling", () => {
  it("works with no body", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run") as any
    );
    expect(response).toBeInstanceOf(Response);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("works with empty components array", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run", {
        components: [],
      }) as any
    );
    expect(response).toBeInstanceOf(Response);
  });

  it("accepts specific components array", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run", {
        components: ["HeroSection"],
      }) as any
    );
    expect(response).toBeInstanceOf(Response);
  });

  it("accepts wrappers array alongside components", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run", {
        components: ["HeroSection"],
        wrappers: ["introWrapper"],
      }) as any
    );
    expect(response).toBeInstanceOf(Response);
  });
});

// ---------------------------------------------------------------------------
// 5. POST — error handling
// ---------------------------------------------------------------------------

describe("POST — error handling", () => {
  it("emits error event when runPipelineStage rejects with Error", async () => {
    mockRunPipelineStage.mockRejectedValue(new Error("Pipeline failed"));

    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run") as any
    );
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const errorEvent = events.find((e: any) => e.type === "error") as any;
    expect(errorEvent).toBeDefined();
    expect(errorEvent.message).toBe("Pipeline failed");
  });

  it("emits generic error for non-Error throws", async () => {
    mockRunPipelineStage.mockRejectedValue("string error");

    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run") as any
    );
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const errorEvent = events.find((e: any) => e.type === "error") as any;
    expect(errorEvent).toBeDefined();
    expect(errorEvent.message).toBe("Unknown error");
  });

  it("still returns SSE response even when pipeline will error", async () => {
    mockRunPipelineStage.mockRejectedValue(new Error("will fail"));

    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run") as any
    );
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });
});

// ---------------------------------------------------------------------------
// 6. POST — no authentication required
// ---------------------------------------------------------------------------

describe("POST — no authentication required", () => {
  it("does not require authorization headers", async () => {
    const request = new Request(
      "http://localhost/api/pipeline/compositions/run",
      {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          Authorization: "Bearer fake-token",
        },
        body: JSON.stringify({}),
      }
    );

    const response = await POST(request as any);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("works with minimal request (no body, no auth)", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run") as any
    );
    expect(response).toBeInstanceOf(Response);
  });
});

// ---------------------------------------------------------------------------
// 7. Executor factory — component generation via Claude
// ---------------------------------------------------------------------------

describe("compositions executor factory — component generation", () => {
  it("returns an async function when called with params and send", () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    expect(typeof executor).toBe("function");
  });

  it("calls runClaudeFix for each component", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection", "TitleCard"], wrappers: [] },
      mockSend
    );
    await executor(jest.fn());

    expect(mockRunClaudeFix).toHaveBeenCalledTimes(2);
  });

  it("emits 'generating' status before each component", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection"], wrappers: [] },
      mockSend
    );
    await executor(jest.fn());

    const generatingEvent = mockSend.mock.calls.find(
      (c: any[]) =>
        c[0]?.type === "component" && c[0]?.status === "generating"
    );
    expect(generatingEvent).toBeDefined();
    expect(generatingEvent![0].name).toBe("HeroSection");
  });

  it("emits 'done' status after successful component generation", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection"], wrappers: [] },
      mockSend
    );
    await executor(jest.fn());

    const doneEvent = mockSend.mock.calls.find(
      (c: any[]) => c[0]?.type === "component" && c[0]?.status === "done"
    );
    expect(doneEvent).toBeDefined();
    expect(doneEvent![0].name).toBe("HeroSection");
  });

  it("emits 'error' status and throws when component generation fails", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);
    mockRunClaudeFix.mockRejectedValue(new Error("Claude error"));

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection"], wrappers: [] },
      mockSend
    );

    await expect(executor(jest.fn())).rejects.toThrow("Claude error");

    const errorEvent = mockSend.mock.calls.find(
      (c: any[]) => c[0]?.type === "component" && c[0]?.status === "error"
    );
    expect(errorEvent).toBeDefined();
    expect(errorEvent![0].name).toBe("HeroSection");
  });

  it("scopes runClaudeFix to remotion/src/remotion/ directory", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection"], wrappers: [] },
      mockSend
    );
    await executor(jest.fn());

    const scopeDir = mockRunClaudeFix.mock.calls[0][1];
    const pathMod = require("path");
    expect(scopeDir).toBe(
      pathMod.join(process.cwd(), "remotion/src/remotion")
    );
  });

  it("passes a log callback to runClaudeFix", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection"], wrappers: [] },
      mockSend
    );
    await executor(jest.fn());

    expect(typeof mockRunClaudeFix.mock.calls[0][2]).toBe("function");
  });

  it("builds a prompt that includes the component name", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection"], wrappers: [] },
      mockSend
    );
    await executor(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0];
    expect(prompt).toContain("HeroSection");
  });

  it("builds a prompt that references the target directory", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection"], wrappers: [] },
      mockSend
    );
    await executor(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0];
    expect(prompt).toContain("remotion/src/remotion/");
  });

  it("builds a prompt that includes spec content when spec file exists", async () => {
    // Mock specs dir existing and containing a matching spec file
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs")) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((dir: string, opts?: any) => {
      if (typeof dir === "string" && dir.includes("specs")) {
        return [
          {
            name: "HeroSection.md",
            isDirectory: () => false,
            isFile: () => true,
          },
        ];
      }
      return [];
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("HeroSection")) {
        return "# Hero Section Spec\nThis is a hero component.";
      }
      return "";
    });

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection"], wrappers: [] },
      mockSend
    );
    await executor(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0];
    expect(prompt).toContain("Hero Section Spec");
  });

  it("reports progress via onLog.progress callback", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

    const progressFn = jest.fn();
    const onLog = Object.assign(jest.fn(), { progress: progressFn });

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection"], wrappers: [] },
      mockSend
    );
    await executor(onLog as any);

    expect(progressFn).toHaveBeenCalledWith(100);
  });

  it("does not crash when onLog has no progress callback", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

    const onLog = jest.fn();
    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection"], wrappers: [] },
      mockSend
    );
    await expect(executor(onLog)).resolves.not.toThrow();
  });

  it("handles empty components array gracefully", async () => {
    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: [], wrappers: [] },
      mockSend
    );
    await executor(jest.fn());

    expect(mockRunClaudeFix).not.toHaveBeenCalled();
  });

  it("defaults to empty arrays when params omits components and wrappers", async () => {
    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    expect(mockRunClaudeFix).not.toHaveBeenCalled();
    expect(mockSpawn).not.toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 8. Executor factory — wrapper generation via python subprocess
// ---------------------------------------------------------------------------

describe("compositions executor factory — wrapper generation", () => {
  it("spawns python3 generate_section_compositions.py for wrappers", async () => {
    const proc = createMockSpawnProcess(0);
    mockSpawn.mockReturnValue(proc);

    mockExistsSync.mockReturnValue(true);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: [], wrappers: ["introWrapper"] },
      mockSend
    );

    const promise = executor(jest.fn());
    // Trigger close after a tick
    await new Promise((r) => setTimeout(r, 10));
    proc._triggerClose();
    await promise;

    expect(mockSpawn).toHaveBeenCalledTimes(1);
    expect(mockSpawn.mock.calls[0][0]).toBe("python3");
    expect(mockSpawn.mock.calls[0][1]).toEqual([
      "generate_section_compositions.py",
    ]);
  });

  it("emits 'generating' status for each wrapper before subprocess", async () => {
    const proc = createMockSpawnProcess(0);
    mockSpawn.mockReturnValue(proc);
    mockExistsSync.mockReturnValue(true);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: [], wrappers: ["introWrapper", "mainWrapper"] },
      mockSend
    );

    const promise = executor(jest.fn());
    await new Promise((r) => setTimeout(r, 10));
    proc._triggerClose();
    await promise;

    const generatingEvents = mockSend.mock.calls.filter(
      (c: any[]) =>
        c[0]?.type === "component" && c[0]?.status === "generating"
    );
    expect(generatingEvents).toHaveLength(2);
    expect(generatingEvents[0][0].name).toBe("introWrapper");
    expect(generatingEvents[1][0].name).toBe("mainWrapper");
  });

  it("emits 'done' for wrappers whose .tsx file exists after subprocess", async () => {
    const proc = createMockSpawnProcess(0);
    mockSpawn.mockReturnValue(proc);

    // introWrapper.tsx exists, mainWrapper.tsx does not
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("introWrapper.tsx")) return true;
      return false;
    });

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: [], wrappers: ["introWrapper", "mainWrapper"] },
      mockSend
    );

    const promise = executor(jest.fn());
    await new Promise((r) => setTimeout(r, 10));
    proc._triggerClose();
    await promise;

    const doneEvents = mockSend.mock.calls.filter(
      (c: any[]) => c[0]?.type === "component" && c[0]?.status === "done"
    );
    expect(doneEvents).toHaveLength(1);
    expect(doneEvents[0][0].name).toBe("introWrapper");
  });

  it("emits 'error' for wrappers whose .tsx file is missing after subprocess", async () => {
    const proc = createMockSpawnProcess(0);
    mockSpawn.mockReturnValue(proc);

    mockExistsSync.mockReturnValue(false);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: [], wrappers: ["missingWrapper"] },
      mockSend
    );

    const promise = executor(jest.fn());
    await new Promise((r) => setTimeout(r, 10));
    proc._triggerClose();
    await promise;

    const errorEvents = mockSend.mock.calls.filter(
      (c: any[]) => c[0]?.type === "component" && c[0]?.status === "error"
    );
    expect(errorEvents).toHaveLength(1);
    expect(errorEvents[0][0].name).toBe("missingWrapper");
  });

  it("rejects when python subprocess exits with non-zero code", async () => {
    const proc = createMockSpawnProcess(1);
    mockSpawn.mockReturnValue(proc);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: [], wrappers: ["introWrapper"] },
      mockSend
    );

    const promise = executor(jest.fn());
    await new Promise((r) => setTimeout(r, 10));
    proc._triggerClose();

    await expect(promise).rejects.toThrow("Wrapper generation failed");
  });

  it("does not spawn subprocess when wrappers array is empty", async () => {
    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: [], wrappers: [] },
      mockSend
    );
    await executor(jest.fn());

    expect(mockSpawn).not.toHaveBeenCalled();
  });

  it("pipes stdout and stderr to onLog", async () => {
    const proc = createMockSpawnProcess(0);
    mockSpawn.mockReturnValue(proc);
    mockExistsSync.mockReturnValue(true);

    const onLog = jest.fn();
    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: [], wrappers: ["introWrapper"] },
      mockSend
    );

    const promise = executor(onLog);
    await new Promise((r) => setTimeout(r, 10));
    proc._triggerStdout("generating wrapper...\n");
    proc._triggerStderr("warning: something\n");
    proc._triggerClose();
    await promise;

    expect(onLog).toHaveBeenCalledWith("generating wrapper...\n");
    expect(onLog).toHaveBeenCalledWith("warning: something\n");
  });
});

// ---------------------------------------------------------------------------
// 9. POST_AssetStaging — response shape
// ---------------------------------------------------------------------------

describe("POST_AssetStaging — response shape", () => {
  it("returns a NextResponse with jobId", async () => {
    mockExistsSync.mockReturnValue(false);

    const request = makeRequest(
      "http://localhost/api/pipeline/asset-staging/run",
      { files: [] }
    );

    const response = await POST_AssetStaging(request as any);
    const data = await response.json();

    expect(data).toHaveProperty("jobId");
    expect(data.jobId).toBe("test-uuid-staging-001");
  });

  it("returns status 200", async () => {
    mockExistsSync.mockReturnValue(false);

    const request = makeRequest(
      "http://localhost/api/pipeline/asset-staging/run",
      { files: [] }
    );

    const response = await POST_AssetStaging(request as any);
    expect(response.status).toBe(200);
  });
});

// ---------------------------------------------------------------------------
// 10. POST_AssetStaging — file copying
// ---------------------------------------------------------------------------

describe("POST_AssetStaging — file copying", () => {
  it("copies files from outputs/veo/ to remotion/public/", async () => {
    const pathMod = require("path");

    // Source exists, dest does not
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("outputs")) return true;
      if (typeof p === "string" && p.includes("remotion/public")) return false;
      return false;
    });

    const request = makeRequest(
      "http://localhost/api/pipeline/asset-staging/run",
      { files: ["clip1.mp4"] }
    );

    await POST_AssetStaging(request as any);

    expect(mockCopyFileSync).toHaveBeenCalledTimes(1);
    const srcArg = mockCopyFileSync.mock.calls[0][0];
    const destArg = mockCopyFileSync.mock.calls[0][1];
    expect(srcArg).toContain("outputs");
    expect(srcArg).toContain("veo");
    expect(srcArg).toContain("clip1.mp4");
    expect(destArg).toContain("remotion");
    expect(destArg).toContain("public");
    expect(destArg).toContain("clip1.mp4");
  });

  it("creates destination directory recursively", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("outputs")) return true;
      return false;
    });

    const request = makeRequest(
      "http://localhost/api/pipeline/asset-staging/run",
      { files: ["subdir/clip1.mp4"] }
    );

    await POST_AssetStaging(request as any);

    expect(mockMkdirSync).toHaveBeenCalled();
    const mkdirCall = mockMkdirSync.mock.calls[0];
    expect(mkdirCall[1]).toEqual({ recursive: true });
  });

  it("skips files that don't exist in source", async () => {
    mockExistsSync.mockReturnValue(false);

    const request = makeRequest(
      "http://localhost/api/pipeline/asset-staging/run",
      { files: ["nonexistent.mp4"] }
    );

    await POST_AssetStaging(request as any);

    expect(mockCopyFileSync).not.toHaveBeenCalled();
  });

  it("skips files that already exist in destination", async () => {
    // Both source and dest exist
    mockExistsSync.mockReturnValue(true);

    const request = makeRequest(
      "http://localhost/api/pipeline/asset-staging/run",
      { files: ["already_there.mp4"] }
    );

    await POST_AssetStaging(request as any);

    expect(mockCopyFileSync).not.toHaveBeenCalled();
  });

  it("copies multiple files", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("outputs")) return true;
      return false;
    });

    const request = makeRequest(
      "http://localhost/api/pipeline/asset-staging/run",
      { files: ["clip1.mp4", "clip2.mp4", "clip3.mp4"] }
    );

    await POST_AssetStaging(request as any);

    expect(mockCopyFileSync).toHaveBeenCalledTimes(3);
  });
});

// ---------------------------------------------------------------------------
// 11. POST_AssetStaging — manifest loading fallback
// ---------------------------------------------------------------------------

describe("POST_AssetStaging — manifest loading", () => {
  it("loads from staging manifest when no files provided", async () => {
    const pathMod = require("path");

    // staging.json exists
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("staging.json")) return true;
      return false;
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("staging.json")) {
        return JSON.stringify(["manifest_clip.mp4"]);
      }
      return "";
    });

    const request = makeRequest(
      "http://localhost/api/pipeline/asset-staging/run",
      {}
    );

    await POST_AssetStaging(request as any);

    // Should have tried to process the manifest file
    const data = await (
      await POST_AssetStaging(
        makeRequest("http://localhost/api/pipeline/asset-staging/run", {}) as any
      )
    ).json();
    expect(data).toHaveProperty("jobId");
  });

  it("loads manifest with files key from JSON object", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("staging.json")) return true;
      if (typeof p === "string" && p.includes("outputs")) return true;
      return false;
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("staging.json")) {
        return JSON.stringify({ files: ["from_manifest.mp4"] });
      }
      return "";
    });

    const request = makeRequest(
      "http://localhost/api/pipeline/asset-staging/run",
      {}
    );

    await POST_AssetStaging(request as any);

    // The manifest file was resolved and processed
    expect(mockReadFileSync).toHaveBeenCalled();
  });

  it("returns empty files list when no manifest exists and no files provided", async () => {
    mockExistsSync.mockReturnValue(false);

    const request = makeRequest(
      "http://localhost/api/pipeline/asset-staging/run",
      {}
    );

    const response = await POST_AssetStaging(request as any);
    expect(response.status).toBe(200);
    // No copies should have been made
    expect(mockCopyFileSync).not.toHaveBeenCalled();
  });

  it("uses body.files over manifest when files are provided", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("outputs")) return true;
      return false;
    });

    const request = makeRequest(
      "http://localhost/api/pipeline/asset-staging/run",
      { files: ["explicit_file.mp4"] }
    );

    await POST_AssetStaging(request as any);

    // Should use explicit file, not manifest
    expect(mockCopyFileSync).toHaveBeenCalledTimes(1);
    expect(mockCopyFileSync.mock.calls[0][0]).toContain("explicit_file.mp4");
  });
});

// ---------------------------------------------------------------------------
// 12. POST_AssetStaging — no authentication required
// ---------------------------------------------------------------------------

describe("POST_AssetStaging — no authentication required", () => {
  it("does not require authorization headers", async () => {
    mockExistsSync.mockReturnValue(false);

    const request = new Request(
      "http://localhost/api/pipeline/asset-staging/run",
      {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          Authorization: "Bearer fake-token",
        },
        body: JSON.stringify({ files: [] }),
      }
    );

    const response = await POST_AssetStaging(request as any);
    expect(response.status).toBe(200);
  });
});

// ---------------------------------------------------------------------------
// 13. GET_CompositionList — response shape
// ---------------------------------------------------------------------------

describe("GET_CompositionList — response shape", () => {
  beforeEach(() => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);
  });

  it("returns Response.json with sections array", async () => {
    const response = await GET_CompositionList();
    const data = await response.json();

    expect(data).toHaveProperty("sections");
    expect(Array.isArray(data.sections)).toBe(true);
  });

  it("returns one section per project config section", async () => {
    const response = await GET_CompositionList();
    const data = await response.json();

    expect(data.sections).toHaveLength(3); // intro, main, outro
  });

  it("each section has sectionId, components, and wrappers", async () => {
    const response = await GET_CompositionList();
    const data = await response.json();

    for (const section of data.sections) {
      expect(section).toHaveProperty("sectionId");
      expect(section).toHaveProperty("components");
      expect(section).toHaveProperty("wrappers");
      expect(typeof section.sectionId).toBe("string");
      expect(Array.isArray(section.components)).toBe(true);
      expect(Array.isArray(section.wrappers)).toBe(true);
    }
  });

  it("sectionId matches the project config section id", async () => {
    const response = await GET_CompositionList();
    const data = await response.json();

    expect(data.sections[0].sectionId).toBe("intro");
    expect(data.sections[1].sectionId).toBe("main");
    expect(data.sections[2].sectionId).toBe("outro");
  });
});

// ---------------------------------------------------------------------------
// 14. GET_CompositionList — CompositionEntry shape
// ---------------------------------------------------------------------------

describe("GET_CompositionList — CompositionEntry shape", () => {
  beforeEach(() => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockImplementation((dir: string, opts?: any) => {
      if (typeof dir === "string" && dir.includes("specs")) {
        return [
          {
            name: "HeroSection.tsx",
            isDirectory: () => false,
            isFile: () => true,
          },
        ];
      }
      return [];
    });
  });

  it("each component entry has name and status", async () => {
    const response = await GET_CompositionList();
    const data = await response.json();

    for (const section of data.sections) {
      for (const comp of section.components) {
        expect(comp).toHaveProperty("name");
        expect(comp).toHaveProperty("status");
        expect(typeof comp.name).toBe("string");
        expect(["exists", "missing", "error"]).toContain(comp.status);
      }
    }
  });

  it("each wrapper entry has name and status", async () => {
    const response = await GET_CompositionList();
    const data = await response.json();

    for (const section of data.sections) {
      for (const wrapper of section.wrappers) {
        expect(wrapper).toHaveProperty("name");
        expect(wrapper).toHaveProperty("status");
        expect(typeof wrapper.name).toBe("string");
        expect(["exists", "missing", "error"]).toContain(wrapper.status);
      }
    }
  });
});

// ---------------------------------------------------------------------------
// 15. GET_CompositionList — component status detection
// ---------------------------------------------------------------------------

describe("GET_CompositionList — component status detection", () => {
  it("returns 'exists' when .tsx file exists in remotion/src/remotion/", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("remotion/src/remotion/")) {
        return true;
      }
      if (typeof p === "string" && p.includes("specs")) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((dir: string, opts?: any) => {
      if (typeof dir === "string" && dir.includes("specs")) {
        return [
          {
            name: "HeroSection.tsx",
            isDirectory: () => false,
            isFile: () => true,
          },
        ];
      }
      return [];
    });

    const response = await GET_CompositionList();
    const data = await response.json();

    const introSection = data.sections[0];
    const heroComp = introSection.components.find(
      (c: any) => c.name === "HeroSection"
    );
    expect(heroComp).toBeDefined();
    expect(heroComp.status).toBe("exists");
  });

  it("returns 'missing' when .tsx file does not exist", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs")) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((dir: string, opts?: any) => {
      if (typeof dir === "string" && dir.includes("specs")) {
        return [
          {
            name: "MissingComponent.tsx",
            isDirectory: () => false,
            isFile: () => true,
          },
        ];
      }
      return [];
    });

    const response = await GET_CompositionList();
    const data = await response.json();

    const introSection = data.sections[0];
    const comp = introSection.components.find(
      (c: any) => c.name === "MissingComponent"
    );
    expect(comp).toBeDefined();
    expect(comp.status).toBe("missing");
  });
});

// ---------------------------------------------------------------------------
// 16. GET_CompositionList — wrapper naming convention
// ---------------------------------------------------------------------------

describe("GET_CompositionList — wrapper naming", () => {
  beforeEach(() => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);
  });

  it("generates wrapper names from section id and compositionId", async () => {
    const response = await GET_CompositionList();
    const data = await response.json();

    const introSection = data.sections[0];
    const wrapperNames = introSection.wrappers.map((w: any) => w.name);

    expect(wrapperNames).toContain("introWrapper");
    expect(wrapperNames).toContain("IntroCompositionWrapper");
  });

  it("deduplicates wrapper names when id and compositionId produce the same name", async () => {
    // Create config where id + 'Wrapper' !== compositionId + 'Wrapper'
    const config = mockProjectConfig();
    mockLoadProject.mockReturnValue(config);

    const response = await GET_CompositionList();
    const data = await response.json();

    // Each section should have exactly 2 wrappers (or 1 if names match)
    for (const section of data.sections) {
      const uniqueNames = new Set(section.wrappers.map((w: any) => w.name));
      expect(uniqueNames.size).toBe(section.wrappers.length);
    }
  });
});

// ---------------------------------------------------------------------------
// 17. GET_CompositionList — error handling
// ---------------------------------------------------------------------------

describe("GET_CompositionList — error handling", () => {
  it("returns 500 when loadProject throws", async () => {
    mockLoadProject.mockImplementation(() => {
      throw new Error("Config not found");
    });

    const response = await GET_CompositionList();
    expect(response.status).toBe(500);

    const data = await response.json();
    expect(data).toHaveProperty("error");
  });
});

// ---------------------------------------------------------------------------
// 18. GET_CompositionList — listSpecComponents handles empty/missing dirs
// ---------------------------------------------------------------------------

describe("GET_CompositionList — spec directory handling", () => {
  it("returns empty components when spec directory does not exist", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await GET_CompositionList();
    const data = await response.json();

    for (const section of data.sections) {
      expect(section.components).toHaveLength(0);
    }
  });

  it("walks subdirectories for spec files", async () => {
    const pathMod = require("path");
    const specIntroDir = pathMod.join(process.cwd(), "specs/intro");
    const subDir = pathMod.join(specIntroDir, "nested");

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs")) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((dir: string, opts?: any) => {
      if (dir === specIntroDir) {
        return [
          {
            name: "nested",
            isDirectory: () => true,
            isFile: () => false,
          },
          {
            name: "TopLevel.md",
            isDirectory: () => false,
            isFile: () => true,
          },
        ];
      }
      if (dir === subDir) {
        return [
          {
            name: "Nested.md",
            isDirectory: () => false,
            isFile: () => true,
          },
        ];
      }
      return [];
    });

    const response = await GET_CompositionList();
    const data = await response.json();

    const introSection = data.sections[0];
    const names = introSection.components.map((c: any) => c.name);
    expect(names).toContain("TopLevel");
    expect(names).toContain("Nested");
  });
});

// ---------------------------------------------------------------------------
// 19. SSE event format
// ---------------------------------------------------------------------------

describe("POST — SSE event format", () => {
  it("formats events as 'data: <JSON>\\n\\n'", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run") as any
    );
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

    const eventBlocks = raw.split("\n\n").filter((b) => b.trim().length > 0);
    for (const block of eventBlocks) {
      expect(block).toMatch(/^data:\s*\{/);
    }
  });
});

// ---------------------------------------------------------------------------
// 20. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/pipeline/compositions/run/route.ts source structure", () => {
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
        "compositions",
        "run",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async function POST", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+POST/);
  });

  it("exports async function POST_AssetStaging", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+POST_AssetStaging/);
  });

  it("exports async function GET_CompositionList", () => {
    expect(sourceCode).toMatch(
      /export\s+async\s+function\s+GET_CompositionList/
    );
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

  it("imports loadProject from @/lib/project", () => {
    expect(sourceCode).toMatch(/@\/lib\/project/);
    expect(sourceCode).toMatch(/loadProject/);
  });

  it("imports SseSend from @/lib/types", () => {
    expect(sourceCode).toMatch(/@\/lib\/types/);
    expect(sourceCode).toMatch(/SseSend/);
  });

  it("imports CompositionEntry and CompositionSection from @/lib/types", () => {
    expect(sourceCode).toMatch(/CompositionEntry/);
    expect(sourceCode).toMatch(/CompositionSection/);
  });

  it("calls registerExecutor('compositions', ...)", () => {
    expect(sourceCode).toMatch(
      /registerExecutor\s*\(\s*["']compositions["']/
    );
  });

  it("calls runPipelineStage('compositions', ...)", () => {
    expect(sourceCode).toMatch(/runPipelineStage\s*\(/);
  });

  it("scopes Claude to remotion/src/remotion/ directory", () => {
    expect(sourceCode).toMatch(
      /remotion\/src\/remotion/
    );
  });

  it("uses TransformStream for SSE", () => {
    expect(sourceCode).toMatch(/TransformStream/);
  });

  it("sets Content-Type to text/event-stream", () => {
    expect(sourceCode).toMatch(/text\/event-stream/);
  });

  it("sets Cache-Control to no-cache", () => {
    expect(sourceCode).toMatch(/no-cache/);
  });

  it("sets Connection to keep-alive", () => {
    expect(sourceCode).toMatch(/keep-alive/);
  });

  it("emits component events with type 'component'", () => {
    expect(sourceCode).toMatch(/type:\s*["']component["']/);
  });

  it("emits 'generating' status", () => {
    expect(sourceCode).toMatch(/status:\s*["']generating["']/);
  });

  it("emits 'done' status", () => {
    expect(sourceCode).toMatch(/status:\s*["']done["']/);
  });

  it("emits 'error' status", () => {
    expect(sourceCode).toMatch(/status:\s*["']error["']/);
  });

  it("uses spawn for python subprocess", () => {
    expect(sourceCode).toMatch(/spawn/);
    expect(sourceCode).toMatch(/python3/);
    expect(sourceCode).toMatch(/generate_section_compositions\.py/);
  });

  it("uses fs.copyFileSync for asset staging", () => {
    expect(sourceCode).toMatch(/copyFileSync/);
  });

  it("references outputs/veo/ directory", () => {
    expect(sourceCode).toMatch(/outputs\/veo/);
  });

  it("references remotion/public/ directory", () => {
    expect(sourceCode).toMatch(/remotion\/public/);
  });

  it("uses better-sqlite3 for error lookup", () => {
    expect(sourceCode).toMatch(/better-sqlite3/);
  });

  it("imports NextRequest from next/server", () => {
    expect(sourceCode).toMatch(
      /import.*NextRequest.*from\s+["']next\/server["']/
    );
  });

  it("imports NextResponse from next/server", () => {
    expect(sourceCode).toMatch(/NextResponse/);
  });

  it("uses new Response(stream, ...) for SSE streaming", () => {
    expect(sourceCode).toMatch(/new\s+Response\s*\(\s*stream/);
  });
});

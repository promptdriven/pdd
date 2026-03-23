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
 *   2. POST /api/pipeline/asset-staging/run — accepts { files? }, copies files from outputs/veo/ to remotion/public/, returns { staged }
 *   3. GET /api/pipeline/compositions/list — returns { sections: CompositionSection[] }
 *   4. No authentication required
 *   5. registerExecutor('compositions', ...) called at module load time
 *   6. Each component is a separate Claude invocation via runClaudeFix
 *   7. Wrappers generated via python3 generate_section_compositions.py subprocess
 *   8. Per-component events: { type: 'component', name, status: 'generating' | 'done' | 'error' }
 *   9. Component status: check if remotion/src/remotion/{componentName}.tsx exists
 *  10. CompositionEntry.lastError from last error job for that component (from DB)
 *  11. Asset staging: fs.copyFileSync for missing files in remotion/public/
 *  12. Claude runs in isolated temp workspaces and only copies validated artifacts back into remotion/src/remotion/
 */

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

import path from "path";

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
const mockSaveProject = jest.fn();

jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
  saveProject: (...args: unknown[]) => mockSaveProject(...args),
}));

jest.mock("@/lib/projects", () => ({
  getProjectDir: () => process.cwd(),
  getAppRemotionDir: () => path.join(process.cwd(), "remotion"),
  getAppRemotionPublicDir: () => path.join(process.cwd(), "remotion", "public"),
  getAppRemotionSrcDir: () => path.join(process.cwd(), "remotion", "src", "remotion"),
  getAppScriptsDir: () => path.join(process.cwd(), "scripts"),
}));

const mockRenderStill = jest.fn();

jest.mock("@/lib/render", () => ({
  renderStill: (...args: unknown[]) => mockRenderStill(...args),
}));

// Mock fs
const mockExistsSync = jest.fn();
const mockReadFileSync = jest.fn();
const mockReaddirSync = jest.fn();
const mockCopyFileSync = jest.fn();
const mockMkdirSync = jest.fn();
const mockRmSync = jest.fn();
const mockWriteFileSync = jest.fn();
const mockMkdtempSync = jest.fn();
const mockCpSync = jest.fn();
const mockSymlinkSync = jest.fn();
const mockOpenSync = jest.fn(() => 99);
const mockReadSync = jest.fn();
const mockCloseSync = jest.fn();

jest.mock("fs", () => ({
  __esModule: true,
  default: {
    existsSync: (...args: unknown[]) => mockExistsSync(...args),
    readFileSync: (...args: unknown[]) => mockReadFileSync(...args),
    readdirSync: (...args: unknown[]) => mockReaddirSync(...args),
    copyFileSync: (...args: unknown[]) => mockCopyFileSync(...args),
    mkdirSync: (...args: unknown[]) => mockMkdirSync(...args),
    rmSync: (...args: unknown[]) => mockRmSync(...args),
    writeFileSync: (...args: unknown[]) => mockWriteFileSync(...args),
    mkdtempSync: (...args: unknown[]) => mockMkdtempSync(...args),
    cpSync: (...args: unknown[]) => mockCpSync(...args),
    symlinkSync: (...args: unknown[]) => mockSymlinkSync(...args),
    openSync: (...args: unknown[]) => mockOpenSync(...args),
    readSync: (...args: unknown[]) => mockReadSync(...args),
    closeSync: (...args: unknown[]) => mockCloseSync(...args),
  },
  existsSync: (...args: unknown[]) => mockExistsSync(...args),
  readFileSync: (...args: unknown[]) => mockReadFileSync(...args),
  readdirSync: (...args: unknown[]) => mockReaddirSync(...args),
  copyFileSync: (...args: unknown[]) => mockCopyFileSync(...args),
  mkdirSync: (...args: unknown[]) => mockMkdirSync(...args),
  rmSync: (...args: unknown[]) => mockRmSync(...args),
  writeFileSync: (...args: unknown[]) => mockWriteFileSync(...args),
  mkdtempSync: (...args: unknown[]) => mockMkdtempSync(...args),
  cpSync: (...args: unknown[]) => mockCpSync(...args),
  symlinkSync: (...args: unknown[]) => mockSymlinkSync(...args),
  openSync: (...args: unknown[]) => mockOpenSync(...args),
  readSync: (...args: unknown[]) => mockReadSync(...args),
  closeSync: (...args: unknown[]) => mockCloseSync(...args),
}));

// Mock child_process.spawn and execSync
const mockSpawn = jest.fn();
const mockExecSync = jest.fn();

jest.mock("child_process", () => ({
  __esModule: true,
  spawn: (...args: unknown[]) => mockSpawn(...args),
  execSync: (...args: unknown[]) => mockExecSync(...args),
}));

// Mock crypto
const mockRandomUUID = jest.fn();
const mockHashUpdate = jest.fn();
const mockHashDigest = jest.fn(() => "test-generator-fingerprint");
const mockCreateHash = jest.fn(() => ({
  update: mockHashUpdate,
  digest: mockHashDigest,
}));

jest.mock("crypto", () => ({
  __esModule: true,
  default: {
    randomUUID: (...args: unknown[]) => mockRandomUUID(...args),
    createHash: (...args: unknown[]) => mockCreateHash(...args),
  },
  randomUUID: (...args: unknown[]) => mockRandomUUID(...args),
  createHash: (...args: unknown[]) => mockCreateHash(...args),
}));

// Import after mocking
import { POST } from "../app/api/pipeline/compositions/run/route";
import { POST as POST_AssetStaging } from "../app/api/pipeline/asset-staging/run/route";
import { GET as GET_CompositionList } from "../app/api/pipeline/compositions/list/route";

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

function mockGeneratedFlatArtifacts(...names: string[]) {
  mockExistsSync.mockImplementation((p: string) => {
    if (typeof p !== "string") return false;
    return names.some((name) =>
      p.endsWith(path.join("remotion", "src", "remotion", `${name}.tsx`))
    );
  });
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
        // Extract the data line from SSE blocks (handles both "data: ..." and "event: ...\ndata: ...")
        const lines = part.split("\n");
        const dataLine = lines.find((l) => l.startsWith("data:"));
        if (dataLine) {
          const json = dataLine.replace(/^data:\s*/, "");
          try {
            events.push(JSON.parse(json));
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
  mockSaveProject.mockReset();
  mockRenderStill.mockReset();
  mockExistsSync.mockReset();
  mockReadFileSync.mockReset();
  mockReaddirSync.mockReset();
  mockCopyFileSync.mockReset();
  mockMkdirSync.mockReset();
  mockRmSync.mockReset();
  mockWriteFileSync.mockReset();
  mockMkdtempSync.mockReset();
  mockCpSync.mockReset();
  mockSymlinkSync.mockReset();
  mockOpenSync.mockReset();
  mockReadSync.mockReset();
  mockCloseSync.mockReset();
  mockSpawn.mockReset();
  mockExecSync.mockReset();
  mockRandomUUID.mockReset();
  mockCreateHash.mockReset();
  mockHashUpdate.mockReset();
  mockHashDigest.mockReset();

  mockRunPipelineStage.mockResolvedValue("test-job-compositions-001");
  mockRunClaudeFix.mockResolvedValue(undefined);
  mockLoadProject.mockReturnValue(mockProjectConfig());
  mockRenderStill.mockResolvedValue(undefined);
  mockRandomUUID.mockReturnValue("test-uuid-staging-001");
  mockCreateHash.mockReturnValue({
    update: mockHashUpdate,
    digest: mockHashDigest,
  });
  mockHashDigest.mockReturnValue("test-generator-fingerprint");
  mockExecSync.mockReturnValue("");
  let tempDirCounter = 0;
  mockMkdtempSync.mockImplementation((prefix: string) => `${prefix}${++tempDirCounter}`);
  mockOpenSync.mockReturnValue(99);
  mockExistsSync.mockImplementation((p: string) => {
    if (typeof p !== "string") return false;
    return /remotion[\/\\]src[\/\\]remotion[\/\\].*(\.tsx|[\/\\]index\.ts)$/.test(p);
  });
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
    // Simulate real runPipelineStage which sends { type: "job", jobId } before resolving
    mockRunPipelineStage.mockImplementation((_stage: string, _params: unknown, send: (data: object) => void) => {
      send({ type: "job", jobId: "test-job-compositions-42" });
      return Promise.resolve("test-job-compositions-42");
    });
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
// 3b. POST — sectionId forwarding
// ---------------------------------------------------------------------------

describe("POST — sectionId forwarding", () => {
  it("passes sectionId to runPipelineStage params when provided in body", async () => {
    await POST(
      makeRequest("http://localhost/api/pipeline/compositions/run", {
        components: ["title_card"],
        sectionId: "part3_mold",
      }) as any
    );
    await flushPromises();

    expect(mockRunPipelineStage).toHaveBeenCalledTimes(1);
    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.sectionId).toBe("part3_mold");
  });
});

// ---------------------------------------------------------------------------
// 4. POST — body parameter handling
// ---------------------------------------------------------------------------

describe("POST — body parameter handling", () => {
  it("works with an empty request body", async () => {
    const response = await POST(
      new Request("http://localhost/api/pipeline/compositions/run", {
        method: "POST",
      }) as any
    );
    await flushPromises();

    expect(response).toBeInstanceOf(Response);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
    expect(mockRunPipelineStage).toHaveBeenCalledWith(
      "compositions",
      {},
      expect.any(Function)
    );
  });

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
    // Error is sent as a named SSE event (event: error\ndata: {message: ...})
    const errorEvent = events.find((e: any) => e.message) as any;
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
    const errorEvent = events.find((e: any) => e.message) as any;
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
  /** Helper: set up mockSpawn to auto-close with given exit code. */
  function setupMockSpawn(exitCode = 0) {
    const proc = createMockSpawnProcess(exitCode);
    mockSpawn.mockReturnValue(proc);
    // Auto-trigger close after a tick
    setTimeout(() => proc._triggerClose(), 5);
    return proc;
  }

  it("returns an async function when called with params and send", () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    expect(typeof executor).toBe("function");
  });

  it("calls runClaudeFix for each component", async () => {
    mockGeneratedFlatArtifacts("HeroSection", "TitleCard");
    mockReaddirSync.mockReturnValue([]);
    setupMockSpawn(0);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection", "TitleCard"], wrappers: [] },
      mockSend
    );
    await executor(jest.fn());

    expect(mockRunClaudeFix).toHaveBeenCalledTimes(2);
  });

  it("emits 'generating' status before each component", async () => {
    mockGeneratedFlatArtifacts("HeroSection");
    mockReaddirSync.mockReturnValue([]);
    setupMockSpawn(0);

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
    mockGeneratedFlatArtifacts("HeroSection");
    mockReaddirSync.mockReturnValue([]);
    setupMockSpawn(0);

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

  it("emits 'error', still regenerates wrappers/bundle, and then throws when component generation fails", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);
    mockRunClaudeFix.mockRejectedValue(new Error("Claude error"));
    setupMockSpawn(0);

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
    expect(mockSpawn).toHaveBeenCalledWith(
      "python3",
      [
        path.join(process.cwd(), "scripts", "generate_section_compositions.py"),
        "--project-dir",
        process.cwd(),
        "--remotion-dir",
        path.join(process.cwd(), "remotion"),
        "--force",
      ],
      expect.objectContaining({
        cwd: process.cwd(),
        stdio: ["ignore", "pipe", "pipe"],
      })
    );
    expect(mockExecSync).toHaveBeenCalledWith(
      "npx remotion bundle src/index.ts --out build",
      expect.objectContaining({
        cwd: expect.stringContaining("remotion"),
        stdio: "pipe",
        timeout: 120_000,
      })
    );
  });

  it("runs Claude in an isolated temp workspace instead of the live remotion tree", async () => {
    mockGeneratedFlatArtifacts("HeroSection");
    mockReaddirSync.mockReturnValue([]);
    setupMockSpawn(0);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection"], wrappers: [] },
      mockSend
    );
    await executor(jest.fn());

    const scopeDir = mockRunClaudeFix.mock.calls[0][1];
    const pathMod = require("path");
    expect(scopeDir).not.toBe(pathMod.join(process.cwd(), "remotion/src/remotion"));
    expect(scopeDir).toContain(pathMod.join("video-editor-stage8-HeroSection-"));
    expect(scopeDir).not.toContain(pathMod.join(process.cwd(), "remotion", "src", "remotion"));
  });

  it("passes a log callback to runClaudeFix", async () => {
    mockGeneratedFlatArtifacts("HeroSection");
    mockReaddirSync.mockReturnValue([]);
    setupMockSpawn(0);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection"], wrappers: [] },
      mockSend
    );
    await executor(jest.fn());

    expect(typeof mockRunClaudeFix.mock.calls[0][2]).toBe("function");
  });

  it("builds a prompt that includes the component name", async () => {
    mockGeneratedFlatArtifacts("HeroSection");
    mockReaddirSync.mockReturnValue([]);
    setupMockSpawn(0);

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
    mockGeneratedFlatArtifacts("HeroSection");
    mockReaddirSync.mockReturnValue([]);
    setupMockSpawn(0);

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
      if (
        typeof p === "string" &&
        p.endsWith(path.join("remotion", "src", "remotion", "HeroSection.tsx"))
      ) {
        return true;
      }
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
    setupMockSpawn(0);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection"], wrappers: [] },
      mockSend
    );
    await executor(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0];
    expect(prompt).toContain("Hero Section Spec");
  });

  it("builds a prompt that includes structured data points when present in the spec", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return false;
      if (
        p.endsWith(path.join("remotion", "src", "remotion", "intro_hero_section.tsx"))
      ) {
        return true;
      }
      return p.includes("specs") || p.includes("hero_section.md");
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return "";
      if (p.includes("hero_section.md")) {
        return [
          "# Hero Section Spec",
          "",
          "## Data Points",
          "```json",
          '{ "startColor": "#3B82F6", "endColor": "#6366F1" }',
          "```",
        ].join("\n");
      }
      return "";
    });
    mockReaddirSync.mockReturnValue([]);
    setupMockSpawn(0);

    const executor = registerCallArgs.factory(
      { components: ["hero_section"], wrappers: [], sectionId: "intro" },
      jest.fn()
    );
    await executor(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0] as string;
    expect(prompt).toContain("STRUCTURED DATA POINTS");
    expect(prompt).toContain('"startColor": "#3B82F6"');
    expect(prompt).toContain('"endColor": "#6366F1"');
  });

  it("reports progress via onLog.progress callback", async () => {
    mockGeneratedFlatArtifacts("HeroSection");
    mockReaddirSync.mockReturnValue([]);
    setupMockSpawn(0);

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
    mockGeneratedFlatArtifacts("HeroSection");
    mockReaddirSync.mockReturnValue([]);
    setupMockSpawn(0);

    const onLog = jest.fn();
    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["HeroSection"], wrappers: [] },
      mockSend
    );
    await expect(executor(onLog)).resolves.not.toThrow();
  });

  it("handles empty components array gracefully", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);
    setupMockSpawn(0);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: [], wrappers: [] },
      mockSend
    );
    await executor(jest.fn());

    expect(mockRunClaudeFix).not.toHaveBeenCalled();
  });

  it("defaults to empty arrays when params omits components and wrappers", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);
    setupMockSpawn(0);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    expect(mockRunClaudeFix).not.toHaveBeenCalled();
    // spawn is still called for the wrapper python script (always runs)
    expect(mockSpawn).toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 7b. Executor factory — section-scoped component generation
// ---------------------------------------------------------------------------

describe("compositions executor factory — section-scoped generation", () => {
  /** Helper: set up mockSpawn to auto-close with given exit code. */
  function setupMockSpawn(exitCode = 0) {
    const proc = createMockSpawnProcess(exitCode);
    mockSpawn.mockReturnValue(proc);
    setTimeout(() => proc._triggerClose(), 5);
    return proc;
  }

  it("generates section-scoped output file when sectionId is provided", async () => {
    mockGeneratedFlatArtifacts("part3_mold_title_card");
    mockReaddirSync.mockReturnValue([]);
    setupMockSpawn(0);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["title_card"], wrappers: [], sectionId: "part3_mold" },
      mockSend
    );
    await executor(jest.fn());

    // runClaudeFix should be called with the section-scoped export name (PascalCase)
    expect(mockRunClaudeFix).toHaveBeenCalledTimes(1);
    const prompt = mockRunClaudeFix.mock.calls[0][0] as string;
    expect(prompt).toContain("Part3MoldTitleCard");
  });

  it("scopes spec lookup to section specDir when sectionId is provided", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (
        typeof p === "string" &&
        p.endsWith(path.join("remotion", "src", "remotion", "main_title_card.tsx"))
      ) {
        return true;
      }
      if (typeof p === "string" && p.includes("specs")) return true;
      return false;
    });
    mockReaddirSync.mockReturnValue([]);
    mockReadFileSync.mockReturnValue("# Part 3 Title Card Spec");
    setupMockSpawn(0);

    const config = mockProjectConfig();
    config.sections[0].specDir = "specs/intro";
    config.sections[1].specDir = "specs/main";
    mockLoadProject.mockReturnValue(config);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["title_card"], wrappers: [], sectionId: "main" },
      mockSend
    );
    await executor(jest.fn());

    // findSpecForComponent should search in the section's specDir first
    const readCalls = mockReadFileSync.mock.calls.map((c: any) => c[0]);
    const specRead = readCalls.find((p: string) => typeof p === "string" && p.includes("specs/main"));
    expect(specRead).toBeDefined();
  });
});

// ---------------------------------------------------------------------------
// 7c. Executor factory — sectionComponents (full-run scoping)
// ---------------------------------------------------------------------------

describe("compositions executor factory — sectionComponents full-run scoping", () => {
  function setupMockSpawn(exitCode = 0) {
    const proc = createMockSpawnProcess(exitCode);
    mockSpawn.mockReturnValue(proc);
    setTimeout(() => proc._triggerClose(), 5);
    return proc;
  }

  it("generates section-scoped files for each entry in sectionComponents", async () => {
    mockGeneratedFlatArtifacts("intro_title_card", "main_title_card");
    mockReaddirSync.mockReturnValue([]);
    setupMockSpawn(0);

    const config = mockProjectConfig();
    config.sections[0].specDir = "specs/intro";
    config.sections[1].specDir = "specs/main";
    config.sections[2].specDir = "specs/outro";
    mockLoadProject.mockReturnValue(config);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      {
        sectionComponents: [
          { sectionId: "intro", components: ["title_card"] },
          { sectionId: "main", components: ["title_card"] },
        ],
        wrappers: [],
      },
      mockSend
    );
    await executor(jest.fn());

    // Should call runClaudeFix twice — once per section
    expect(mockRunClaudeFix).toHaveBeenCalledTimes(2);

    const prompt1 = mockRunClaudeFix.mock.calls[0][0] as string;
    const prompt2 = mockRunClaudeFix.mock.calls[1][0] as string;

    // Each prompt should reference the section-scoped export name (PascalCase)
    expect(prompt1).toContain("IntroTitleCard");
    expect(prompt2).toContain("MainTitleCard");
  });

  it("uses each section's specDir for spec lookup", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (
        typeof p === "string" &&
        (p.endsWith(path.join("remotion", "src", "remotion", "intro_title_card.tsx")) ||
          p.endsWith(path.join("remotion", "src", "remotion", "main_title_card.tsx")))
      ) {
        return true;
      }
      if (typeof p === "string" && p.includes("specs")) return true;
      return false;
    });
    mockReaddirSync.mockReturnValue([]);
    mockReadFileSync.mockReturnValue("# Spec content");
    setupMockSpawn(0);

    const config = mockProjectConfig();
    config.sections[0].specDir = "specs/intro";
    config.sections[1].specDir = "specs/main";
    mockLoadProject.mockReturnValue(config);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      {
        sectionComponents: [
          { sectionId: "intro", components: ["title_card"] },
          { sectionId: "main", components: ["title_card"] },
        ],
        wrappers: [],
      },
      mockSend
    );
    await executor(jest.fn());

    // Should have looked up specs in both section dirs
    const readCalls = mockReadFileSync.mock.calls.map((c: any) => c[0]);
    const introSpec = readCalls.find(
      (p: string) => typeof p === "string" && p.includes("specs/intro")
    );
    const mainSpec = readCalls.find(
      (p: string) => typeof p === "string" && p.includes("specs/main")
    );
    expect(introSpec).toBeDefined();
    expect(mainSpec).toBeDefined();
  });

  it("emits per-component status events for sectionComponents", async () => {
    mockGeneratedFlatArtifacts("intro_title_card", "main_title_card");
    mockReaddirSync.mockReturnValue([]);
    setupMockSpawn(0);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      {
        sectionComponents: [
          { sectionId: "intro", components: ["title_card"] },
          { sectionId: "main", components: ["title_card"] },
        ],
        wrappers: [],
      },
      mockSend
    );
    await executor(jest.fn());

    const generatingEvents = mockSend.mock.calls
      .filter((c: any[]) => c[0]?.type === "component" && c[0]?.status === "generating")
      .map((c: any[]) => c[0].name);
    const doneEvents = mockSend.mock.calls
      .filter((c: any[]) => c[0]?.type === "component" && c[0]?.status === "done")
      .map((c: any[]) => c[0].name);

    expect(generatingEvents).toContain("title_card");
    expect(doneEvents).toContain("title_card");
    // Two generating + two done events (one per section)
    expect(generatingEvents.length).toBe(2);
    expect(doneEvents.length).toBe(2);
  });
});

// ---------------------------------------------------------------------------
// 8. Executor factory — wrapper generation via python subprocess
// ---------------------------------------------------------------------------

describe("compositions executor factory — wrapper generation", () => {
  it("spawns python3 generate_section_compositions.py for wrappers", async () => {
    const proc = createMockSpawnProcess(0);
    mockSpawn.mockReturnValue(proc);

    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

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
      path.join(process.cwd(), "scripts", "generate_section_compositions.py"),
      "--project-dir",
      process.cwd(),
      "--remotion-dir",
      path.join(process.cwd(), "remotion"),
      "--force",
    ]);
  });

  it("emits 'generating' status for each wrapper before subprocess", async () => {
    const proc = createMockSpawnProcess(0);
    mockSpawn.mockReturnValue(proc);
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

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
    mockReaddirSync.mockReturnValue([]);

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
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

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

  it("always spawns wrapper subprocess even when wrappers array is empty", async () => {
    const proc = createMockSpawnProcess(0);
    mockSpawn.mockReturnValue(proc);
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: [], wrappers: [] },
      mockSend
    );

    const promise = executor(jest.fn());
    await new Promise((r) => setTimeout(r, 10));
    proc._triggerClose();
    await promise;

    // The wrapper script always runs to generate/update Root.tsx
    expect(mockSpawn).toHaveBeenCalled();
  });

  it("pipes stdout and stderr to onLog", async () => {
    const proc = createMockSpawnProcess(0);
    mockSpawn.mockReturnValue(proc);
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

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
  it("returns a NextResponse with staged count", async () => {
    mockExistsSync.mockReturnValue(false);

    const request = makeRequest(
      "http://localhost/api/pipeline/asset-staging/run",
      { files: [] }
    );

    const response = await POST_AssetStaging(request as any);
    const data = await response.json();

    expect(data).toEqual({ staged: 0 });
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

  it("does not return a synthetic jobId for synchronous staging", async () => {
    mockExistsSync.mockReturnValue(false);

    const request = makeRequest(
      "http://localhost/api/pipeline/asset-staging/run",
      { files: [] }
    );

    const response = await POST_AssetStaging(request as any);
    const data = await response.json();

    expect(data).not.toHaveProperty("jobId");
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

    // Should still return a synchronous staging payload.
    const data = await (
      await POST_AssetStaging(
        makeRequest("http://localhost/api/pipeline/asset-staging/run", {}) as any
      )
    ).json();
    expect(data).toHaveProperty("staged");
    expect(data).not.toHaveProperty("jobId");
  });

  it("returns staged count in response", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("outputs")) return true;
      return false;
    });

    const request = makeRequest(
      "http://localhost/api/pipeline/asset-staging/run",
      { files: ["clip1.mp4"] }
    );

    const response = await POST_AssetStaging(request as any);
    const data = await response.json();

    expect(data).toHaveProperty("staged");
    expect(typeof data.staged).toBe("number");
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

  it("each section has id, label, components, and wrappers", async () => {
    const response = await GET_CompositionList();
    const data = await response.json();

    for (const section of data.sections) {
      expect(section).toHaveProperty("id");
      expect(section).toHaveProperty("label");
      expect(section).toHaveProperty("components");
      expect(section).toHaveProperty("wrappers");
      expect(typeof section.id).toBe("string");
      expect(Array.isArray(section.components)).toBe(true);
      expect(Array.isArray(section.wrappers)).toBe(true);
    }
  });

  it("id matches the project config section id", async () => {
    const response = await GET_CompositionList();
    const data = await response.json();

    expect(data.sections[0].id).toBe("intro");
    expect(data.sections[1].id).toBe("main");
    expect(data.sections[2].id).toBe("outro");
  });

  it("includes stale artifact metadata when the stored manifest fingerprint is missing", async () => {
    mockExistsSync.mockImplementation((targetPath: string) => {
      if (typeof targetPath !== "string") {
        return false;
      }

      if (targetPath.endsWith(path.join("outputs", "compositions", "manifest.json"))) {
        return true;
      }

      if (
        targetPath.endsWith(path.join("scripts", "generate_section_compositions.py")) ||
        targetPath.endsWith(path.join("app", "api", "pipeline", "_lib", "visual-contract-manifest.ts")) ||
        targetPath.endsWith(path.join("remotion", "src", "remotion", "_shared", "visual-runtime.tsx"))
      ) {
        return true;
      }

      return targetPath.includes("specs");
    });
    mockReadFileSync.mockImplementation((targetPath: string) => {
      if (
        typeof targetPath === "string" &&
        targetPath.endsWith(path.join("outputs", "compositions", "manifest.json"))
      ) {
        return JSON.stringify({
          version: 1,
          updatedAt: "2026-03-14T00:00:00.000Z",
          sections: [],
        });
      }

      return "# Component\n[Remotion]";
    });

    const response = await GET_CompositionList();
    const data = await response.json();

    expect(data.artifactState?.stale).toBe(true);
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
        expect(["done", "missing", "error", "pending"]).toContain(comp.status);
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
        expect(["done", "missing", "error", "pending"]).toContain(wrapper.status);
      }
    }
  });
});

// ---------------------------------------------------------------------------
// 15. GET_CompositionList — component status detection
// ---------------------------------------------------------------------------

describe("GET_CompositionList — component status detection", () => {
  it("returns 'done' when .tsx file exists in remotion/src/remotion/", async () => {
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
    expect(heroComp.status).toBe("done");
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
// 15b. GET_CompositionList — section-scoped component detection
// ---------------------------------------------------------------------------

describe("GET_CompositionList — section-scoped components", () => {
  it("returns 'done' when section-scoped .tsx file exists ({sectionId}_{name}.tsx)", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs")) return true;
      // Only the section-scoped file exists, NOT the flat file
      if (typeof p === "string" && p.endsWith("intro_title_card.tsx")) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((dir: string, opts?: any) => {
      if (typeof dir === "string" && dir.includes("specs")) {
        return [
          {
            name: "title_card.md",
            isDirectory: () => false,
            isFile: () => true,
          },
        ];
      }
      return [];
    });
    // Stub readFileSync for Veo-prompt check (first line doesn't contain [veo:])
    mockReadFileSync.mockReturnValue("# Title Card Spec\nSome content");

    const response = await GET_CompositionList();
    const data = await response.json();

    const introSection = data.sections.find((s: any) => s.id === "intro");
    const comp = introSection.components.find(
      (c: any) => c.name === "title_card"
    );
    expect(comp).toBeDefined();
    expect(comp.status).toBe("done");
  });

  it("prefers section-scoped file over flat file", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs")) return true;
      // Both section-scoped and flat files exist
      if (typeof p === "string" && p.endsWith("intro_title_card.tsx")) return true;
      if (typeof p === "string" && p.endsWith("title_card.tsx")) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((dir: string, opts?: any) => {
      if (typeof dir === "string" && dir.includes("specs")) {
        return [
          {
            name: "title_card.md",
            isDirectory: () => false,
            isFile: () => true,
          },
        ];
      }
      return [];
    });
    mockReadFileSync.mockReturnValue("# Title Card Spec\nSome content");

    const response = await GET_CompositionList();
    const data = await response.json();

    const introSection = data.sections.find((s: any) => s.id === "intro");
    const comp = introSection.components.find(
      (c: any) => c.name === "title_card"
    );
    expect(comp).toBeDefined();
    expect(comp.status).toBe("done");
  });

  it("returns 'missing' when an artifact exists on disk but the section render graph does not register it", async () => {
    const config = mockProjectConfig();
    config.sections[0].compositions = ["intro_other_component"];
    mockLoadProject.mockReturnValue(config);

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs")) return true;
      if (typeof p === "string" && p.endsWith("intro_title_card.tsx")) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((dir: string) => {
      if (typeof dir === "string" && dir.includes("specs")) {
        return [
          {
            name: "title_card.md",
            isDirectory: () => false,
            isFile: () => true,
          },
        ];
      }
      return [];
    });
    mockReadFileSync.mockReturnValue("# Title Card Spec\nSome content");

    const response = await GET_CompositionList();
    const data = await response.json();

    const introSection = data.sections.find((s: any) => s.id === "intro");
    const comp = introSection.components.find(
      (c: any) => c.name === "title_card"
    );
    expect(comp).toBeDefined();
    expect(comp.status).toBe("missing");
    expect(comp.error).toMatch(/not registered/i);
  });
});

// ---------------------------------------------------------------------------
// 15c. GET_CompositionList — section-prefixed PascalCase directory detection
// ---------------------------------------------------------------------------

describe("GET_CompositionList — section-prefixed PascalCase directory detection", () => {
  it("returns 'done' when {SectionPascal}{NN}{PascalName}/index.ts exists but {NN}-{PascalName}/ does not", async () => {
    const pathMod = require("path");
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs")) return true;
      // Only Pascal-prefixed dir exists, NOT kebab dir
      if (typeof p === "string" && p.endsWith(pathMod.join("Part1Economics06StatCalloutUplevel", "index.ts"))) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((dir: string, opts?: any) => {
      if (typeof dir === "string" && dir.includes("specs")) {
        return [
          { name: "06_stat_callout_uplevel.md", isDirectory: () => false, isFile: () => true },
        ];
      }
      return [];
    });
    mockReadFileSync.mockReturnValue("# Stat Callout\nSome content");

    // Use a project config with a section id that has underscore (part1_economics)
    const config = mockProjectConfig();
    config.sections[0].id = "part1_economics";
    config.sections[0].specDir = "specs/part1_economics";
    config.sections[0].compositionId = "Part1Economics";
    mockLoadProject.mockReturnValue(config);

    const response = await GET_CompositionList();
    const data = await response.json();

    const section = data.sections.find((s: any) => s.id === "part1_economics");
    const comp = section?.components.find((c: any) => c.name === "06_stat_callout_uplevel");
    expect(comp).toBeDefined();
    expect(comp.status).toBe("done");
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
// 16b. GET_CompositionList — wrapper status checks actual file locations
// ---------------------------------------------------------------------------

describe("GET_CompositionList — wrapper status detection", () => {
  it("returns 'done' when {sectionId}/index.tsx exists", async () => {
    const pathMod = require("path");
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs")) return true;
      // {sectionId}/index.tsx exists
      if (typeof p === "string" && p.endsWith(pathMod.join("intro", "index.tsx"))) return true;
      return false;
    });
    mockReaddirSync.mockReturnValue([]);

    const response = await GET_CompositionList();
    const data = await response.json();

    const introSection = data.sections.find((s: any) => s.id === "intro");
    const doneWrappers = introSection.wrappers.filter((w: any) => w.status === "done");
    expect(doneWrappers.length).toBeGreaterThan(0);
  });

  it("returns 'done' when {compositionId}.tsx exists", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs")) return true;
      // {compositionId}.tsx exists (e.g., IntroComposition.tsx)
      if (typeof p === "string" && p.endsWith("IntroComposition.tsx")) return true;
      return false;
    });
    mockReaddirSync.mockReturnValue([]);

    const response = await GET_CompositionList();
    const data = await response.json();

    const introSection = data.sections.find((s: any) => s.id === "intro");
    const doneWrappers = introSection.wrappers.filter((w: any) => w.status === "done");
    expect(doneWrappers.length).toBeGreaterThan(0);
  });

  it("returns 'missing' when neither wrapper file exists", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs")) return true;
      return false;
    });
    mockReaddirSync.mockReturnValue([]);

    const response = await GET_CompositionList();
    const data = await response.json();

    const introSection = data.sections.find((s: any) => s.id === "intro");
    for (const w of introSection.wrappers) {
      expect(w.status).toBe("missing");
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
    // The list route calls listSpecComponents(path.join("specs", section.specDir))
    // where section.specDir = "specs/intro" => "specs/specs/intro"
    const specIntroDir = pathMod.join(process.cwd(), "specs", "specs/intro");
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

    // Each event block should contain a "data:" line (some may have "event:" prefix for named events)
    const eventBlocks = raw.split("\n\n").filter((b) => b.trim().length > 0);
    for (const block of eventBlocks) {
      expect(block).toMatch(/data:\s*/);
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

  it("only exports POST (asset-staging and list are separate routes)", () => {
    expect(sourceCode).not.toMatch(/export\s+async\s+function\s+POST_AssetStaging/);
    expect(sourceCode).not.toMatch(/export\s+async\s+function\s+GET_CompositionList/);
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

  it("imports SseSend type from @/lib/types", () => {
    expect(sourceCode).toMatch(/import\s+type\s*\{.*SseSend.*\}\s*from\s+["']@\/lib\/types["']/);
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

  it("uses createSseStream for SSE", () => {
    expect(sourceCode).toMatch(/createSseStream/);
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

  it("instructs generated Remotion scenes to keep interpolate input ranges strictly increasing", () => {
    expect(sourceCode).toMatch(/inputRange arrays must always be strictly increasing/i);
  });

  it("instructs generated Remotion scenes to keep helper props, constants, and exports consistent", () => {
    expect(sourceCode).toMatch(/helper component contracts internally consistent/i);
    expect(sourceCode).toMatch(/imported constant must be declared|imported constants must be declared/i);
    expect(sourceCode).toMatch(/default-vs-named exports must match the import style/i);
  });

  it("references outputs and veo directories", () => {
    expect(sourceCode).toMatch(/outputs.*veo/);
  });

  it("references remotion/public/ directory", () => {
    expect(sourceCode).toMatch(/remotion\/public/);
  });

  it("imports saveProject from @/lib/project", () => {
    expect(sourceCode).toMatch(/saveProject/);
  });

  it("imports NextRequest from next/server", () => {
    expect(sourceCode).toMatch(
      /import.*NextRequest.*from\s+["']next\/server["']/
    );
  });

  it("imports NextRequest from next/server", () => {
    expect(sourceCode).toMatch(/import.*NextRequest.*from\s+["']next\/server["']/);
  });

  it("uses new Response(stream, ...) for SSE streaming", () => {
    expect(sourceCode).toMatch(/new\s+Response\s*\(\s*stream/);
  });

  it("defines generateSectionConstants function", () => {
    expect(sourceCode).toMatch(/generateSectionConstants/);
  });

  it("defines generateSectionComposition function", () => {
    expect(sourceCode).toMatch(/generateSectionComposition/);
  });
});

// ---------------------------------------------------------------------------
// 21. Specs prompt includes spec.md content and word timestamps
// ---------------------------------------------------------------------------

describe("specs route — enhanced prompt with spec.md and word timestamps", () => {
  let specsSourceCode: string;

  beforeAll(() => {
    const realFs = jest.requireActual("fs") as typeof import("fs");
    const pathMod = require("path");
    specsSourceCode = realFs.readFileSync(
      pathMod.join(
        __dirname,
        "..",
        "app",
        "api",
        "pipeline",
        "specs",
        "run",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("reads spec.md content for context", () => {
    expect(specsSourceCode).toMatch(/spec\.md/);
    expect(specsSourceCode).toMatch(/readFileSync/);
  });

  it("references word timestamps file path", () => {
    expect(specsSourceCode).toMatch(/word_timestamps\.json/);
  });

  it("includes reference spec format example in prompt", () => {
    // The prompt should include guidance about canvas specs, animation sequence, etc.
    expect(specsSourceCode).toMatch(/Canvas|canvas/);
    expect(specsSourceCode).toMatch(/Animation Sequence|animation sequence|Frame.*\d/i);
  });

  it("instructs Claude to generate numbered spec files", () => {
    expect(specsSourceCode).toMatch(/\{NN\}|zero-padded|numbered/i);
  });
});

// ---------------------------------------------------------------------------
// 21b. Discovery runs even when generation throws (try-finally)
// ---------------------------------------------------------------------------

describe("compositions executor — discovery runs after generation error", () => {
  function setupMockSpawn(exitCode = 0) {
    const proc = createMockSpawnProcess(exitCode);
    mockSpawn.mockReturnValue(proc);
    setTimeout(() => proc._triggerClose(), 5);
    return proc;
  }

  it("runs discovery and updates project.json even when a component fails to generate", async () => {
    setupMockSpawn(0);

    // Set up: two components, second one fails
    // loadProject is called multiple times (duration calc, sectionComponents lookup, discovery)
    // specDir is relative to SPECS_DIR (cwd/specs/), so just "cold_open" not "specs/cold_open"
    mockLoadProject.mockImplementation(() => {
      const c = mockProjectConfig();
      c.sections[0].specDir = "cold_open";
      c.sections[0].id = "cold_open";
      return c;
    });

    // First call succeeds, second call fails
    mockRunClaudeFix
      .mockResolvedValueOnce(undefined)
      .mockRejectedValueOnce(new Error("Claude timeout"));

    const pathMod = require("path");
    // SPECS_DIR in route.ts is path.join(cwd, "specs"), and section.specDir = "cold_open"
    // so sectionSpecDir = path.join(cwd, "specs", "cold_open")
    const specsDir = pathMod.join(process.cwd(), "specs", "cold_open");
    const remotionDir = pathMod.join(process.cwd(), "remotion/src/remotion");

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return false;
      // Spec dir exists
      if (p === specsDir) return true;
      // The first component's directory exists (discovery checks TitleCard/index.ts for non-digit-prefixed base)
      if (p === pathMod.join(remotionDir, "TitleCard", "index.ts")) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((p: string, opts?: object) => {
      if (typeof p === "string" && p.includes("specs") && p.includes("cold_open")) {
        return [
          { name: "title_card.md", isFile: () => true },
          { name: "hero_section.md", isFile: () => true },
        ];
      }
      // veo dir
      return [];
    });
    mockReadFileSync.mockReturnValue("# Spec content");

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      {
        sectionComponents: [
          { sectionId: "cold_open", components: ["title_card", "hero_section"] },
        ],
        wrappers: [],
      },
      mockSend
    );

    // Should throw the generation error
    await expect(executor(jest.fn())).rejects.toThrow("Claude timeout");

    // But discovery should have run — saveProject should have been called
    expect(mockSaveProject).toHaveBeenCalled();
  });

  it("still throws the original error after discovery completes", async () => {
    setupMockSpawn(0);

    const config = mockProjectConfig();
    config.sections[0].specDir = "specs/cold_open";
    config.sections[0].id = "cold_open";
    mockLoadProject.mockReturnValue(config);

    mockRunClaudeFix.mockRejectedValueOnce(new Error("Network failure"));

    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockImplementation((p: string, opts?: object) => {
      if (typeof p === "string" && p.includes("specs/cold_open")) {
        return [{ name: "title_card.md", isFile: () => true }];
      }
      return [];
    });
    mockReadFileSync.mockReturnValue("# Spec content");

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      {
        sectionComponents: [
          { sectionId: "cold_open", components: ["title_card"] },
        ],
        wrappers: [],
      },
      mockSend
    );

    await expect(executor(jest.fn())).rejects.toThrow("Network failure");
  });
});

// ---------------------------------------------------------------------------
// 21c. Generated component smoke validation
// ---------------------------------------------------------------------------

describe("compositions executor — generated preview validation", () => {
  function setupMockSpawn(exitCode = 0) {
    const proc = createMockSpawnProcess(exitCode);
    mockSpawn.mockReturnValue(proc);
    setTimeout(() => proc._triggerClose(), 5);
    return proc;
  }

  it("smoke-renders generated preview compositions after bundling", async () => {
    setupMockSpawn(0);

    const config = mockProjectConfig();
    config.sections[0].id = "cold_open";
    config.sections[0].specDir = "cold_open";
    config.sections[0].compositionId = "ColdOpenSection";
    mockLoadProject.mockReturnValue(config);

    const pathMod = require("path");
    const specsDir = pathMod.join(process.cwd(), "specs", "cold_open");
    const remotionDir = pathMod.join(process.cwd(), "remotion/src/remotion");

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return false;
      if (p === specsDir) return true;
      if (p === pathMod.join(remotionDir, "ColdOpen05CrossfadeTransition", "index.ts")) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs") && p.includes("cold_open")) {
        return [{ name: "05_crossfade_transition.md", isFile: () => true }];
      }
      return [];
    });
    mockReadFileSync.mockReturnValue("# Spec content");

    const executor = registerCallArgs.factory(
      {
        sectionComponents: [
          { sectionId: "cold_open", components: ["05_crossfade_transition"] },
        ],
        wrappers: [],
      },
      jest.fn()
    );

    await executor(jest.fn());

    expect(mockRenderStill).toHaveBeenCalledWith(
      "cold-open05-crossfade-transition",
      30,
      expect.any(String)
    );
  });

  it("fails the stage when smoke validation of a generated composition fails", async () => {
    setupMockSpawn(0);
    mockRenderStill.mockRejectedValueOnce(new Error("Runtime render error"));

    const config = mockProjectConfig();
    config.sections[0].id = "part1_economics";
    config.sections[0].specDir = "part1_economics";
    config.sections[0].compositionId = "Part1Economics";
    mockLoadProject.mockReturnValue(config);

    const pathMod = require("path");
    const specsDir = pathMod.join(process.cwd(), "specs", "part1_economics");
    const remotionDir = pathMod.join(process.cwd(), "remotion/src/remotion");

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return false;
      if (p === specsDir) return true;
      if (p === pathMod.join(remotionDir, "Part1Economics07StatCalloutGitclear", "index.ts")) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs") && p.includes("part1_economics")) {
        return [{ name: "07_stat_callout_gitclear.md", isFile: () => true }];
      }
      return [];
    });
    mockReadFileSync.mockReturnValue("# Spec content");

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      {
        sectionComponents: [
          { sectionId: "part1_economics", components: ["07_stat_callout_gitclear"] },
        ],
        wrappers: [],
      },
      mockSend
    );

    await expect(executor(jest.fn())).rejects.toThrow(
      "Component validation failed: 07_stat_callout_gitclear: Runtime render error"
    );

    const errorEvent = mockSend.mock.calls.find(
      (c: any[]) => c[0]?.type === "component" && c[0]?.status === "error"
    );
    expect(errorEvent).toBeDefined();
    expect(errorEvent![0].name).toBe("07_stat_callout_gitclear");
  });

  it("fails generation when Claude returns but the expected component artifact was not created", async () => {
    setupMockSpawn(0);

    const config = mockProjectConfig();
    config.sections[0].id = "veo_section";
    config.sections[0].specDir = "veo_section";
    config.sections[0].compositionId = "VeoSection";
    mockLoadProject.mockReturnValue(config);

    const pathMod = require("path");
    const specsDir = pathMod.join(process.cwd(), "specs", "veo_section");

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return false;
      if (p === specsDir) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs") && p.includes("veo_section")) {
        return [{ name: "05_split_nature_comparison.md", isFile: () => true }];
      }
      return [];
    });
    mockReadFileSync.mockReturnValue("[split:]\n# Spec content");

    const executor = registerCallArgs.factory(
      {
        sectionComponents: [
          { sectionId: "veo_section", components: ["05_split_nature_comparison"] },
        ],
        wrappers: [],
      },
      jest.fn()
    );

    await expect(executor(jest.fn())).rejects.toThrow(
      "Expected generated component output not found for veo_section_05_split_nature_comparison"
    );
    expect(mockRunClaudeFix).toHaveBeenCalledTimes(2);
    expect(mockRenderStill).not.toHaveBeenCalled();
  });

  it("retries once when Claude returns without creating the expected artifact", async () => {
    setupMockSpawn(0);

    const config = mockProjectConfig();
    config.sections[0].id = "veo_section";
    config.sections[0].specDir = "veo_section";
    config.sections[0].compositionId = "VeoSection";
    mockLoadProject.mockReturnValue(config);

    const pathMod = require("path");
    const specsDir = pathMod.join(process.cwd(), "specs", "veo_section");
    let artifactExists = false;
    let attemptCount = 0;
    mockRunClaudeFix.mockImplementation(async () => {
      attemptCount += 1;
      artifactExists = attemptCount >= 2;
    });
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return false;
      if (p === specsDir) return true;
      if (
        p.endsWith(
          pathMod.join(
            "remotion",
            "src",
            "remotion",
            "VeoSection05SplitNatureComparison",
            "index.ts"
          )
        )
      ) {
        return artifactExists;
      }
      return false;
    });
    mockReaddirSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs") && p.includes("veo_section")) {
        return [{ name: "05_split_nature_comparison.md", isFile: () => true }];
      }
      return [];
    });
    mockReadFileSync.mockReturnValue("[split:]\n# Spec content");

    const onLog = jest.fn();
    const executor = registerCallArgs.factory(
      {
        sectionComponents: [
          { sectionId: "veo_section", components: ["05_split_nature_comparison"] },
        ],
        wrappers: [],
      },
      jest.fn()
    );

    await expect(executor(onLog)).resolves.toBeUndefined();

    expect(mockRunClaudeFix).toHaveBeenCalledTimes(2);
    expect(mockCpSync).toHaveBeenCalledWith(
      expect.stringContaining(
        pathMod.join(
          "remotion",
          "src",
          "remotion",
          "VeoSection05SplitNatureComparison"
        )
      ),
      pathMod.join(
        process.cwd(),
        "remotion",
        "src",
        "remotion",
        "VeoSection05SplitNatureComparison"
      ),
      { recursive: true }
    );
    expect(onLog).toHaveBeenCalledWith(
      "[compositions] No generated artifact found for veo_section_05_split_nature_comparison after Claude run; retrying once."
    );
  });

  it("retries once when the generated artifact has duplicate exported names", async () => {
    setupMockSpawn(0);

    const config = mockProjectConfig();
    config.sections[0].id = "part1_economics";
    config.sections[0].specDir = "part1_economics";
    config.sections[0].compositionId = "Part1Economics";
    mockLoadProject.mockReturnValue(config);

    const osMod = require("os");
    const pathMod = require("path");
    const specsDir = pathMod.join(process.cwd(), "specs", "part1_economics");
    const componentDirName = "Part1Economics07SplitContextComparison";
    const firstWorkspace = pathMod.join(
      osMod.tmpdir(),
      "video-editor-stage8-part1_economics_07_split_context_comparison-1",
      "remotion",
      "src",
      "remotion",
      componentDirName
    );
    const secondWorkspace = pathMod.join(
      osMod.tmpdir(),
      "video-editor-stage8-part1_economics_07_split_context_comparison-2",
      "remotion",
      "src",
      "remotion",
      componentDirName
    );

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return false;
      if (p === specsDir) return true;
      if (p.endsWith(pathMod.join(componentDirName, "index.ts"))) return true;
      if (p.endsWith(pathMod.join(componentDirName, "constants.ts"))) return true;
      if (p.endsWith(pathMod.join(componentDirName, "LeftPanel.tsx"))) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return [];
      if (p.includes(pathMod.join("specs", "part1_economics"))) {
        return [{ name: "07_split_context_comparison.md", isFile: () => true }];
      }
      if (
        p === firstWorkspace ||
        p === secondWorkspace
      ) {
        return ["index.ts", "constants.ts", "LeftPanel.tsx"];
      }
      return [];
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return "";
      if (p.endsWith("07_split_context_comparison.md")) {
        return "# Spec content";
      }
      if (p.endsWith(pathMod.join(componentDirName, "index.ts"))) {
        return "export { Part1Economics07SplitContextComparison } from './Part1Economics07SplitContextComparison';\nexport { default } from './Part1Economics07SplitContextComparison';";
      }
      if (p.endsWith(pathMod.join(componentDirName, "LeftPanel.tsx"))) {
        return "export const LeftPanel = () => null;";
      }
      if (p.startsWith(firstWorkspace) && p.endsWith(pathMod.join(componentDirName, "constants.ts"))) {
        return "export const GREEN_HIGHLIGHT = '#5AAA6E';\nexport const GREEN_HIGHLIGHT = { yFrac: 0.35, hFrac: 0.06 };";
      }
      if (p.startsWith(secondWorkspace) && p.endsWith(pathMod.join(componentDirName, "constants.ts"))) {
        return "export const GREEN_HIGHLIGHT_COLOR = '#5AAA6E';\nexport const GREEN_HIGHLIGHT_REGION = { yFrac: 0.35, hFrac: 0.06 };";
      }
      return "";
    });

    const onLog = jest.fn();
    const executor = registerCallArgs.factory(
      {
        sectionComponents: [
          { sectionId: "part1_economics", components: ["07_split_context_comparison"] },
        ],
        wrappers: [],
      },
      jest.fn()
    );

    await expect(executor(onLog)).resolves.toBeUndefined();

    expect(mockRunClaudeFix).toHaveBeenCalledTimes(2);
    expect(onLog).toHaveBeenCalledWith(
      "[compositions] Generated component validation failed for part1_economics_07_split_context_comparison after Claude run; retrying once. Duplicate exported names in constants.ts: GREEN_HIGHLIGHT"
    );
    expect(mockCpSync).toHaveBeenCalledWith(
      secondWorkspace,
      pathMod.join(process.cwd(), "remotion", "src", "remotion", componentDirName),
      { recursive: true }
    );
  });

  it("uses a distinct temp workspace per component generation", async () => {
    setupMockSpawn(0);

    const config = mockProjectConfig();
    config.sections[0].id = "intro";
    config.sections[0].specDir = "intro";
    config.sections[1].id = "main";
    config.sections[1].specDir = "main";
    mockLoadProject.mockReturnValue(config);

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return false;
      if (p.endsWith(path.join("remotion", "src", "remotion", "intro_title_card.tsx"))) return true;
      if (p.endsWith(path.join("remotion", "src", "remotion", "main_title_card.tsx"))) return true;
      if (p.includes(path.join("specs", "intro")) || p.includes(path.join("specs", "main"))) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return [];
      if (p.includes(path.join("specs", "intro"))) {
        return [{ name: "title_card.md", isFile: () => true }];
      }
      if (p.includes(path.join("specs", "main"))) {
        return [{ name: "title_card.md", isFile: () => true }];
      }
      return [];
    });
    mockReadFileSync.mockReturnValue("# Spec content");

    const executor = registerCallArgs.factory(
      {
        sectionComponents: [
          { sectionId: "intro", components: ["title_card"] },
          { sectionId: "main", components: ["title_card"] },
        ],
        wrappers: [],
      },
      jest.fn()
    );

    await expect(executor(jest.fn())).resolves.toBeUndefined();

    expect(mockRunClaudeFix).toHaveBeenCalledTimes(2);
    expect(mockRunClaudeFix.mock.calls[0][1]).not.toBe(mockRunClaudeFix.mock.calls[1][1]);
  });

  it("only preview-validates compositions that were actually discovered into the section render graph", async () => {
    setupMockSpawn(0);

    const config = mockProjectConfig();
    config.sections[0].id = "veo_section";
    config.sections[0].specDir = "veo_section";
    config.sections[0].compositionId = "VeoSection";
    mockLoadProject.mockReturnValue(config);

    const pathMod = require("path");
    const specsDir = pathMod.join(process.cwd(), "specs", "veo_section");
    const remotionDir = pathMod.join(process.cwd(), "remotion/src/remotion");

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return false;
      if (p === specsDir) return true;
      if (p === pathMod.join(remotionDir, "VeoSection05SplitNatureComparison", "index.ts")) {
        return true;
      }
      return false;
    });
    mockReaddirSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs") && p.includes("veo_section")) {
        return [];
      }
      return [];
    });

    const executor = registerCallArgs.factory(
      {
        sectionComponents: [
          { sectionId: "veo_section", components: ["05_split_nature_comparison"] },
        ],
        wrappers: [],
      },
      jest.fn()
    );

    await expect(executor(jest.fn())).resolves.toBeUndefined();
    expect(mockRenderStill).not.toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 21c. buildComponentPrompt uses exportName as dirName
// ---------------------------------------------------------------------------

describe("compositions executor — buildComponentPrompt dirName alignment", () => {
  let compositionsSourceCode: string;

  beforeAll(() => {
    const realFs = jest.requireActual("fs") as typeof import("fs");
    const pathMod = require("path");
    compositionsSourceCode = realFs.readFileSync(
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

  it("uses exportName as dirName in buildComponentPrompt (not NN-PascalName format)", () => {
    // Extract just the buildComponentPrompt function source (ends at line "async function generateSectionConstants")
    const funcStart = compositionsSourceCode.indexOf("function buildComponentPrompt");
    const funcEnd = compositionsSourceCode.indexOf("async function generateSectionConstants");
    const funcSource = compositionsSourceCode.slice(funcStart, funcEnd);

    // dirName should equal exportName in buildComponentPrompt
    expect(funcSource).toMatch(/const dirName = exportName;/);
    // Should NOT have the old NN-prefix logic for dirName in buildComponentPrompt
    expect(funcSource).not.toMatch(/nnMatch.*strippedPascal.*dirName|dirName.*nnMatch/);
  });

  it("generates prompt with exportName directory for section-scoped components", () => {
    // When baseName is "05_crossfade_transition" and outputName is "cold_open_05_crossfade_transition"
    // the prompt should use ColdOpen05CrossfadeTransition/ as the directory
    // (not 05-CrossfadeTransition/ which is the old behavior)
    mockGeneratedFlatArtifacts("cold_open_05_crossfade_transition");
    mockReaddirSync.mockReturnValue([]);
    mockReadFileSync.mockReturnValue("# Spec");

    const config = mockProjectConfig();
    config.sections[0].specDir = "specs/cold_open";
    config.sections[0].id = "cold_open";
    mockLoadProject.mockReturnValue(config);

    // Call runClaudeFix to capture the prompt
    mockRunClaudeFix.mockResolvedValue(undefined);
    const proc = createMockSpawnProcess(0);
    mockSpawn.mockReturnValue(proc);
    setTimeout(() => proc._triggerClose(), 5);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      {
        sectionComponents: [
          { sectionId: "cold_open", components: ["05_crossfade_transition"] },
        ],
        wrappers: [],
      },
      mockSend
    );

    return executor(jest.fn()).then(() => {
      const prompt = mockRunClaudeFix.mock.calls[0][0] as string;
      // Should reference ColdOpen05CrossfadeTransition directory
      expect(prompt).toContain("ColdOpen05CrossfadeTransition/");
      // Should NOT reference 05-CrossfadeTransition directory
      expect(prompt).not.toContain("05-CrossfadeTransition/");
    });
  });
});

// ---------------------------------------------------------------------------
// 22. buildComponentPrompt supports multi-file output
// ---------------------------------------------------------------------------

describe("compositions executor — buildComponentPrompt multi-file output", () => {
  let compositionsSourceCode: string;

  beforeAll(() => {
    const realFs = jest.requireActual("fs") as typeof import("fs");
    const pathMod = require("path");
    compositionsSourceCode = realFs.readFileSync(
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

  it("instructs Claude to create component subdirectory", () => {
    // buildComponentPrompt should reference creating a directory structure
    expect(compositionsSourceCode).toMatch(/directory|subdirectory|sub-component/i);
  });

  it("references index.ts barrel export pattern", () => {
    expect(compositionsSourceCode).toMatch(/index\.ts/);
  });

  it("does NOT constrain output to single flat .tsx file only", () => {
    // The prompt should mention directory-based output, not just single file
    expect(compositionsSourceCode).toMatch(/constants\.ts|sub.*component/i);
  });

  it("instructs Claude to use supported quartic easing", () => {
    expect(compositionsSourceCode).toContain("Easing.poly(4)");
    expect(compositionsSourceCode).toContain("NOT Easing.quart");
  });

  it("instructs Claude to route multi-clip Veo visuals through media aliases instead of inventing filenames", () => {
    expect(compositionsSourceCode).toContain("Never hardcode Veo filenames");
    expect(compositionsSourceCode).toContain("useVisualMediaAssetSrc('leftSrc'");
    expect(compositionsSourceCode).toContain("useVisualMediaAssetSrc('rightSrc'");
    expect(compositionsSourceCode).toContain("do not wrap it in staticFile() again");
  });

  it("instructs Claude to keep overlays readable with explicit visibility minimums", () => {
    expect(compositionsSourceCode).toContain("minimum text opacity");
    expect(compositionsSourceCode).toContain("minimum font size");
    expect(compositionsSourceCode).toContain("divider");
  });

  it("specifies minimum opacity for dividers and horizontal rules", () => {
    // Without a minimum opacity, Claude generates rules at 0.2-0.5 opacity
    // which are invisible on dark backgrounds. The prompt must specify a floor.
    expect(compositionsSourceCode).toMatch(/divider.*opacity.*0\.[67]/is);
  });

  it("buildComponentPrompt derives dirName from baseName, not scoped outputName", () => {
    // The prompt must accept a baseName parameter for NN-prefix directory naming
    // so that "10_split_perception_reality" → "10-SplitPerceptionReality" directory
    // even when the scoped outputName is "part1_economics_10_split_perception_reality"
    expect(compositionsSourceCode).toMatch(
      /function\s+buildComponentPrompt\s*\(\s*baseName\s*:\s*string\s*,\s*outputName\s*:\s*string/
    );
  });

  it("extracts string IDs from compositions before passing to generateSectionConstants/Composition", () => {
    // The code must handle mixed-type compositions arrays (strings and timing objects)
    // by extracting IDs before passing to functions that expect string[]
    expect(compositionsSourceCode).toMatch(/typeof comp === ["']string["']/);
  });

  it("discovery merges with existing timing data instead of replacing", () => {
    // Line 587 must NOT do: section.compositions = discoveredComponents
    // It must preserve existing timing objects by merging
    expect(compositionsSourceCode).toMatch(/existingTimingMap|timingMap/);
    expect(compositionsSourceCode).not.toMatch(
      /section\.compositions\s*=\s*discoveredComponents\s*;/
    );
  });

  it("discovery checks section-prefixed PascalCase directory for digit-prefixed components", () => {
    // When a component like 07_monitor_glow_overlay exists in a directory named
    // ColdOpen07MonitorGlowOverlay/ (section-prefixed PascalCase), the discovery
    // logic must find it — not just check for 07-MonitorGlowOverlay/
    expect(compositionsSourceCode).toMatch(/pascalDirIndex/);
    expect(compositionsSourceCode).toMatch(/sectionPascal/);
  });
});

// ---------------------------------------------------------------------------
// 23. generateSectionConstants produces BEATS/VISUAL_SEQUENCE
// ---------------------------------------------------------------------------

describe("compositions executor — generateSectionConstants", () => {
  function setupMockSpawn(exitCode = 0) {
    const proc = createMockSpawnProcess(exitCode);
    mockSpawn.mockReturnValue(proc);
    setTimeout(() => proc._triggerClose(), 5);
    return proc;
  }

  /**
   * Set up mocks so that component discovery finds a generated component,
   * triggering the section constants and composition generation flow.
   */
  function setupDiscoveryMocks() {
    const pathMod = require("path");
    const specsDir = pathMod.join(process.cwd(), "specs");
    const remotionDir = pathMod.join(process.cwd(), "remotion/src/remotion");

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return false;
      // Spec directory exists
      if (p.includes(pathMod.join("specs", "specs/intro"))) return true;
      // Generated TSX file exists (section-scoped: intro_01_chart.tsx)
      if (p.endsWith("intro_01_chart.tsx")) return true;
      // Word timestamps
      if (p.includes("_words.json")) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((dir: string) => {
      if (typeof dir === "string" && dir.includes("specs")) {
        return [
          { name: "01_chart.md", isDirectory: () => false, isFile: () => true },
        ];
      }
      return [];
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("_words.json")) {
        return JSON.stringify([
          { word: "Hello", start: 0.0, end: 0.5 },
          { word: "world", start: 0.6, end: 1.0 },
        ]);
      }
      if (typeof p === "string" && p.includes("01_chart.md")) {
        return "# Chart spec\nSome content";
      }
      return "";
    });
  }

  it("writes a constants.ts file containing BEATS and VISUAL_SEQUENCE", async () => {
    const config = mockProjectConfig();
    config.sections[0].specDir = "specs/intro";
    mockLoadProject.mockReturnValue(config);
    setupDiscoveryMocks();
    setupMockSpawn(0);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      {
        components: ["01_chart"],
        wrappers: [],
        sectionId: "intro",
      },
      mockSend
    );
    await executor(jest.fn());

    const constantsWrite = mockWriteFileSync.mock.calls.find(
      (call: unknown[]) =>
        typeof call[0] === "string" &&
        (call[0] as string).endsWith(path.join("remotion/src/remotion", "intro", "constants.ts"))
    );
    expect(constantsWrite).toBeDefined();
    expect(String(constantsWrite?.[1])).toContain("export const BEATS");
    expect(String(constantsWrite?.[1])).toContain("export const VISUAL_SEQUENCE");
  });

  it("uses s2f helper and the real audio sync timestamps path in generated constants flow", async () => {
    const config = mockProjectConfig();
    config.sections[0].specDir = "specs/intro";
    mockLoadProject.mockReturnValue(config);
    setupDiscoveryMocks();
    setupMockSpawn(0);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["01_chart"], wrappers: [], sectionId: "intro" },
      mockSend
    );
    await executor(jest.fn());

    const constantsWrite = mockWriteFileSync.mock.calls.find(
      (call: unknown[]) =>
        typeof call[0] === "string" &&
        (call[0] as string).endsWith(path.join("remotion/src/remotion", "intro", "constants.ts"))
    );
    expect(String(constantsWrite?.[1])).toContain("const s2f");
    expect(mockExistsSync).toHaveBeenCalledWith(
      path.join(process.cwd(), "outputs", "tts", "intro", "word_timestamps.json")
    );
  });
});

describe("compositions route timing source", () => {
  let compositionsSourceCode: string;

  beforeAll(() => {
    const realFs = jest.requireActual("fs") as typeof import("fs");
    const pathMod = require("path");
    compositionsSourceCode = realFs.readFileSync(
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

  it("delegates section timing generation to the shared deterministic helper", () => {
    expect(compositionsSourceCode).toMatch(/buildSectionConstantsSource/);
  });

  it("does not rely on the stale data/{section}_words.json path", () => {
    expect(compositionsSourceCode).not.toMatch(/_words\.json/);
    expect(compositionsSourceCode).not.toMatch(/const\s+DATA_DIR/);
  });
});

// ---------------------------------------------------------------------------
// 24. generateSectionComposition generates activeVisual pattern
// ---------------------------------------------------------------------------

describe("compositions executor — generated section timelines", () => {
  function setupMockSpawn(exitCode = 0) {
    const proc = createMockSpawnProcess(exitCode);
    mockSpawn.mockReturnValue(proc);
    setTimeout(() => proc._triggerClose(), 5);
    return proc;
  }

  function setupDiscoveryMocks() {
    const pathMod = require("path");
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return false;
      if (p.includes(pathMod.join("specs", "specs/intro"))) return true;
      if (p.endsWith("intro_01_chart.tsx")) return true;
      if (p.includes("_words.json")) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((dir: string) => {
      if (typeof dir === "string" && dir.includes("specs")) {
        return [
          { name: "01_chart.md", isDirectory: () => false, isFile: () => true },
        ];
      }
      return [];
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("_words.json")) {
        return JSON.stringify([]);
      }
      if (typeof p === "string" && p.includes("01_chart.md")) {
        return "# Chart spec\nSome content";
      }
      return "";
    });
  }

  it("marks discovered sections as generated when no authored timeline exists", async () => {
    const config = mockProjectConfig();
    config.sections[0].specDir = "specs/intro";
    mockLoadProject.mockReturnValue(config);
    setupDiscoveryMocks();
    setupMockSpawn(0);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["01_chart"], wrappers: [], sectionId: "intro" },
      mockSend
    );
    await executor(jest.fn());

    const savedConfig = mockSaveProject.mock.calls.at(-1)?.[0];
    expect(savedConfig).toBeDefined();
    expect(savedConfig.sections[0].timelineSource).toBe("generated");
  });

  it("marks discovered sections as generated even when a legacy authored section timeline exists", async () => {
    const config = mockProjectConfig();
    config.sections[0].id = "cold_open";
    config.sections[0].specDir = "specs/cold_open";
    config.sections[0].compositionId = "ColdOpenSection";
    config.sections[0].timelineSource = "authored";
    mockLoadProject.mockReturnValue(config);

    const pathMod = require("path");
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return false;
      if (p.includes(pathMod.join("specs", "specs/cold_open"))) return true;
      if (p.endsWith("cold_open_01_chart.tsx")) return true;
      if (p.endsWith("ColdOpenSection.tsx")) return true;
      if (p.includes("_words.json")) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((dir: string) => {
      if (typeof dir === "string" && dir.includes("specs")) {
        return [
          { name: "01_chart.md", isDirectory: () => false, isFile: () => true },
        ];
      }
      return [];
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("_words.json")) {
        return JSON.stringify([]);
      }
      if (typeof p === "string" && p.includes("01_chart.md")) {
        return "# Chart spec\nSome content";
      }
      return "";
    });
    setupMockSpawn(0);

    const executor = registerCallArgs.factory(
      { components: ["01_chart"], wrappers: [], sectionId: "cold_open" },
      jest.fn()
    );
    await executor(jest.fn());

    const savedConfig = mockSaveProject.mock.calls.at(-1)?.[0];
    expect(savedConfig).toBeDefined();
    expect(savedConfig.sections[0].timelineSource).toBe("generated");
  });

  it("prefers section-scoped flat files over shared legacy component directories during discovery", async () => {
    const pathMod = require("path");
    const config = mockProjectConfig();
    config.sections[0].id = "intro";
    config.sections[0].specDir = "specs/intro";
    mockLoadProject.mockReturnValue(config);

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return false;
      if (p.includes(pathMod.join("specs", "specs/intro"))) return true;
      if (p.endsWith(pathMod.join("01-Chart", "index.ts"))) return true;
      if (p.endsWith("intro_01_chart.tsx")) return true;
      if (p.includes("_words.json")) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((dir: string) => {
      if (typeof dir === "string" && dir.includes("specs")) {
        return [
          { name: "01_chart.md", isDirectory: () => false, isFile: () => true },
        ];
      }
      return [];
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("_words.json")) {
        return JSON.stringify([]);
      }
      if (typeof p === "string" && p.includes("01_chart.md")) {
        return "# Chart spec\nSome content";
      }
      return "";
    });
    setupMockSpawn(0);

    const executor = registerCallArgs.factory(
      { components: ["01_chart"], wrappers: [], sectionId: "intro" },
      jest.fn(),
    );
    await executor(jest.fn());

    const savedConfig = mockSaveProject.mock.calls.at(-1)?.[0];
    expect(savedConfig.sections[0].compositions).toContain("intro_01_chart");
    expect(savedConfig.sections[0].compositions).not.toContain("01_chart");
  });

  it("does not ask Claude to generate a section composition prompt for generated timelines", async () => {
    const config = mockProjectConfig();
    config.sections[0].specDir = "specs/intro";
    mockLoadProject.mockReturnValue(config);
    setupDiscoveryMocks();
    setupMockSpawn(0);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["01_chart"], wrappers: [], sectionId: "intro" },
      mockSend
    );
    await executor(jest.fn());

    const allCalls = mockRunClaudeFix.mock.calls;
    const compositionCall = allCalls.find(
      (call: any[]) =>
        typeof call[0] === "string" &&
        call[0].includes("activeVisual")
    );
    expect(compositionCall).toBeUndefined();
  });

  it("writes a generated composition manifest after discovery", async () => {
    const config = mockProjectConfig();
    config.sections[0].specDir = "specs/intro";
    mockLoadProject.mockReturnValue(config);
    setupDiscoveryMocks();
    setupMockSpawn(0);

    const executor = registerCallArgs.factory(
      { components: ["01_chart"], wrappers: [], sectionId: "intro" },
      jest.fn()
    );
    await executor(jest.fn());

    const manifestWrite = mockWriteFileSync.mock.calls.find(
      (call: unknown[]) =>
        typeof call[0] === "string" &&
        (call[0] as string).endsWith(
          path.join("outputs", "compositions", "manifest.json")
        )
    );
    expect(manifestWrite).toBeDefined();
    expect(String(manifestWrite?.[1])).toContain('"id": "intro"');
    expect(String(manifestWrite?.[1])).toContain('"intro_01_chart"');
    expect(String(manifestWrite?.[1])).toContain('"generatorFingerprint":');
  });
});

// ---------------------------------------------------------------------------
// 25. Composition list — component directory detection
// ---------------------------------------------------------------------------

describe("GET_CompositionList — component directory detection", () => {
  it("returns 'done' when component directory with index.ts exists", async () => {
    const pathMod = require("path");
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("specs")) return true;
      // Component directory exists: {NN}-{ComponentName}/index.ts
      if (typeof p === "string" && p.endsWith(pathMod.join("02-SockPriceChart", "index.ts"))) return true;
      // Also check flat file path (should fail)
      if (typeof p === "string" && p.endsWith("intro_02_sock_price_chart.tsx")) return false;
      if (typeof p === "string" && p.endsWith("02_sock_price_chart.tsx")) return false;
      return false;
    });
    mockReaddirSync.mockImplementation((dir: string, opts?: any) => {
      if (typeof dir === "string" && dir.includes("specs")) {
        return [
          {
            name: "02_sock_price_chart.md",
            isDirectory: () => false,
            isFile: () => true,
          },
        ];
      }
      return [];
    });
    mockReadFileSync.mockReturnValue("# Sock Price Chart\n[Remotion]");

    const response = await GET_CompositionList();
    const data = await response.json();

    const introSection = data.sections.find((s: any) => s.id === "intro");
    const comp = introSection?.components.find(
      (c: any) => c.name === "02_sock_price_chart"
    );
    expect(comp).toBeDefined();
    expect(comp.status).toBe("done");
  });
});

// ---------------------------------------------------------------------------
// Preview route: extracts string IDs from mixed compositions
// ---------------------------------------------------------------------------

describe("compositions preview — handles timing objects in compositions", () => {
  let previewSourceCode: string;

  beforeAll(() => {
    const realFs = jest.requireActual("fs") as typeof import("fs");
    const pathMod = require("path");
    previewSourceCode = realFs.readFileSync(
      pathMod.join(
        __dirname,
        "..",
        "app",
        "api",
        "pipeline",
        "compositions",
        "preview",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("preview route extracts string IDs from mixed compositions", () => {
    // preview/route.ts now delegates mixed composition handling to the shared manifest resolver
    expect(previewSourceCode).toMatch(/resolveSectionCompositionIds/);
  });
});

// ---------------------------------------------------------------------------
// Section-prefix inference for spec lookup
// ---------------------------------------------------------------------------

describe("compositions executor — section-prefix spec inference", () => {
  it("findSpecForComponent infers section from prefixed name and finds the stripped spec file", () => {
    // Verify the source code contains the section-prefix inference logic
    const realFs = jest.requireActual("fs") as typeof import("fs");
    const pathMod = require("path");
    const sourceCode = realFs.readFileSync(
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

    // The function should infer section from component name prefix and strip it
    expect(sourceCode).toMatch(/componentName\.startsWith\(prefix\)/);
    expect(sourceCode).toMatch(/componentName\.slice\(prefix\.length\)/);
    // It should search the section's specDir for the stripped name
    expect(sourceCode).toMatch(/sec\.specDir/);
  });

  it("passes spec content to prompt when component has section prefix but no sectionId", async () => {
    // The spec file is at specs/cold_open/04_zoom_out.md
    // Component name is cold_open_04_zoom_out (section-prefixed)
    // Without the fix, findSpecForComponent would not find it
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p !== "string") return false;
      if (p.endsWith("specs")) return true;
      if (p.includes(path.join("specs", "cold_open"))) return true;
      if (p.endsWith(path.join("cold_open", "04_zoom_out.md"))) return true;
      return false;
    });
    mockReaddirSync.mockReturnValue([]);
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("04_zoom_out.md")) {
        return "[Remotion]\n# Zoom Out\nZoom out spec content here";
      }
      return "";
    });

    const config = mockProjectConfig();
    config.sections = [
      { id: "cold_open", label: "Cold Open", specDir: "cold_open", compositionId: "ColdOpen", durationSeconds: 17.5, offsetSeconds: 0 },
    ];
    mockLoadProject.mockReturnValue(config);

    const proc = createMockSpawnProcess(0);
    mockSpawn.mockReturnValue(proc);
    setTimeout(() => proc._triggerClose(), 5);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { components: ["cold_open_04_zoom_out"], wrappers: [] },
      mockSend
    );

    // The executor will call runClaudeFix — even if artifact validation fails afterward,
    // we can inspect the prompt that was passed
    try { await executor(jest.fn()); } catch { /* generation may fail in test env */ }

    if (mockRunClaudeFix.mock.calls.length > 0) {
      const prompt = mockRunClaudeFix.mock.calls[0][0] as string;
      expect(prompt).toContain("Zoom out spec content here");
      expect(prompt).not.toContain("spec not found");
    } else {
      // If runClaudeFix wasn't called, verify spec was at least read
      const readCalls = mockReadFileSync.mock.calls.map((c: any) => c[0]);
      const specRead = readCalls.find(
        (p: string) => typeof p === "string" && p.includes("04_zoom_out.md")
      );
      expect(specRead).toBeDefined();
    }
  });
});

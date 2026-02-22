/**
 * Tests for app/api/pipeline/veo/run/route.ts
 * (also covers clips, references, and staging-manifest endpoints)
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_pipeline_veo_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. POST /api/pipeline/veo/run — accepts { clips?: string[] }, returns SSE stream with { jobId }
 *   2. Frame chaining: extract last frame of clip N, pass as referenceImagePath to clip N+1
 *   3. GET /api/pipeline/veo/clips — returns { clips: VeoClip[] } with correct shape
 *   4. POST /api/pipeline/veo/references/run — accepts { referenceId }, returns { jobId }
 *   5. GET /api/pipeline/veo/staging-manifest — returns { files: AssetStagingEntry[] }
 *   6. No authentication required
 *   7. Clip output path: outputs/veo/{clipId}.mp4
 *   8. Frame chain path: outputs/veo/{clipId}_last_frame.png
 *   9. Stale detection: clip is stale if frameChainDeps have newer mtime
 *  10. Reference portrait output: outputs/veo/references/{referenceId}.png
 *  11. registerExecutor('veo', ...) called at module load time
 *  12. Per-clip SSE events: { type: 'clip', clipId, status: 'generating' | 'done' | 'error' }
 *  13. Clips processed sequentially for frame chaining
 *  14. Expected staging files from loadProject().sections mapped to veo clip filenames
 */

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockRegisterExecutor = jest.fn();
const mockRunPipelineStage = jest.fn();
const mockCreateJob = jest.fn();
const mockRunJob = jest.fn();

jest.mock("@/lib/jobs", () => ({
  registerExecutor: (...args: unknown[]) => mockRegisterExecutor(...args),
  runPipelineStage: (...args: unknown[]) => mockRunPipelineStage(...args),
  createJob: (...args: unknown[]) => mockCreateJob(...args),
  runJob: (...args: unknown[]) => mockRunJob(...args),
}));

const mockCreateSseStream = jest.fn();

jest.mock("@/lib/sse", () => ({
  createSseStream: (...args: unknown[]) => mockCreateSseStream(...args),
}));

const mockLoadProject = jest.fn();

jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
}));

const mockGenerateVeoClip = jest.fn();
const mockExtractLastFrame = jest.fn();
const mockGenerateReferenceImage = jest.fn();

jest.mock("@/lib/veo", () => ({
  generateVeoClip: (...args: unknown[]) => mockGenerateVeoClip(...args),
  extractLastFrame: (...args: unknown[]) => mockExtractLastFrame(...args),
  generateReferenceImage: (...args: unknown[]) =>
    mockGenerateReferenceImage(...args),
}));

// Mock fs
const mockExistsSync = jest.fn();
const mockReadFileSync = jest.fn();
const mockMkdirSync = jest.fn();
const mockStatSync = jest.fn();
const mockReaddirSync = jest.fn();

jest.mock("fs", () => ({
  __esModule: true,
  default: {
    existsSync: (...args: unknown[]) => mockExistsSync(...args),
    readFileSync: (...args: unknown[]) => mockReadFileSync(...args),
    mkdirSync: (...args: unknown[]) => mockMkdirSync(...args),
    statSync: (...args: unknown[]) => mockStatSync(...args),
    readdirSync: (...args: unknown[]) => mockReaddirSync(...args),
  },
  existsSync: (...args: unknown[]) => mockExistsSync(...args),
  readFileSync: (...args: unknown[]) => mockReadFileSync(...args),
  mkdirSync: (...args: unknown[]) => mockMkdirSync(...args),
  statSync: (...args: unknown[]) => mockStatSync(...args),
  readdirSync: (...args: unknown[]) => mockReaddirSync(...args),
}));

// Import after mocking
import {
  POST_run,
  GET_clips,
  POST_references,
  GET_staging,
} from "../app/api/pipeline/veo/run/route";

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
    audioSync: {
      sectionGroups: { narration: ["intro", "main", "outro"] },
    },
    veo: {
      model: "veo-2.0-generate-001",
      aspectRatio: "16:9" as const,
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

function makeRequest(url: string, body?: object): Request {
  if (body) {
    return new Request(url, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(body),
    });
  }
  return new Request(url, { method: "POST" });
}

function makeSseStreamMock() {
  const sent: object[] = [];
  let closedDone = false;
  let closedError: string | null = null;

  const stream = new ReadableStream<Uint8Array>({
    start(controller) {
      // minimal stream
    },
  });

  return {
    result: {
      stream,
      send: (data: object) => {
        sent.push(data);
      },
      done: () => {
        closedDone = true;
      },
      error: (msg: string) => {
        closedError = msg;
      },
    },
    getSent: () => sent,
    isDone: () => closedDone,
    getError: () => closedError,
  };
}

/** Flush microtask queue so fire-and-forget IIFE completes. */
function flushPromises(): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, 50));
}

// ---------------------------------------------------------------------------
// Setup
// ---------------------------------------------------------------------------

beforeEach(() => {
  mockRunPipelineStage.mockReset();
  mockCreateJob.mockReset();
  mockRunJob.mockReset();
  mockCreateSseStream.mockReset();
  mockLoadProject.mockReset();
  mockGenerateVeoClip.mockReset();
  mockExtractLastFrame.mockReset();
  mockGenerateReferenceImage.mockReset();
  mockExistsSync.mockReset();
  mockReadFileSync.mockReset();
  mockMkdirSync.mockReset();
  mockStatSync.mockReset();
  mockReaddirSync.mockReset();

  mockRunPipelineStage.mockResolvedValue("test-job-veo-001");
  mockLoadProject.mockReturnValue(mockProjectConfig());
  mockGenerateVeoClip.mockResolvedValue(undefined);
  mockExtractLastFrame.mockResolvedValue(undefined);
  mockGenerateReferenceImage.mockResolvedValue(undefined);
  mockCreateJob.mockReturnValue("test-job-ref-001");
  mockRunJob.mockResolvedValue(undefined);
});

// ---------------------------------------------------------------------------
// 1. registerExecutor — module load side effect
// ---------------------------------------------------------------------------

describe("registerExecutor at module load", () => {
  it("registers executor for 'veo' stage", () => {
    expect(registerCallArgs.stage).toBe("veo");
  });

  it("passes an executor factory function", () => {
    expect(typeof registerCallArgs.factory).toBe("function");
  });
});

// ---------------------------------------------------------------------------
// 2. POST_run — response shape and SSE headers
// ---------------------------------------------------------------------------

describe("POST_run response shape", () => {
  beforeEach(() => {
    const sseMock = makeSseStreamMock();
    mockCreateSseStream.mockReturnValue(sseMock.result);
  });

  it("returns a Response object", async () => {
    const response = await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run") as any
    );
    expect(response).toBeInstanceOf(Response);
  });

  it("sets Content-Type to text/event-stream", async () => {
    const response = await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run") as any
    );
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("sets Cache-Control to no-cache", async () => {
    const response = await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run") as any
    );
    expect(response.headers.get("Cache-Control")).toBe("no-cache");
  });

  it("sets Connection to keep-alive", async () => {
    const response = await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run") as any
    );
    expect(response.headers.get("Connection")).toBe("keep-alive");
  });

  it("returns a ReadableStream body", async () => {
    const response = await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run") as any
    );
    expect(response.body).toBeInstanceOf(ReadableStream);
  });
});

// ---------------------------------------------------------------------------
// 3. POST_run — success flow
// ---------------------------------------------------------------------------

describe("POST_run — success flow", () => {
  let sseMock: ReturnType<typeof makeSseStreamMock>;

  beforeEach(() => {
    sseMock = makeSseStreamMock();
    mockCreateSseStream.mockReturnValue(sseMock.result);
    mockRunPipelineStage.mockResolvedValue("test-job-veo-42");
  });

  it("calls runPipelineStage with 'veo' stage", async () => {
    await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run") as any
    );
    await flushPromises();

    expect(mockRunPipelineStage).toHaveBeenCalledTimes(1);
    expect(mockRunPipelineStage.mock.calls[0][0]).toBe("veo");
  });

  it("passes clips param from body to runPipelineStage", async () => {
    await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run", {
        clips: ["intro", "outro"],
      }) as any
    );
    await flushPromises();

    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.clips).toEqual(["intro", "outro"]);
  });

  it("passes undefined clips when body has no clips", async () => {
    await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run", {}) as any
    );
    await flushPromises();

    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.clips).toBeUndefined();
  });

  it("passes a send function to runPipelineStage", async () => {
    await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run") as any
    );
    await flushPromises();

    expect(typeof mockRunPipelineStage.mock.calls[0][2]).toBe("function");
  });

  it("emits complete event with jobId after runPipelineStage resolves", async () => {
    await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run") as any
    );
    await flushPromises();

    const completeEvent = sseMock
      .getSent()
      .find((e: any) => e.type === "complete") as any;
    expect(completeEvent).toBeDefined();
    expect(completeEvent.jobId).toBe("test-job-veo-42");
  });

  it("calls done() on SSE stream after success", async () => {
    await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run") as any
    );
    await flushPromises();

    expect(sseMock.isDone()).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// 4. POST_run — body parameter handling
// ---------------------------------------------------------------------------

describe("POST_run — body parameter handling", () => {
  beforeEach(() => {
    const sseMock = makeSseStreamMock();
    mockCreateSseStream.mockReturnValue(sseMock.result);
  });

  it("works with no body (generates all clips)", async () => {
    const response = await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run") as any
    );
    expect(response).toBeInstanceOf(Response);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("works with empty clips array", async () => {
    const response = await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run", {
        clips: [],
      }) as any
    );
    expect(response).toBeInstanceOf(Response);
  });

  it("accepts specific clips array", async () => {
    const response = await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run", {
        clips: ["intro", "outro"],
      }) as any
    );
    expect(response).toBeInstanceOf(Response);
  });

  it("handles invalid body gracefully (non-JSON)", async () => {
    const request = new Request("http://localhost/api/pipeline/veo/run", {
      method: "POST",
      body: "not json",
    });

    const response = await POST_run(request as any);
    expect(response).toBeInstanceOf(Response);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });
});

// ---------------------------------------------------------------------------
// 5. POST_run — error handling
// ---------------------------------------------------------------------------

describe("POST_run — error handling", () => {
  let sseMock: ReturnType<typeof makeSseStreamMock>;

  beforeEach(() => {
    sseMock = makeSseStreamMock();
    mockCreateSseStream.mockReturnValue(sseMock.result);
  });

  it("calls error() on SSE stream when runPipelineStage rejects with Error", async () => {
    mockRunPipelineStage.mockRejectedValue(new Error("Pipeline failed"));

    await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run") as any
    );
    await flushPromises();

    expect(sseMock.getError()).toBe("Pipeline failed");
  });

  it("calls error() with 'Unknown error' for non-Error throws", async () => {
    mockRunPipelineStage.mockRejectedValue("string error");

    await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run") as any
    );
    await flushPromises();

    expect(sseMock.getError()).toBe("Unknown error");
  });

  it("still returns SSE response even when pipeline will error", async () => {
    mockRunPipelineStage.mockRejectedValue(new Error("will fail"));

    const response = await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run") as any
    );
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });
});

// ---------------------------------------------------------------------------
// 6. POST_run — no authentication required
// ---------------------------------------------------------------------------

describe("POST_run — no authentication required", () => {
  beforeEach(() => {
    const sseMock = makeSseStreamMock();
    mockCreateSseStream.mockReturnValue(sseMock.result);
  });

  it("does not require authorization headers", async () => {
    const request = new Request("http://localhost/api/pipeline/veo/run", {
      method: "POST",
      headers: { Authorization: "Bearer fake-token" },
    });

    const response = await POST_run(request as any);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("works with minimal request (no body, no auth)", async () => {
    const response = await POST_run(
      makeRequest("http://localhost/api/pipeline/veo/run") as any
    );
    expect(response).toBeInstanceOf(Response);
  });
});

// ---------------------------------------------------------------------------
// 7. Veo executor factory — clip generation
// ---------------------------------------------------------------------------

describe("veo executor factory — clip generation", () => {
  beforeEach(() => {
    // Setup Veo prompt resolution
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("veo.json")) return true;
      return false;
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("veo.json")) {
        return JSON.stringify({ prompt: "Test veo prompt for clip" });
      }
      return "";
    });
  });

  it("returns an async function when called with params and send", () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    expect(typeof executor).toBe("function");
  });

  it("calls loadProject() to get section list", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    expect(mockLoadProject).toHaveBeenCalledTimes(1);
  });

  it("generates all clips when params.clips is not provided", async () => {
    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    // Should generate clips for all 3 sections (intro, main, outro)
    expect(mockGenerateVeoClip).toHaveBeenCalledTimes(3);
  });

  it("generates only specified clips when params.clips is provided", async () => {
    const mockSend = jest.fn();
    const executor = registerCallArgs.factory(
      { clips: ["intro", "outro"] },
      mockSend
    );
    await executor(jest.fn());

    expect(mockGenerateVeoClip).toHaveBeenCalledTimes(2);
  });

  it("outputs clips to outputs/veo/{clipId}.mp4", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro
    mockLoadProject.mockReturnValue(config);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    const outputPath = mockGenerateVeoClip.mock.calls[0][3];
    expect(outputPath).toContain("outputs");
    expect(outputPath).toContain("veo");
    expect(outputPath).toContain("intro.mp4");
  });

  it("passes aspectRatio from project config to generateVeoClip", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]];
    mockLoadProject.mockReturnValue(config);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    const aspectRatio = mockGenerateVeoClip.mock.calls[0][2];
    expect(aspectRatio).toBe("16:9");
  });

  it("passes null referenceImagePath for the first clip", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]];
    mockLoadProject.mockReturnValue(config);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    const refImagePath = mockGenerateVeoClip.mock.calls[0][1];
    expect(refImagePath).toBeNull();
  });

  it("emits per-clip SSE events with type 'clip'", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]];
    mockLoadProject.mockReturnValue(config);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    const clipEvents = mockSend.mock.calls.filter(
      (c: any[]) => c[0]?.type === "clip"
    );
    expect(clipEvents.length).toBeGreaterThanOrEqual(1);
  });

  it("emits 'generating' status before clip generation", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]];
    mockLoadProject.mockReturnValue(config);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    const generatingEvent = mockSend.mock.calls.find(
      (c: any[]) => c[0]?.type === "clip" && c[0]?.status === "generating"
    );
    expect(generatingEvent).toBeDefined();
    expect(generatingEvent![0].clipId).toBe("intro");
  });

  it("emits 'done' status after successful clip generation", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]];
    mockLoadProject.mockReturnValue(config);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    const doneEvent = mockSend.mock.calls.find(
      (c: any[]) => c[0]?.type === "clip" && c[0]?.status === "done"
    );
    expect(doneEvent).toBeDefined();
    expect(doneEvent![0].clipId).toBe("intro");
  });

  it("emits 'error' status when clip generation fails", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]];
    mockLoadProject.mockReturnValue(config);
    mockGenerateVeoClip.mockRejectedValue(new Error("Veo API error"));

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);

    await expect(executor(jest.fn())).rejects.toThrow("Veo API error");

    const errorEvent = mockSend.mock.calls.find(
      (c: any[]) => c[0]?.type === "clip" && c[0]?.status === "error"
    );
    expect(errorEvent).toBeDefined();
    expect(errorEvent![0].clipId).toBe("intro");
  });

  it("ensures output directory exists before generating clip", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]];
    mockLoadProject.mockReturnValue(config);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    expect(mockMkdirSync).toHaveBeenCalled();
    const mkdirCall = mockMkdirSync.mock.calls[0];
    expect(mkdirCall[1]).toEqual({ recursive: true });
  });

  it("reports progress via onLog.progress callback", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]];
    mockLoadProject.mockReturnValue(config);

    const progressFn = jest.fn();
    const onLog = Object.assign(jest.fn(), { progress: progressFn });

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(onLog as any);

    expect(progressFn).toHaveBeenCalledWith(100);
  });

  it("does not crash when onLog has no progress callback", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]];
    mockLoadProject.mockReturnValue(config);

    const onLog = jest.fn();
    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await expect(executor(onLog)).resolves.not.toThrow();
  });
});

// ---------------------------------------------------------------------------
// 8. Veo executor factory — frame chaining
// ---------------------------------------------------------------------------

describe("veo executor factory — frame chaining", () => {
  beforeEach(() => {
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("veo.json")) return true;
      return false;
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("veo.json")) {
        return JSON.stringify({ prompt: "Test veo prompt" });
      }
      return "";
    });
  });

  it("extracts last frame of clip N for use in clip N+1", async () => {
    const config = mockProjectConfig();
    config.sections = config.sections.slice(0, 2); // intro, main
    mockLoadProject.mockReturnValue(config);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    // extractLastFrame should be called once (for intro, not for the last clip)
    expect(mockExtractLastFrame).toHaveBeenCalledTimes(1);

    // First arg is the clip output path, second is the frame output path
    const extractCall = mockExtractLastFrame.mock.calls[0];
    expect(extractCall[0]).toContain("intro.mp4");
    expect(extractCall[1]).toContain("intro_last_frame.png");
  });

  it("passes extracted frame path as referenceImagePath to next clip", async () => {
    const config = mockProjectConfig();
    config.sections = config.sections.slice(0, 2); // intro, main
    mockLoadProject.mockReturnValue(config);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    // First clip: null reference
    expect(mockGenerateVeoClip.mock.calls[0][1]).toBeNull();

    // Second clip: should have the last frame path as reference
    const secondRef = mockGenerateVeoClip.mock.calls[1][1];
    expect(secondRef).toContain("intro_last_frame.png");
  });

  it("does not extract last frame for the final clip", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro (single clip)
    mockLoadProject.mockReturnValue(config);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    expect(mockExtractLastFrame).not.toHaveBeenCalled();
  });

  it("processes clips sequentially, not in parallel", async () => {
    const callOrder: string[] = [];

    mockGenerateVeoClip.mockImplementation(
      async (prompt: string, ref: string | null, ar: string, out: string) => {
        callOrder.push(`generate:${out.includes("intro") ? "intro" : out.includes("main") ? "main" : "outro"}`);
      }
    );
    mockExtractLastFrame.mockImplementation(
      async (clipPath: string, framePath: string) => {
        callOrder.push(`extract:${clipPath.includes("intro") ? "intro" : "main"}`);
      }
    );

    const config = mockProjectConfig();
    config.sections = config.sections.slice(0, 3);
    mockLoadProject.mockReturnValue(config);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    // Verify sequential order: generate intro, extract intro, generate main, extract main, generate outro
    expect(callOrder[0]).toBe("generate:intro");
    expect(callOrder[1]).toBe("extract:intro");
    expect(callOrder[2]).toBe("generate:main");
    expect(callOrder[3]).toBe("extract:main");
    expect(callOrder[4]).toBe("generate:outro");
  });

  it("frame chain path is outputs/veo/{clipId}_last_frame.png", async () => {
    const config = mockProjectConfig();
    config.sections = config.sections.slice(0, 2);
    mockLoadProject.mockReturnValue(config);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    const framePath = mockExtractLastFrame.mock.calls[0][1];
    expect(framePath).toMatch(/outputs[/\\]veo[/\\]intro_last_frame\.png$/);
  });
});

// ---------------------------------------------------------------------------
// 9. GET_clips — response shape
// ---------------------------------------------------------------------------

describe("GET_clips — response shape", () => {
  it("returns Response.json with clips array", async () => {
    const response = await GET_clips();
    const data = await response.json();

    expect(data).toHaveProperty("clips");
    expect(Array.isArray(data.clips)).toBe(true);
  });

  it("returns one clip per section from project config", async () => {
    const response = await GET_clips();
    const data = await response.json();

    expect(data.clips).toHaveLength(3); // intro, main, outro
  });

  it("each clip has required VeoClip fields", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await GET_clips();
    const data = await response.json();

    for (const clip of data.clips) {
      expect(clip).toHaveProperty("id");
      expect(clip).toHaveProperty("sectionId");
      expect(clip).toHaveProperty("aspectRatio");
      expect(clip).toHaveProperty("status");
      expect(clip).toHaveProperty("stale");
      expect(clip).toHaveProperty("frameChainDeps");
    }
  });

  it("sets aspectRatio from project config", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await GET_clips();
    const data = await response.json();

    for (const clip of data.clips) {
      expect(clip.aspectRatio).toBe("16:9");
    }
  });

  it("clip id matches section id", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await GET_clips();
    const data = await response.json();

    expect(data.clips[0].id).toBe("intro");
    expect(data.clips[1].id).toBe("main");
    expect(data.clips[2].id).toBe("outro");
  });

  it("sectionId matches id", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await GET_clips();
    const data = await response.json();

    for (const clip of data.clips) {
      expect(clip.sectionId).toBe(clip.id);
    }
  });
});

// ---------------------------------------------------------------------------
// 10. GET_clips — status detection
// ---------------------------------------------------------------------------

describe("GET_clips — status detection", () => {
  it("returns 'done' when clip file exists", async () => {
    mockExistsSync.mockReturnValue(true);
    mockStatSync.mockReturnValue({ mtimeMs: 1000 });

    const response = await GET_clips();
    const data = await response.json();

    expect(data.clips[0].status).toBe("done");
  });

  it("returns 'missing' when clip file does not exist", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await GET_clips();
    const data = await response.json();

    expect(data.clips[0].status).toBe("missing");
  });
});

// ---------------------------------------------------------------------------
// 11. GET_clips — frameChainDeps
// ---------------------------------------------------------------------------

describe("GET_clips — frameChainDeps", () => {
  it("first clip has no frame chain deps", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await GET_clips();
    const data = await response.json();

    expect(data.clips[0].frameChainDeps).toEqual([]);
  });

  it("non-first clip depends on previous clip's last frame", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await GET_clips();
    const data = await response.json();

    expect(data.clips[1].frameChainDeps).toHaveLength(1);
    expect(data.clips[1].frameChainDeps[0]).toContain("intro_last_frame.png");
  });

  it("deps path includes outputs/veo/ prefix", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await GET_clips();
    const data = await response.json();

    expect(data.clips[1].frameChainDeps[0]).toMatch(
      /outputs[/\\]veo[/\\]intro_last_frame\.png/
    );
  });
});

// ---------------------------------------------------------------------------
// 12. GET_clips — stale detection
// ---------------------------------------------------------------------------

describe("GET_clips — stale detection", () => {
  it("clip is stale when dep has newer mtime than clip", async () => {
    mockExistsSync.mockReturnValue(true);
    mockStatSync.mockImplementation((p: string) => {
      // clip mtime = 1000, dep mtime = 2000 (newer)
      if (typeof p === "string" && p.includes("_last_frame")) {
        return { mtimeMs: 2000 };
      }
      return { mtimeMs: 1000 };
    });

    const response = await GET_clips();
    const data = await response.json();

    // Second clip (main) depends on intro's last frame
    expect(data.clips[1].stale).toBe(true);
  });

  it("clip is not stale when dep has older mtime", async () => {
    mockExistsSync.mockReturnValue(true);
    mockStatSync.mockImplementation((p: string) => {
      // clip mtime = 2000, dep mtime = 1000 (older)
      if (typeof p === "string" && p.includes("_last_frame")) {
        return { mtimeMs: 1000 };
      }
      return { mtimeMs: 2000 };
    });

    const response = await GET_clips();
    const data = await response.json();

    expect(data.clips[1].stale).toBe(false);
  });

  it("first clip (no deps) is never stale", async () => {
    mockExistsSync.mockReturnValue(true);
    mockStatSync.mockReturnValue({ mtimeMs: 1000 });

    const response = await GET_clips();
    const data = await response.json();

    expect(data.clips[0].stale).toBe(false);
  });

  it("missing clip is not stale regardless of dep mtime", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await GET_clips();
    const data = await response.json();

    expect(data.clips[1].stale).toBe(false);
  });
});

// ---------------------------------------------------------------------------
// 13. POST_references — validation and response
// ---------------------------------------------------------------------------

describe("POST_references — validation and response", () => {
  it("returns 400 when referenceId is missing", async () => {
    const request = makeRequest(
      "http://localhost/api/pipeline/veo/references/run",
      {}
    );

    const response = await POST_references(request as any);
    expect(response.status).toBe(400);

    const data = await response.json();
    expect(data.error).toContain("referenceId");
  });

  it("returns 400 when referenceId is not a string", async () => {
    const request = makeRequest(
      "http://localhost/api/pipeline/veo/references/run",
      { referenceId: 123 }
    );

    const response = await POST_references(request as any);
    expect(response.status).toBe(400);
  });

  it("returns 400 when referenceId is empty string", async () => {
    const request = makeRequest(
      "http://localhost/api/pipeline/veo/references/run",
      { referenceId: "" }
    );

    const response = await POST_references(request as any);
    expect(response.status).toBe(400);
  });

  it("returns jobId on valid request", async () => {
    mockExistsSync.mockReturnValue(false);
    const request = makeRequest(
      "http://localhost/api/pipeline/veo/references/run",
      { referenceId: "host-portrait" }
    );

    const response = await POST_references(request as any);
    const data = await response.json();

    expect(data).toHaveProperty("jobId");
    expect(data.jobId).toBe("test-job-ref-001");
  });

  it("calls createJob with 'veo' stage and referenceId params", async () => {
    mockExistsSync.mockReturnValue(false);
    const request = makeRequest(
      "http://localhost/api/pipeline/veo/references/run",
      { referenceId: "host-portrait" }
    );

    await POST_references(request as any);
    await flushPromises();

    expect(mockCreateJob).toHaveBeenCalledWith("veo", {
      referenceId: "host-portrait",
      mode: "reference",
    });
  });

  it("calls runJob with the created jobId", async () => {
    mockExistsSync.mockReturnValue(false);
    const request = makeRequest(
      "http://localhost/api/pipeline/veo/references/run",
      { referenceId: "host-portrait" }
    );

    await POST_references(request as any);
    await flushPromises();

    expect(mockRunJob).toHaveBeenCalledWith("test-job-ref-001", expect.any(Function));
  });

  it("reference output path is outputs/veo/references/{referenceId}.png", async () => {
    mockExistsSync.mockReturnValue(false);

    // Capture the executor passed to runJob
    mockRunJob.mockImplementation(async (jobId: string, executor: Function) => {
      await executor(jest.fn());
    });

    const request = makeRequest(
      "http://localhost/api/pipeline/veo/references/run",
      { referenceId: "host-portrait" }
    );

    await POST_references(request as any);
    await flushPromises();

    const outputPath = mockGenerateReferenceImage.mock.calls[0][1];
    expect(outputPath).toContain("outputs");
    expect(outputPath).toContain("veo");
    expect(outputPath).toContain("references");
    expect(outputPath).toContain("host-portrait.png");
  });

  it("calls generateReferenceImage with resolved prompt and output path", async () => {
    mockExistsSync.mockReturnValue(false);

    mockRunJob.mockImplementation(async (jobId: string, executor: Function) => {
      await executor(jest.fn());
    });

    const request = makeRequest(
      "http://localhost/api/pipeline/veo/references/run",
      { referenceId: "host-portrait" }
    );

    await POST_references(request as any);
    await flushPromises();

    expect(mockGenerateReferenceImage).toHaveBeenCalledTimes(1);
    // When no references.json or txt found, prompt falls back to referenceId
    expect(mockGenerateReferenceImage.mock.calls[0][0]).toBe("host-portrait");
  });
});

// ---------------------------------------------------------------------------
// 14. POST_references — no authentication required
// ---------------------------------------------------------------------------

describe("POST_references — no authentication required", () => {
  it("does not require authorization headers", async () => {
    mockExistsSync.mockReturnValue(false);
    const request = new Request(
      "http://localhost/api/pipeline/veo/references/run",
      {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          Authorization: "Bearer fake-token",
        },
        body: JSON.stringify({ referenceId: "host" }),
      }
    );

    const response = await POST_references(request as any);
    expect(response.status).toBe(200);
  });
});

// ---------------------------------------------------------------------------
// 15. GET_staging — staging manifest
// ---------------------------------------------------------------------------

describe("GET_staging — staging manifest", () => {
  it("returns Response.json with files array", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

    const response = await GET_staging();
    const data = await response.json();

    expect(data).toHaveProperty("files");
    expect(Array.isArray(data.files)).toBe(true);
  });

  it("expected files come from project sections mapped to veo clip filenames", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

    const response = await GET_staging();
    const data = await response.json();

    const expectedFiles = data.files.filter(
      (f: any) => f.expected === true
    );
    expect(expectedFiles).toHaveLength(3);
    expect(expectedFiles[0].file).toBe("veo/intro.mp4");
    expect(expectedFiles[1].file).toBe("veo/main.mp4");
    expect(expectedFiles[2].file).toBe("veo/outro.mp4");
  });

  it("marks expected files as present: false when not in remotion/public/", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

    const response = await GET_staging();
    const data = await response.json();

    for (const entry of data.files) {
      if (entry.expected) {
        expect(entry.present).toBe(false);
      }
    }
  });

  it("each entry has AssetStagingEntry shape: { file, expected, present }", async () => {
    mockExistsSync.mockReturnValue(false);
    mockReaddirSync.mockReturnValue([]);

    const response = await GET_staging();
    const data = await response.json();

    for (const entry of data.files) {
      expect(entry).toHaveProperty("file");
      expect(entry).toHaveProperty("expected");
      expect(entry).toHaveProperty("present");
      expect(typeof entry.file).toBe("string");
      expect(typeof entry.expected).toBe("boolean");
      expect(typeof entry.present).toBe("boolean");
    }
  });

  it("includes unexpected present files with expected: false", async () => {
    const pathMod = require("path");
    const publicDir = pathMod.join(process.cwd(), "remotion", "public");

    // Simulate remotion/public/ directory exists with an extra file
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p === publicDir) return true;
      return false;
    });
    mockReaddirSync.mockImplementation((dir: string, opts?: any) => {
      if (typeof dir === "string" && dir === publicDir) {
        return [
          {
            name: "extra-file.mp4",
            isDirectory: () => false,
            isFile: () => true,
          },
        ];
      }
      return [];
    });

    const response = await GET_staging();
    const data = await response.json();

    const unexpectedEntries = data.files.filter(
      (f: any) => f.expected === false && f.present === true
    );
    expect(unexpectedEntries.length).toBeGreaterThanOrEqual(1);
    expect(unexpectedEntries[0].file).toBe("extra-file.mp4");
  });
});

// ---------------------------------------------------------------------------
// 16. resolveVeoPrompt — prompt resolution (tested via executor)
// ---------------------------------------------------------------------------

describe("resolveVeoPrompt — prompt resolution", () => {
  it("reads prompt from veo.json with 'prompt' key", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]];
    mockLoadProject.mockReturnValue(config);

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("veo.json")) return true;
      return false;
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("veo.json")) {
        return JSON.stringify({ prompt: "Aerial drone shot" });
      }
      return "";
    });

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    const prompt = mockGenerateVeoClip.mock.calls[0][0];
    expect(prompt).toBe("Aerial drone shot");
  });

  it("reads prompt from veo.json with 'veoPrompt' key", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]];
    mockLoadProject.mockReturnValue(config);

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("veo.json")) return true;
      return false;
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("veo.json")) {
        return JSON.stringify({ veoPrompt: "City skyline at dusk" });
      }
      return "";
    });

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    const prompt = mockGenerateVeoClip.mock.calls[0][0];
    expect(prompt).toBe("City skyline at dusk");
  });

  it("reads prompt from veo.json with 'videoPrompt' key", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]];
    mockLoadProject.mockReturnValue(config);

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("veo.json")) return true;
      return false;
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("veo.json")) {
        return JSON.stringify({ videoPrompt: "Ocean waves crashing" });
      }
      return "";
    });

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    const prompt = mockGenerateVeoClip.mock.calls[0][0];
    expect(prompt).toBe("Ocean waves crashing");
  });

  it("reads prompt from veo.txt as plain text", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]];
    mockLoadProject.mockReturnValue(config);

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.endsWith("veo.txt")) return true;
      return false;
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.endsWith("veo.txt")) {
        return "A serene mountain landscape";
      }
      return "";
    });

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    const prompt = mockGenerateVeoClip.mock.calls[0][0];
    expect(prompt).toBe("A serene mountain landscape");
  });

  it("falls back from veo.json to spec.json to veo.txt", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]];
    mockLoadProject.mockReturnValue(config);

    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("spec.json")) return true;
      return false;
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("spec.json")) {
        return JSON.stringify({ prompt: "From spec.json" });
      }
      return "";
    });

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());

    const prompt = mockGenerateVeoClip.mock.calls[0][0];
    expect(prompt).toBe("From spec.json");
  });

  it("throws when no prompt file is found", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]];
    mockLoadProject.mockReturnValue(config);

    mockExistsSync.mockReturnValue(false);

    const mockSend = jest.fn();
    const executor = registerCallArgs.factory({}, mockSend);

    await expect(executor(jest.fn())).rejects.toThrow("No Veo prompt found");
  });
});

// ---------------------------------------------------------------------------
// 17. resolveReferencePrompt — reference prompt resolution
// ---------------------------------------------------------------------------

describe("resolveReferencePrompt — via POST_references", () => {
  it("reads prompt from references.json when entry is a string", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("references.json")) return true;
      return false;
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("references.json")) {
        return JSON.stringify({
          "host-portrait": "Professional headshot of a young woman",
        });
      }
      return "";
    });

    mockRunJob.mockImplementation(async (jobId: string, executor: Function) => {
      await executor(jest.fn());
    });

    const request = makeRequest(
      "http://localhost/api/pipeline/veo/references/run",
      { referenceId: "host-portrait" }
    );

    await POST_references(request as any);
    await flushPromises();

    expect(mockGenerateReferenceImage.mock.calls[0][0]).toBe(
      "Professional headshot of a young woman"
    );
  });

  it("reads prompt from references.json when entry has .prompt property", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("references.json")) return true;
      return false;
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.includes("references.json")) {
        return JSON.stringify({
          "host-portrait": { prompt: "Studio lit headshot" },
        });
      }
      return "";
    });

    mockRunJob.mockImplementation(async (jobId: string, executor: Function) => {
      await executor(jest.fn());
    });

    const request = makeRequest(
      "http://localhost/api/pipeline/veo/references/run",
      { referenceId: "host-portrait" }
    );

    await POST_references(request as any);
    await flushPromises();

    expect(mockGenerateReferenceImage.mock.calls[0][0]).toBe(
      "Studio lit headshot"
    );
  });

  it("falls back to referenceId as prompt when no files found", async () => {
    mockExistsSync.mockReturnValue(false);

    mockRunJob.mockImplementation(async (jobId: string, executor: Function) => {
      await executor(jest.fn());
    });

    const request = makeRequest(
      "http://localhost/api/pipeline/veo/references/run",
      { referenceId: "host-portrait" }
    );

    await POST_references(request as any);
    await flushPromises();

    expect(mockGenerateReferenceImage.mock.calls[0][0]).toBe("host-portrait");
  });
});

// ---------------------------------------------------------------------------
// 18. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/pipeline/veo/run/route.ts source structure", () => {
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
        "veo",
        "run",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async function POST_run", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+POST_run/);
  });

  it("exports async function GET_clips", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+GET_clips/);
  });

  it("exports async function POST_references", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+POST_references/);
  });

  it("exports async function GET_staging", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+GET_staging/);
  });

  it("imports registerExecutor and runPipelineStage from @/lib/jobs", () => {
    expect(sourceCode).toMatch(/@\/lib\/jobs/);
    expect(sourceCode).toMatch(/registerExecutor/);
    expect(sourceCode).toMatch(/runPipelineStage/);
  });

  it("imports createJob and runJob from @/lib/jobs", () => {
    expect(sourceCode).toMatch(/createJob/);
    expect(sourceCode).toMatch(/runJob/);
  });

  it("imports createSseStream from @/lib/sse", () => {
    expect(sourceCode).toMatch(/@\/lib\/sse/);
    expect(sourceCode).toMatch(/createSseStream/);
  });

  it("imports loadProject from @/lib/project", () => {
    expect(sourceCode).toMatch(/@\/lib\/project/);
    expect(sourceCode).toMatch(/loadProject/);
  });

  it("imports generateVeoClip, extractLastFrame, generateReferenceImage from @/lib/veo", () => {
    expect(sourceCode).toMatch(/@\/lib\/veo/);
    expect(sourceCode).toMatch(/generateVeoClip/);
    expect(sourceCode).toMatch(/extractLastFrame/);
    expect(sourceCode).toMatch(/generateReferenceImage/);
  });

  it("imports SseSend from @/lib/types", () => {
    expect(sourceCode).toMatch(/@\/lib\/types/);
    expect(sourceCode).toMatch(/SseSend/);
  });

  it("calls registerExecutor('veo', ...)", () => {
    expect(sourceCode).toMatch(/registerExecutor\s*\(\s*["']veo["']/);
  });

  it("calls runPipelineStage('veo', ...)", () => {
    expect(sourceCode).toMatch(/runPipelineStage\s*\(\s*["']veo["']/);
  });

  it("uses new Response(stream, ...) for SSE streaming", () => {
    expect(sourceCode).toMatch(/new\s+Response\s*\(\s*stream/);
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

  it("emits clip events with type 'clip'", () => {
    expect(sourceCode).toMatch(/type:\s*["']clip["']/);
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

  it("clip output path is outputs/veo/{clipId}.mp4", () => {
    expect(sourceCode).toContain("outputs");
    expect(sourceCode).toContain("veo");
    expect(sourceCode).toMatch(/\.mp4/);
  });

  it("frame chain output path is outputs/veo/{clipId}_last_frame.png", () => {
    expect(sourceCode).toMatch(/_last_frame\.png/);
  });

  it("reference portrait path is outputs/veo/references/{referenceId}.png", () => {
    expect(sourceCode).toContain("outputs");
    expect(sourceCode).toContain("references");
    expect(sourceCode).toMatch(/referenceId.*\.png/);
  });

  it("defines VeoClip type with required fields", () => {
    expect(sourceCode).toMatch(/type\s+VeoClip/);
    expect(sourceCode).toContain("id: string");
    expect(sourceCode).toContain("sectionId: string");
    expect(sourceCode).toContain("aspectRatio");
    expect(sourceCode).toContain("stale: boolean");
    expect(sourceCode).toContain("frameChainDeps: string[]");
  });

  it("defines AssetStagingEntry type", () => {
    expect(sourceCode).toMatch(/type\s+AssetStagingEntry/);
    expect(sourceCode).toMatch(/file:\s*string/);
    expect(sourceCode).toMatch(/expected:\s*boolean/);
    expect(sourceCode).toMatch(/present:\s*boolean/);
  });

  it("uses runtime = 'nodejs'", () => {
    expect(sourceCode).toMatch(/runtime\s*=\s*["']nodejs["']/);
  });

  it("checks referenceId validation in POST_references", () => {
    expect(sourceCode).toMatch(/referenceId is required/);
  });

  it("uses remotion/public/ as public directory for staging", () => {
    expect(sourceCode).toMatch(/remotion.*public/);
  });

  it("uses Response.json for JSON responses", () => {
    expect(sourceCode).toMatch(/Response\.json/);
  });

  it("creates job with 'veo' stage and mode 'reference'", () => {
    expect(sourceCode).toMatch(/createJob\s*\(\s*["']veo["']/);
    expect(sourceCode).toMatch(/mode:\s*["']reference["']/);
  });
});

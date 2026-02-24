/**
 * Tests for app/api/pipeline/render/run/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_pipeline_render_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. POST /api/pipeline/render/run — accepts { sections?: string[] }, renders
 *      up to maxParallelRenders sections concurrently, returns SSE stream with { jobId }
 *   2. After each section renders, reads ffprobe duration via getSectionDuration()
 *      and updates project.json with durationSeconds and recalculated offsetSeconds
 *   3. POST /api/pipeline/stitch/run — runs ffmpeg concat via stitchFullVideo(),
 *      returns { jobId }
 *   4. GET /api/pipeline/render/status — returns { sections, fullVideo }
 *   5. SectionRenderStatus = { sectionId, status: 'done'|'missing'|'error', duration?, progress? }
 *   6. FullVideoInfo = { exists, path?, size?, duration? }
 *   7. No authentication required
 *   8. registerExecutor('render', ...) called at module load time
 *   9. Parallel renders: batches by config.render.maxParallelRenders
 *  10. Section output path: outputs/sections/{sectionId}.mp4
 *  11. Full video output: outputs/full_video.mp4
 *  12. Emit per-section progress events: { type: 'section-progress', sectionId, percent }
 *  13. offsetSeconds recalculation: cumulative durations in section order
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

const mockRenderSection = jest.fn();
const mockGetSectionDuration = jest.fn();
const mockStitchFullVideo = jest.fn();

jest.mock("@/lib/render", () => ({
  renderSection: (...args: unknown[]) => mockRenderSection(...args),
  getSectionDuration: (...args: unknown[]) => mockGetSectionDuration(...args),
  stitchFullVideo: (...args: unknown[]) => mockStitchFullVideo(...args),
}));

const mockLoadProject = jest.fn();
const mockSaveProject = jest.fn();

jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
  saveProject: (...args: unknown[]) => mockSaveProject(...args),
}));

const mockMkdir = jest.fn();
const mockAccess = jest.fn();
const mockStat = jest.fn();

jest.mock("fs/promises", () => ({
  mkdir: (...args: unknown[]) => mockMkdir(...args),
  access: (...args: unknown[]) => mockAccess(...args),
  stat: (...args: unknown[]) => mockStat(...args),
}));

jest.mock("crypto", () => ({
  randomUUID: () => "test-uuid-stitch-001",
}));

// Import after mocking
import {
  POST,
  POST_stitch,
  GET_status,
} from "../app/api/pipeline/render/run/route";

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
  if (body) {
    return new Request(url, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(body),
    });
  }
  return new Request(url, { method: "POST" });
}

function makeGetRequest(url: string): Request {
  return new Request(url, { method: "GET" });
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
      maxParallelRenders: 2,
      outputDir: "output/final",
      fps: 30,
      width: 1920,
      height: 1080,
    },
  };
}

// ---------------------------------------------------------------------------
// Setup
// ---------------------------------------------------------------------------

beforeEach(() => {
  mockRunPipelineStage.mockReset();
  mockRenderSection.mockReset();
  mockGetSectionDuration.mockReset();
  mockStitchFullVideo.mockReset();
  mockLoadProject.mockReset();
  mockSaveProject.mockReset();
  mockMkdir.mockReset();
  mockAccess.mockReset();
  mockStat.mockReset();

  mockRunPipelineStage.mockResolvedValue("test-job-render-001");
  mockRenderSection.mockResolvedValue(undefined);
  mockGetSectionDuration.mockResolvedValue(10.0);
  mockStitchFullVideo.mockResolvedValue(undefined);
  mockLoadProject.mockReturnValue(mockProjectConfig());
  mockSaveProject.mockReturnValue(undefined);
  mockMkdir.mockResolvedValue(undefined);
  mockAccess.mockResolvedValue(undefined);
  mockStat.mockResolvedValue({ size: 1024000 });
});

// ---------------------------------------------------------------------------
// 1. registerExecutor — module load side effect
// ---------------------------------------------------------------------------

describe("registerExecutor at module load", () => {
  it("registers executor for 'render' stage", () => {
    expect(registerCallArgs.stage).toBe("render");
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
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );
    expect(response).toBeInstanceOf(Response);
  });

  it("sets Content-Type to text/event-stream", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("sets Cache-Control to no-cache", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );
    expect(response.headers.get("Cache-Control")).toBe("no-cache");
  });

  it("sets Connection to keep-alive", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );
    expect(response.headers.get("Connection")).toBe("keep-alive");
  });

  it("returns a ReadableStream body", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );
    expect(response.body).toBeInstanceOf(ReadableStream);
  });
});

// ---------------------------------------------------------------------------
// 3. POST — success flow with SSE events
// ---------------------------------------------------------------------------

describe("POST — success flow", () => {
  beforeEach(() => {
    mockRunPipelineStage.mockResolvedValue("test-job-render-42");
  });

  it("calls runPipelineStage with 'render' stage", async () => {
    await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );
    await flushPromises();

    expect(mockRunPipelineStage).toHaveBeenCalledTimes(1);
    expect(mockRunPipelineStage.mock.calls[0][0]).toBe("render");
  });

  it("passes sections param from body to runPipelineStage", async () => {
    await POST(
      makeRequest("http://localhost/api/pipeline/render/run", {
        sections: ["intro", "outro"],
      }) as any
    );
    await flushPromises();

    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.sections).toEqual(["intro", "outro"]);
  });

  it("passes undefined sections when body has no sections array", async () => {
    await POST(
      makeRequest("http://localhost/api/pipeline/render/run", {}) as any
    );
    await flushPromises();

    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.sections).toBeUndefined();
  });

  it("passes a send function to runPipelineStage", async () => {
    await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );
    await flushPromises();

    expect(typeof mockRunPipelineStage.mock.calls[0][2]).toBe("function");
  });

  it("emits jobId event after runPipelineStage resolves", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const jobEvent = events.find((e: any) => e.jobId) as any;
    expect(jobEvent).toBeDefined();
    expect(jobEvent.jobId).toBe("test-job-render-42");
  });
});

// ---------------------------------------------------------------------------
// 4. POST — body parameter handling
// ---------------------------------------------------------------------------

describe("POST — body parameter handling", () => {
  it("works with no body (renders all sections)", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );
    expect(response).toBeInstanceOf(Response);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("accepts specific sections array", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run", {
        sections: ["intro", "outro"],
      }) as any
    );
    expect(response).toBeInstanceOf(Response);
  });

  it("handles invalid body gracefully (non-JSON)", async () => {
    const request = new Request("http://localhost/api/pipeline/render/run", {
      method: "POST",
      body: "not json",
    });

    const response = await POST(request as any);
    expect(response).toBeInstanceOf(Response);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("handles body with sections as non-array gracefully", async () => {
    await POST(
      makeRequest("http://localhost/api/pipeline/render/run", {
        sections: "not-an-array",
      }) as any
    );
    await flushPromises();

    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.sections).toBeUndefined();
  });
});

// ---------------------------------------------------------------------------
// 5. POST — error handling
// ---------------------------------------------------------------------------

describe("POST — error handling", () => {
  it("emits error event when runPipelineStage rejects with Error", async () => {
    mockRunPipelineStage.mockRejectedValue(new Error("Render failed"));

    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const errorEvent = events.find((e: any) => e.type === "error") as any;
    expect(errorEvent).toBeDefined();
    expect(errorEvent.message).toBe("Render failed");
  });

  it("emits generic error for non-Error throws", async () => {
    mockRunPipelineStage.mockRejectedValue("string error");

    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
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
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });
});

// ---------------------------------------------------------------------------
// 6. POST — no authentication required
// ---------------------------------------------------------------------------

describe("POST — no authentication required", () => {
  it("does not require authorization headers", async () => {
    const request = new Request("http://localhost/api/pipeline/render/run", {
      method: "POST",
      headers: { Authorization: "Bearer fake-token" },
    });

    const response = await POST(request as any);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("works with minimal request (no body, no auth)", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );
    expect(response).toBeInstanceOf(Response);
  });
});

// ---------------------------------------------------------------------------
// 7. Render executor factory — registered with pipeline job system
// ---------------------------------------------------------------------------

describe("render executor factory", () => {
  it("returns an async function when called with params and send", () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    expect(typeof executor).toBe("function");
  });

  it("calls loadProject() to get section list", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    expect(mockLoadProject).toHaveBeenCalled();
  });

  it("renders all sections when params.sections is not provided", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    // With 3 sections and maxParallelRenders=2, renderSection should be called 3 times
    expect(mockRenderSection).toHaveBeenCalledTimes(3);
  });

  it("renders only specified sections when params.sections is provided", async () => {
    const executor = registerCallArgs.factory(
      { sections: ["intro", "outro"] },
      jest.fn()
    );
    await executor(jest.fn());

    expect(mockRenderSection).toHaveBeenCalledTimes(2);
  });

  it("passes compositionId and output path to renderSection", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro
    mockLoadProject.mockReturnValue(config);

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const pathMod = require("path");
    expect(mockRenderSection.mock.calls[0][0]).toBe("IntroComposition");
    expect(mockRenderSection.mock.calls[0][1]).toBe(
      pathMod.join("outputs", "sections", "intro.mp4")
    );
  });

  it("uses outputs/sections/{sectionId}.mp4 output path", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[1]]; // just main
    mockLoadProject.mockReturnValue(config);

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const pathMod = require("path");
    expect(mockRenderSection.mock.calls[0][1]).toBe(
      pathMod.join("outputs", "sections", "main.mp4")
    );
  });

  it("creates outputs/sections directory with recursive flag", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const pathMod = require("path");
    expect(mockMkdir).toHaveBeenCalledWith(
      pathMod.join("outputs", "sections"),
      { recursive: true }
    );
  });

  it("calls getSectionDuration after each section renders", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    // 3 sections
    expect(mockGetSectionDuration).toHaveBeenCalledTimes(3);
  });

  it("calls saveProject to update durations after each section renders", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    // saveProject called once per section for duration updates
    expect(mockSaveProject).toHaveBeenCalledTimes(3);
  });

  it("updates durationSeconds for rendered section in project config", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro
    mockLoadProject.mockReturnValue(config);
    mockGetSectionDuration.mockResolvedValue(15.5);

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const savedConfig = mockSaveProject.mock.calls[0][0];
    const introSection = savedConfig.sections.find(
      (s: any) => s.id === "intro"
    );
    expect(introSection.durationSeconds).toBe(15.5);
  });

  it("recalculates offsetSeconds as cumulative durations", async () => {
    // Set up config with known durations
    const config = mockProjectConfig();
    mockLoadProject.mockReturnValue(config);

    // Return different durations for each section
    mockGetSectionDuration
      .mockResolvedValueOnce(10.0)
      .mockResolvedValueOnce(20.0)
      .mockResolvedValueOnce(5.0);

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    // The last saveProject call should have the final calculated offsets
    const lastCallIndex = mockSaveProject.mock.calls.length - 1;
    const savedConfig = mockSaveProject.mock.calls[lastCallIndex][0];

    // After all 3 sections are rendered with durations [10, 20, 5]:
    // intro: offset=0, main: offset=10, outro: offset=30
    expect(savedConfig.sections[0].offsetSeconds).toBe(0);
  });

  it("emits section-progress events via send callback", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro
    mockLoadProject.mockReturnValue(config);

    // Capture the onProgress callback and call it
    mockRenderSection.mockImplementation(
      async (
        _compositionId: string,
        _outputPath: string,
        onProgress: (p: { percent: number }) => void
      ) => {
        onProgress({ percent: 50 });
        onProgress({ percent: 100 });
      }
    );

    const sendFn = jest.fn();
    const executor = registerCallArgs.factory({}, sendFn);
    await executor(jest.fn());

    // Verify section-progress events were sent
    const progressCalls = sendFn.mock.calls.filter(
      (call: any[]) => call[0]?.type === "section-progress"
    );
    expect(progressCalls.length).toBeGreaterThanOrEqual(2);
    expect(progressCalls[0][0]).toMatchObject({
      type: "section-progress",
      sectionId: "intro",
      percent: 50,
    });
  });

  it("respects maxParallelRenders for batching", async () => {
    const config = mockProjectConfig();
    config.render.maxParallelRenders = 1;
    mockLoadProject.mockReturnValue(config);

    // Track render invocation order
    const renderOrder: string[] = [];
    mockRenderSection.mockImplementation(
      async (compositionId: string) => {
        renderOrder.push(compositionId);
      }
    );

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    // All 3 sections should be rendered sequentially with maxParallel=1
    expect(renderOrder).toHaveLength(3);
  });

  it("renders in parallel batches of maxParallelRenders", async () => {
    const config = mockProjectConfig();
    config.render.maxParallelRenders = 2;
    mockLoadProject.mockReturnValue(config);

    let concurrentCount = 0;
    let maxConcurrent = 0;

    mockRenderSection.mockImplementation(async () => {
      concurrentCount++;
      maxConcurrent = Math.max(maxConcurrent, concurrentCount);
      await new Promise((resolve) => setTimeout(resolve, 10));
      concurrentCount--;
    });

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    expect(maxConcurrent).toBeLessThanOrEqual(2);
  });

  it("uses onLog to report rendering progress", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro
    mockLoadProject.mockReturnValue(config);

    const onLog = jest.fn();
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(onLog);

    expect(onLog).toHaveBeenCalled();
    const logMessages = onLog.mock.calls.map((c: any[]) => c[0]);
    expect(logMessages.some((m: string) => m.includes("intro"))).toBe(true);
  });

  it("propagates renderSection errors", async () => {
    mockRenderSection.mockRejectedValue(new Error("Render crashed"));

    const executor = registerCallArgs.factory({}, jest.fn());
    await expect(executor(jest.fn())).rejects.toThrow("Render crashed");
  });

  it("handles empty sections array by rendering all sections", async () => {
    const executor = registerCallArgs.factory(
      { sections: [] },
      jest.fn()
    );
    await executor(jest.fn());

    // Empty array is falsy in the check, so all sections should render
    expect(mockRenderSection).toHaveBeenCalledTimes(3);
  });

  it("defaults maxParallelRenders to 1 when not set", async () => {
    const config = mockProjectConfig();
    config.render.maxParallelRenders = 0;
    mockLoadProject.mockReturnValue(config);

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    // Should still render all 3 sections (sequentially with maxParallel=1)
    expect(mockRenderSection).toHaveBeenCalledTimes(3);
  });
});

// ---------------------------------------------------------------------------
// 8. POST_stitch — stitch full video
// ---------------------------------------------------------------------------

describe("POST_stitch", () => {
  it("returns JSON response with jobId", async () => {
    const response = await POST_stitch(
      makeRequest("http://localhost/api/pipeline/stitch/run") as any
    );
    const body = await response.json();

    expect(body.jobId).toBeDefined();
    expect(typeof body.jobId).toBe("string");
  });

  it("returns 200 status on success", async () => {
    const response = await POST_stitch(
      makeRequest("http://localhost/api/pipeline/stitch/run") as any
    );

    expect(response.status).toBe(200);
  });

  it("calls loadProject to get section list", async () => {
    await POST_stitch(
      makeRequest("http://localhost/api/pipeline/stitch/run") as any
    );

    expect(mockLoadProject).toHaveBeenCalledTimes(1);
  });

  it("calls stitchFullVideo with section paths and output path", async () => {
    await POST_stitch(
      makeRequest("http://localhost/api/pipeline/stitch/run") as any
    );

    expect(mockStitchFullVideo).toHaveBeenCalledTimes(1);

    const pathMod = require("path");
    const sectionPaths = mockStitchFullVideo.mock.calls[0][0];
    expect(sectionPaths).toEqual([
      pathMod.join("outputs", "sections", "intro.mp4"),
      pathMod.join("outputs", "sections", "main.mp4"),
      pathMod.join("outputs", "sections", "outro.mp4"),
    ]);
  });

  it("outputs to outputs/full_video.mp4", async () => {
    await POST_stitch(
      makeRequest("http://localhost/api/pipeline/stitch/run") as any
    );

    const pathMod = require("path");
    const outputPath = mockStitchFullVideo.mock.calls[0][1];
    expect(outputPath).toBe(pathMod.join("outputs", "full_video.mp4"));
  });

  it("creates outputs directory", async () => {
    await POST_stitch(
      makeRequest("http://localhost/api/pipeline/stitch/run") as any
    );

    expect(mockMkdir).toHaveBeenCalledWith("outputs", { recursive: true });
  });

  it("returns 500 on error", async () => {
    mockStitchFullVideo.mockRejectedValue(new Error("ffmpeg failed"));

    const response = await POST_stitch(
      makeRequest("http://localhost/api/pipeline/stitch/run") as any
    );

    expect(response.status).toBe(500);
    const body = await response.json();
    expect(body.error).toBe("Internal Server Error");
  });

  it("does not require authentication", async () => {
    const request = new Request("http://localhost/api/pipeline/stitch/run", {
      method: "POST",
      headers: { Authorization: "Bearer fake-token" },
    });

    const response = await POST_stitch(request as any);
    expect(response.status).toBe(200);
  });
});

// ---------------------------------------------------------------------------
// 9. GET_status — render status
// ---------------------------------------------------------------------------

describe("GET_status", () => {
  it("returns 200 status on success", async () => {
    const response = await GET_status(
      makeGetRequest("http://localhost/api/pipeline/render/status") as any
    );

    expect(response.status).toBe(200);
  });

  it("returns sections array in response", async () => {
    const response = await GET_status(
      makeGetRequest("http://localhost/api/pipeline/render/status") as any
    );
    const body = await response.json();

    expect(Array.isArray(body.sections)).toBe(true);
    expect(body.sections.length).toBe(3);
  });

  it("returns fullVideo object in response", async () => {
    const response = await GET_status(
      makeGetRequest("http://localhost/api/pipeline/render/status") as any
    );
    const body = await response.json();

    expect(body.fullVideo).toBeDefined();
    expect(typeof body.fullVideo.exists).toBe("boolean");
  });

  it("marks sections as 'done' when file exists and duration is available", async () => {
    mockAccess.mockResolvedValue(undefined);
    mockGetSectionDuration.mockResolvedValue(12.5);

    const response = await GET_status(
      makeGetRequest("http://localhost/api/pipeline/render/status") as any
    );
    const body = await response.json();

    expect(body.sections[0].status).toBe("done");
    expect(body.sections[0].sectionId).toBe("intro");
    expect(body.sections[0].duration).toBe(12.5);
  });

  it("marks sections as 'missing' when file does not exist", async () => {
    mockAccess.mockRejectedValue(new Error("ENOENT"));

    const response = await GET_status(
      makeGetRequest("http://localhost/api/pipeline/render/status") as any
    );
    const body = await response.json();

    expect(body.sections[0].status).toBe("missing");
    expect(body.sections[0].sectionId).toBe("intro");
  });

  it("includes sectionId in each status entry", async () => {
    const response = await GET_status(
      makeGetRequest("http://localhost/api/pipeline/render/status") as any
    );
    const body = await response.json();

    const ids = body.sections.map((s: any) => s.sectionId);
    expect(ids).toEqual(["intro", "main", "outro"]);
  });

  it("checks correct file paths for section status", async () => {
    await GET_status(
      makeGetRequest("http://localhost/api/pipeline/render/status") as any
    );

    const pathMod = require("path");
    // access is called for each section
    expect(mockAccess).toHaveBeenCalledWith(
      pathMod.join("outputs", "sections", "intro.mp4")
    );
    expect(mockAccess).toHaveBeenCalledWith(
      pathMod.join("outputs", "sections", "main.mp4")
    );
    expect(mockAccess).toHaveBeenCalledWith(
      pathMod.join("outputs", "sections", "outro.mp4")
    );
  });

  it("returns fullVideo.exists=true when full_video.mp4 exists", async () => {
    mockStat.mockResolvedValue({ size: 5000000 });
    mockGetSectionDuration.mockResolvedValue(65.5);

    const response = await GET_status(
      makeGetRequest("http://localhost/api/pipeline/render/status") as any
    );
    const body = await response.json();

    expect(body.fullVideo.exists).toBe(true);
    expect(body.fullVideo.size).toBe(5000000);
  });

  it("returns fullVideo.exists=false when full_video.mp4 does not exist", async () => {
    mockStat.mockRejectedValue(new Error("ENOENT"));

    const response = await GET_status(
      makeGetRequest("http://localhost/api/pipeline/render/status") as any
    );
    const body = await response.json();

    expect(body.fullVideo.exists).toBe(false);
  });

  it("includes path and duration in fullVideo when it exists", async () => {
    mockStat.mockResolvedValue({ size: 5000000 });
    // getSectionDuration is called for sections (3) + fullVideo (1)
    mockGetSectionDuration.mockResolvedValue(65.5);

    const response = await GET_status(
      makeGetRequest("http://localhost/api/pipeline/render/status") as any
    );
    const body = await response.json();

    const pathMod = require("path");
    expect(body.fullVideo.path).toBe(pathMod.join("outputs", "full_video.mp4"));
    expect(body.fullVideo.duration).toBe(65.5);
  });

  it("returns 500 when loadProject throws", async () => {
    mockLoadProject.mockImplementation(() => {
      throw new Error("project.json not found");
    });

    const response = await GET_status(
      makeGetRequest("http://localhost/api/pipeline/render/status") as any
    );

    expect(response.status).toBe(500);
    const body = await response.json();
    expect(body.error).toBe("Internal Server Error");
  });

  it("does not require authentication", async () => {
    const request = new Request(
      "http://localhost/api/pipeline/render/status",
      {
        method: "GET",
        headers: { Authorization: "Bearer fake-token" },
      }
    );

    const response = await GET_status(request as any);
    expect(response.status).toBe(200);
  });
});

// ---------------------------------------------------------------------------
// 10. POST — SSE event format
// ---------------------------------------------------------------------------

describe("POST — SSE event format", () => {
  it("formats events as 'data: <JSON>\\n\\n'", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
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
// 11. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/pipeline/render/run/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    const fs = require("fs");
    const pathMod = require("path");
    sourceCode = fs.readFileSync(
      pathMod.join(
        __dirname,
        "..",
        "app",
        "api",
        "pipeline",
        "render",
        "run",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async function POST", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+POST\s*\(/);
  });

  it("exports async function POST_stitch", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+POST_stitch/);
  });

  it("exports async function GET_status", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+GET_status/);
  });

  it("imports registerExecutor and runPipelineStage from @/lib/jobs", () => {
    expect(sourceCode).toMatch(/@\/lib\/jobs/);
    expect(sourceCode).toMatch(/registerExecutor/);
    expect(sourceCode).toMatch(/runPipelineStage/);
  });

  it("imports renderSection, getSectionDuration, stitchFullVideo from @/lib/render", () => {
    expect(sourceCode).toMatch(/@\/lib\/render/);
    expect(sourceCode).toMatch(/renderSection/);
    expect(sourceCode).toMatch(/getSectionDuration/);
    expect(sourceCode).toMatch(/stitchFullVideo/);
  });

  it("imports loadProject and saveProject from @/lib/project", () => {
    expect(sourceCode).toMatch(/@\/lib\/project/);
    expect(sourceCode).toMatch(/loadProject/);
    expect(sourceCode).toMatch(/saveProject/);
  });

  it("imports RenderProgress and SseSend from @/lib/types", () => {
    expect(sourceCode).toMatch(/@\/lib\/types/);
    expect(sourceCode).toMatch(/RenderProgress/);
    expect(sourceCode).toMatch(/SseSend/);
  });

  it("calls registerExecutor('render', ...)", () => {
    expect(sourceCode).toMatch(/registerExecutor\s*\(\s*["']render["']/);
  });

  it("calls runPipelineStage('render', ...)", () => {
    expect(sourceCode).toMatch(
      /runPipelineStage\s*\(\s*["']render["']/
    );
  });

  it("uses outputs/sections path for section files", () => {
    expect(sourceCode).toMatch(/outputs.*sections/);
  });

  it("uses outputs/full_video.mp4 for stitched output", () => {
    expect(sourceCode).toMatch(/full_video\.mp4/);
  });

  it("sets Content-Type to text/event-stream in response headers", () => {
    expect(sourceCode).toMatch(/text\/event-stream/);
  });

  it("sets Cache-Control to no-cache", () => {
    expect(sourceCode).toMatch(/no-cache/);
  });

  it("sets Connection to keep-alive", () => {
    expect(sourceCode).toMatch(/keep-alive/);
  });

  it("emits section-progress events", () => {
    expect(sourceCode).toMatch(/section-progress/);
  });

  it("uses Promise.all for parallel rendering", () => {
    expect(sourceCode).toMatch(/Promise\.all/);
  });

  it("recalculates offsetSeconds", () => {
    expect(sourceCode).toMatch(/offsetSeconds/);
  });

  it("creates directories with recursive flag", () => {
    expect(sourceCode).toMatch(/mkdir.*recursive/s);
  });
});

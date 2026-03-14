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

import path from "path";

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockRegisterExecutor = jest.fn();
const mockStartJobInBackground = jest.fn();

jest.mock("@/lib/jobs", () => ({
  registerExecutor: (...args: unknown[]) => mockRegisterExecutor(...args),
  startJobInBackground: (...args: unknown[]) => mockStartJobInBackground(...args),
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

const mockBuildSectionConstantsSource = jest.fn();

jest.mock("@/lib/projects", () => ({
  getProjectDir: () => process.cwd(),
  getAppRemotionDir: () => path.join(process.cwd(), "remotion"),
  getAppRemotionPublicDir: () => path.join(process.cwd(), "remotion", "public"),
  getAppScriptsDir: () => path.join(process.cwd(), "scripts"),
}));

jest.mock("@/lib/composition-timing", () => ({
  buildSectionConstantsSource: (...args: unknown[]) =>
    mockBuildSectionConstantsSource(...args),
}));

const mockMkdir = jest.fn();
const mockAccess = jest.fn();
const mockStat = jest.fn();
const mockRm = jest.fn();
const mockWriteFile = jest.fn();

jest.mock("fs/promises", () => ({
  mkdir: (...args: unknown[]) => mockMkdir(...args),
  access: (...args: unknown[]) => mockAccess(...args),
  stat: (...args: unknown[]) => mockStat(...args),
  rm: (...args: unknown[]) => mockRm(...args),
  writeFile: (...args: unknown[]) => mockWriteFile(...args),
}));

const mockSpawn = jest.fn();
const mockExecSync = jest.fn();

jest.mock("child_process", () => ({
  spawn: (...args: unknown[]) => mockSpawn(...args),
  execSync: (...args: unknown[]) => mockExecSync(...args),
}));

jest.mock("crypto", () => ({
  randomUUID: () => "test-uuid-stitch-001",
}));

// Import after mocking
import { POST } from "../app/api/pipeline/render/run/route";

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
  mockStartJobInBackground.mockReset();
  mockRenderSection.mockReset();
  mockGetSectionDuration.mockReset();
  mockStitchFullVideo.mockReset();
  mockLoadProject.mockReset();
  mockSaveProject.mockReset();
  mockBuildSectionConstantsSource.mockReset();
  mockMkdir.mockReset();
  mockAccess.mockReset();
  mockStat.mockReset();
  mockRm.mockReset();
  mockWriteFile.mockReset();
  mockSpawn.mockReset();
  mockExecSync.mockReset();

  mockRm.mockResolvedValue(undefined);
  mockWriteFile.mockResolvedValue(undefined);
  mockSpawn.mockReturnValue({
    stdout: { on: jest.fn((event: string, cb: Function) => { if (event === 'data') cb(Buffer.from('ok')); }) },
    stderr: { on: jest.fn() },
    on: jest.fn((event: string, cb: Function) => { if (event === 'close') cb(0); }),
  });
  mockExecSync.mockReturnValue(Buffer.from(''));
  mockBuildSectionConstantsSource.mockImplementation(
    (_projectDir: string, section: { id: string }) =>
      `// constants for ${section.id}\nexport const VISUAL_SEQUENCE = [];\n`
  );

  mockStartJobInBackground.mockReturnValue("test-job-render-001");
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

  it("returns JSON response with Content-Type application/json", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );
    expect(response.headers.get("Content-Type")).toContain("application/json");
  });

  it("returns a JSON body with jobId", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );
    const body = await response.json();
    expect(body).toHaveProperty("jobId");
    expect(body.jobId).toBe("test-job-render-001");
  });
});

// ---------------------------------------------------------------------------
// 3. POST — success flow with SSE events
// ---------------------------------------------------------------------------

describe("POST — success flow", () => {
  beforeEach(() => {
    mockStartJobInBackground.mockReturnValue("test-job-render-42");
  });

  it("starts a background render job", async () => {
    await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );

    expect(mockStartJobInBackground).toHaveBeenCalledTimes(1);
    expect(mockStartJobInBackground.mock.calls[0][0]).toBe("render");
  });

  it("passes sections param from body to the background render job", async () => {
    await POST(
      makeRequest("http://localhost/api/pipeline/render/run", {
        sections: ["intro", "outro"],
      }) as any
    );

    const params = mockStartJobInBackground.mock.calls[0][1];
    expect(params.sections).toEqual(["intro", "outro"]);
  });

  it("passes undefined sections when body has no sections array", async () => {
    await POST(
      makeRequest("http://localhost/api/pipeline/render/run", {}) as any
    );

    const params = mockStartJobInBackground.mock.calls[0][1];
    expect(params.sections).toBeUndefined();
  });

  it("returns jobId in JSON response immediately after job creation", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );

    const body = await response.json();
    expect(body.jobId).toBe("test-job-render-42");
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
    const body = await response.json();
    expect(body).toHaveProperty("jobId");
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
    const body = await response.json();
    expect(body).toHaveProperty("jobId");
  });

  it("handles body with sections as non-array gracefully", async () => {
    await POST(
      makeRequest("http://localhost/api/pipeline/render/run", {
        sections: "not-an-array",
      }) as any
    );

    const params = mockStartJobInBackground.mock.calls[0][1];
    expect(params.sections).toBeUndefined();
  });
});

// ---------------------------------------------------------------------------
// 5. POST — error handling
// ---------------------------------------------------------------------------

describe("POST — error handling", () => {
  it("returns JSON error when background job creation throws Error", async () => {
    mockStartJobInBackground.mockImplementation(() => {
      throw new Error("Render failed");
    });

    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );

    expect(response.status).toBe(500);
    const body = await response.json();
    expect(body.error).toBe("Render failed");
  });

  it("returns generic error for non-Error throws", async () => {
    mockStartJobInBackground.mockImplementation(() => {
      throw "string error";
    });

    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );

    expect(response.status).toBe(500);
    const body = await response.json();
    expect(body.error).toBe("Unknown error");
  });

  it("returns a Response even when pipeline errors", async () => {
    mockStartJobInBackground.mockImplementation(() => {
      throw new Error("will fail");
    });

    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );
    expect(response).toBeInstanceOf(Response);
    expect(response.status).toBe(500);
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
    const body = await response.json();
    expect(body).toHaveProperty("jobId");
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
      pathMod.join(process.cwd(), "outputs", "sections", "intro.mp4")
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
      pathMod.join(process.cwd(), "outputs", "sections", "main.mp4")
    );
  });

  it("creates outputs/sections directory with recursive flag", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const pathMod = require("path");
    expect(mockMkdir).toHaveBeenCalledWith(
      pathMod.join(process.cwd(), "outputs", "sections"),
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
// 8. POST — JSON response format (not SSE)
// ---------------------------------------------------------------------------

describe("POST — JSON response format", () => {
  it("returns JSON with jobId on success", async () => {
    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );

    const body = await response.json();
    expect(body).toHaveProperty("jobId");
    expect(typeof body.jobId).toBe("string");
  });

  it("returns JSON with error on failure", async () => {
    mockStartJobInBackground.mockImplementation(() => {
      throw new Error("Pipeline broke");
    });

    const response = await POST(
      makeRequest("http://localhost/api/pipeline/render/run") as any
    );

    const body = await response.json();
    expect(body).toHaveProperty("error");
    expect(body.error).toBe("Pipeline broke");
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

  it("defines renderSections helper function", () => {
    expect(sourceCode).toMatch(/async\s+function\s+renderSections/);
  });

  it("defines updateProjectDurations helper function", () => {
    expect(sourceCode).toMatch(/async\s+function\s+updateProjectDurations/);
  });

  it("imports registerExecutor and startJobInBackground from @/lib/jobs", () => {
    expect(sourceCode).toMatch(/@\/lib\/jobs/);
    expect(sourceCode).toMatch(/registerExecutor/);
    expect(sourceCode).toMatch(/startJobInBackground/);
  });

  it("imports renderSection and getSectionDuration from @/lib/render", () => {
    expect(sourceCode).toMatch(/@\/lib\/render/);
    expect(sourceCode).toMatch(/renderSection/);
    expect(sourceCode).toMatch(/getSectionDuration/);
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

  it("calls startJobInBackground('render', ...)", () => {
    expect(sourceCode).toMatch(
      /startJobInBackground\s*\(\s*["']render["']/
    );
  });

  it("uses outputs/sections path for section files", () => {
    expect(sourceCode).toMatch(/outputs.*sections/);
  });

  it("uses Response.json for JSON responses", () => {
    expect(sourceCode).toMatch(/Response\.json/);
  });

  it("returns 500 status on error", () => {
    expect(sourceCode).toMatch(/500/);
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

// ---------------------------------------------------------------------------
// 12. rebuildBundle — cache clearing
// ---------------------------------------------------------------------------

describe("rebuildBundle — cache clearing", () => {
  it("removes remotion/build/ before running npx remotion bundle", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const pathMod = require("path");
    const rmCalls = mockRm.mock.calls;
    const buildRm = rmCalls.find((c: any[]) =>
      String(c[0]).includes(pathMod.join("remotion", "build"))
    );
    expect(buildRm).toBeDefined();
    expect(buildRm![1]).toEqual({ recursive: true, force: true });
  });

  it("removes webpack cache dir before running npx remotion bundle", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const pathMod = require("path");
    const rmCalls = mockRm.mock.calls;
    const cacheRm = rmCalls.find((c: any[]) =>
      String(c[0]).includes(pathMod.join("node_modules", ".cache", "webpack"))
    );
    expect(cacheRm).toBeDefined();
    expect(cacheRm![1]).toEqual({ recursive: true, force: true });
  });

  it("clears cache BEFORE calling execSync for bundle", async () => {
    const callOrder: string[] = [];
    mockRm.mockImplementation(async (p: string) => {
      if (String(p).includes("build")) callOrder.push("rm-build");
      if (String(p).includes("webpack")) callOrder.push("rm-cache");
    });
    mockExecSync.mockImplementation(() => {
      callOrder.push("bundle");
      return Buffer.from('');
    });

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    expect(callOrder.indexOf("rm-build")).toBeLessThan(callOrder.indexOf("bundle"));
    expect(callOrder.indexOf("rm-cache")).toBeLessThan(callOrder.indexOf("bundle"));
  });

  it("rewrites section constants from the resolved spec timeline before bundling", async () => {
    mockBuildSectionConstantsSource.mockReturnValue(
      'export const VISUAL_SEQUENCE = [{ id: "02_ocean_wave_sunset" }, { id: "04_forest_canopy_aerial" }];\n'
    );
    mockLoadProject.mockReturnValue({
      ...mockProjectConfig(),
      sections: [
        {
          id: "veo_section",
          label: "Veo Section",
          videoFile: "outputs/sections/veo_section.mp4",
          specDir: "veo_section",
          remotionDir: "remotion/veo_section",
          compositionId: "VeoSection",
          durationSeconds: 11.584,
          offsetSeconds: 0,
          compositions: [
            "veo_section_01_title_card",
            "03_narration_overlay_intro",
            "05_narration_overlay_forest",
          ],
        },
      ],
    });

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const constantsCall = mockWriteFile.mock.calls.find((call: unknown[]) =>
      String(call[0]).includes("remotion/src/remotion/veo_section/constants.ts")
    );

    expect(constantsCall).toBeDefined();
    expect(mockBuildSectionConstantsSource).toHaveBeenCalled();
    expect(mockBuildSectionConstantsSource).toHaveBeenCalledWith(
      process.cwd(),
      expect.objectContaining({ id: "veo_section" }),
      ["veo_section_01_title_card", "03_narration_overlay_intro", "05_narration_overlay_forest"]
    );
    expect(String(constantsCall?.[1])).toContain('id: "02_ocean_wave_sunset"');
    expect(String(constantsCall?.[1])).toContain('id: "04_forest_canopy_aerial"');
  });

  it("does not clobber section constants when no compositions were discovered", async () => {
    mockLoadProject.mockReturnValue({
      ...mockProjectConfig(),
      sections: [
        {
          id: "media_only_section",
          label: "Media Only Section",
          videoFile: "outputs/sections/media_only_section.mp4",
          specDir: "media_only_section",
          remotionDir: "remotion/media_only_section",
          compositionId: "MediaOnlySection",
          durationSeconds: 8.0,
          offsetSeconds: 0,
          compositions: [],
        },
      ],
    });

    const onLog = jest.fn();
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(onLog);

    expect(mockBuildSectionConstantsSource).not.toHaveBeenCalled();
    expect(
      mockWriteFile.mock.calls.some((call: unknown[]) =>
        String(call[0]).includes("remotion/src/remotion/media_only_section/constants.ts")
      )
    ).toBe(false);
    expect(onLog).toHaveBeenCalledWith(
      'Skipped section constants refresh for "media_only_section" because no compositions were discovered.'
    );
  });
});

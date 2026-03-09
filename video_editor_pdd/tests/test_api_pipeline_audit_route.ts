/**
 * Tests for app/api/pipeline/audit/run/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_pipeline_audit_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. POST /api/pipeline/audit/run — accepts { sections?: string[] }, defaults to all.
 *      Launches one agent per section concurrently. Returns SSE stream with { jobId }.
 *   2. Each per-section agent: resolves a spec-local audit timestamp → extracts
 *      a frame from the rendered section video when available (or falls back to
 *      renderStill()) → calls runClaudeAnalysis() comparing the still PNG against
 *      the spec file → writes
 *      specs/{specDir}/AUDIT_{specName}.md with pass/fail verdict and details.
 *   3. GET /api/pipeline/audit/results — returns { sections: AuditSectionResult[] }
 *      with passCount, failCount, status ('done'|'pending'|'error'), and specs array.
 *   4. No authentication required.
 *   5. Still output path: outputs/audit/{sectionId}/{specName}_frame.png
 *   6. Audit report path: specs/{specDir}/AUDIT_{specName}.md
 *   7. Concurrent agents: Promise.all(sections.map(...))
 *   8. Emit per-section events: { type: 'audit-section', sectionId, status, passCount, failCount }
 *   9. GET parses AUDIT_*.md files to extract verdicts (## Verdict heading)
 *  10. registerExecutor('audit', ...) called at module load time
 *  11. Audit markdown format: ## Verdict\n{pass|fail}\n## Summary\n{text}
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

const mockRenderStill = jest.fn();
const mockExtractFrameAtTime = jest.fn();

jest.mock("@/lib/render", () => ({
  renderStill: (...args: unknown[]) => mockRenderStill(...args),
  extractFrameAtTime: (...args: unknown[]) => mockExtractFrameAtTime(...args),
}));

const mockRunClaudeAnalysis = jest.fn();

jest.mock("@/lib/claude", () => ({
  runClaudeAnalysis: (...args: unknown[]) => mockRunClaudeAnalysis(...args),
}));

const mockLoadProject = jest.fn();

jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
}));

const mockReaddirSync = jest.fn();
const mockReadFileSync = jest.fn();
const mockWriteFileSync = jest.fn();
const mockMkdirSync = jest.fn();
const mockExistsSync = jest.fn();

jest.mock("fs", () => ({
  readdirSync: (...args: unknown[]) => mockReaddirSync(...args),
  readFileSync: (...args: unknown[]) => mockReadFileSync(...args),
  writeFileSync: (...args: unknown[]) => mockWriteFileSync(...args),
  mkdirSync: (...args: unknown[]) => mockMkdirSync(...args),
  existsSync: (...args: unknown[]) => mockExistsSync(...args),
}));

// Import after mocking
import { POST } from "../app/api/pipeline/audit/run/route";
import { GET } from "../app/api/pipeline/audit/results/route";

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

function makeRequest(body?: object): Request {
  if (body) {
    return new Request("http://localhost/api/pipeline/audit/run", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(body),
    });
  }
  return new Request("http://localhost/api/pipeline/audit/run", {
    method: "POST",
  });
}

function makeGetRequest(): Request {
  return new Request("http://localhost/api/pipeline/audit/results", {
    method: "GET",
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
      // Handle both string and Uint8Array values (TransformStream may pass strings)
      const chunk =
        typeof value === "string"
          ? value
          : decoder.decode(value, { stream: true });
      buffer += chunk;
      const parts = buffer.split("\n\n");
      buffer = parts.pop() ?? "";
      for (const part of parts) {
        const dataLine =
          part
            .split("\n")
            .find((line) => line.startsWith("data:"))
            ?.replace(/^data:\s*/, "") ?? "";
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

// ---------------------------------------------------------------------------
// Setup
// ---------------------------------------------------------------------------

beforeEach(() => {
  mockRunPipelineStage.mockReset();
  mockRenderStill.mockReset();
  mockExtractFrameAtTime.mockReset();
  mockRunClaudeAnalysis.mockReset();
  mockLoadProject.mockReset();
  mockReaddirSync.mockReset();
  mockReadFileSync.mockReset();
  mockWriteFileSync.mockReset();
  mockMkdirSync.mockReset();
  mockExistsSync.mockReset();

  mockRunPipelineStage.mockResolvedValue("test-job-audit-001");
  mockRenderStill.mockResolvedValue(undefined);
  mockExtractFrameAtTime.mockResolvedValue(undefined);
  mockRunClaudeAnalysis.mockResolvedValue({
    severity: "pass",
    fixType: "none",
    technicalAssessment: "Frame matches spec",
    suggestedFixes: [],
    confidence: 0.95,
  });
  mockLoadProject.mockReturnValue(mockProjectConfig());
  mockReaddirSync.mockReturnValue([]);
  mockReadFileSync.mockReturnValue("**Timestamp:** 0:00 - 0:03\n");
  mockExistsSync.mockReturnValue(true);
  mockMkdirSync.mockReturnValue(undefined);
  mockWriteFileSync.mockReturnValue(undefined);
});

// ---------------------------------------------------------------------------
// 1. registerExecutor — module load side effect
// ---------------------------------------------------------------------------

describe("registerExecutor at module load", () => {
  it("registers executor for 'audit' stage", () => {
    expect(registerCallArgs.stage).toBe("audit");
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
    const response = await POST(makeRequest() as any);
    expect(response).toBeInstanceOf(Response);
  });

  it("sets Content-Type to text/event-stream", async () => {
    const response = await POST(makeRequest() as any);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("sets Cache-Control to no-cache", async () => {
    const response = await POST(makeRequest() as any);
    expect(response.headers.get("Cache-Control")).toBe("no-cache");
  });

  it("sets Connection to keep-alive", async () => {
    const response = await POST(makeRequest() as any);
    expect(response.headers.get("Connection")).toBe("keep-alive");
  });

  it("returns a ReadableStream body", async () => {
    const response = await POST(makeRequest() as any);
    expect(response.body).toBeInstanceOf(ReadableStream);
  });
});

// ---------------------------------------------------------------------------
// 3. POST — success flow with SSE events
// ---------------------------------------------------------------------------

describe("POST — success flow", () => {
  beforeEach(() => {
    mockRunPipelineStage.mockResolvedValue("test-job-audit-42");
  });

  it("calls runPipelineStage with 'audit' stage", async () => {
    await POST(makeRequest() as any);
    await flushPromises();

    expect(mockRunPipelineStage).toHaveBeenCalledTimes(1);
    expect(mockRunPipelineStage.mock.calls[0][0]).toBe("audit");
  });

  it("passes sections param from body to runPipelineStage", async () => {
    await POST(
      makeRequest({ sections: ["intro", "outro"] }) as any
    );
    await flushPromises();

    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.sections).toEqual(["intro", "outro"]);
  });

  it("passes undefined sections when body has no sections array", async () => {
    await POST(makeRequest({}) as any);
    await flushPromises();

    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.sections).toBeUndefined();
  });

  it("passes a send function to runPipelineStage", async () => {
    await POST(makeRequest() as any);
    await flushPromises();

    expect(typeof mockRunPipelineStage.mock.calls[0][2]).toBe("function");
  });

  it("emits jobId event after runPipelineStage resolves", async () => {
    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const jobEvent = events.find((e: any) => e.jobId) as any;
    expect(jobEvent).toBeDefined();
    expect(jobEvent.jobId).toBe("test-job-audit-42");
  });

  it("does not crash if the client disconnects before the audit job finishes", async () => {
    let resolveStage: ((jobId: string) => void) | null = null;
    mockRunPipelineStage.mockImplementation(
      () =>
        new Promise<string>((resolve) => {
          resolveStage = resolve;
        })
    );

    const response = await POST(makeRequest() as any);
    await response.body!.cancel();

    resolveStage?.("test-job-after-cancel");
    await flushPromises();

    expect(mockRunPipelineStage).toHaveBeenCalledTimes(1);
  });
});

// ---------------------------------------------------------------------------
// 4. POST — body parameter handling
// ---------------------------------------------------------------------------

describe("POST — body parameter handling", () => {
  it("works with no body (audits all sections)", async () => {
    const response = await POST(makeRequest() as any);
    expect(response).toBeInstanceOf(Response);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("accepts specific sections array", async () => {
    const response = await POST(
      makeRequest({ sections: ["intro", "outro"] }) as any
    );
    expect(response).toBeInstanceOf(Response);
  });

  it("handles invalid body gracefully (non-JSON)", async () => {
    const request = new Request("http://localhost/api/pipeline/audit/run", {
      method: "POST",
      body: "not json",
    });

    const response = await POST(request as any);
    expect(response).toBeInstanceOf(Response);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });
});

// ---------------------------------------------------------------------------
// 5. POST — error handling
// ---------------------------------------------------------------------------

describe("POST — error handling", () => {
  it("emits error event when runPipelineStage rejects with Error", async () => {
    mockRunPipelineStage.mockRejectedValue(new Error("Audit failed"));

    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const errorEvent = events.find((e: any) => e.message === "Audit failed") as any;
    expect(errorEvent).toBeDefined();
    expect(errorEvent.message).toBe("Audit failed");
  });

  it("emits generic error for non-Error throws", async () => {
    mockRunPipelineStage.mockRejectedValue("string error");

    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const errorEvent = events.find((e: any) => e.message === "Unknown error") as any;
    expect(errorEvent).toBeDefined();
    expect(errorEvent.message).toBe("Unknown error");
  });

  it("still returns SSE response even when pipeline will error", async () => {
    mockRunPipelineStage.mockRejectedValue(new Error("will fail"));

    const response = await POST(makeRequest() as any);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });
});

// ---------------------------------------------------------------------------
// 6. POST — no authentication required
// ---------------------------------------------------------------------------

describe("POST — no authentication required", () => {
  it("does not require authorization headers", async () => {
    const request = new Request("http://localhost/api/pipeline/audit/run", {
      method: "POST",
      headers: { Authorization: "Bearer fake-token" },
    });

    const response = await POST(request as any);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("works with minimal request (no body, no auth)", async () => {
    const response = await POST(makeRequest() as any);
    expect(response).toBeInstanceOf(Response);
  });
});

// ---------------------------------------------------------------------------
// 7. Audit executor factory — registered with pipeline job system
// ---------------------------------------------------------------------------

describe("audit executor factory", () => {
  it("returns an async function when called with params and send", () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    expect(typeof executor).toBe("function");
  });

  it("calls loadProject() to get section list", async () => {
    mockReaddirSync.mockReturnValue([]);

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    expect(mockLoadProject).toHaveBeenCalled();
  });

  it("audits all sections when params.sections is not provided", async () => {
    // Each section has one spec file
    mockReaddirSync.mockReturnValue(["visual.md"]);

    const sendFn = jest.fn();
    const executor = registerCallArgs.factory({}, sendFn);
    await executor(jest.fn());

    // 3 sections → should get 3 running + 3 done events
    const runningEvents = sendFn.mock.calls.filter(
      (call: any[]) =>
        call[0]?.type === "audit-section" && call[0]?.status === "running"
    );
    expect(runningEvents.length).toBe(3);
  });

  it("audits only specified sections when params.sections is provided", async () => {
    mockReaddirSync.mockReturnValue(["visual.md"]);

    const sendFn = jest.fn();
    const executor = registerCallArgs.factory(
      { sections: ["intro", "outro"] },
      sendFn
    );
    await executor(jest.fn());

    const runningEvents = sendFn.mock.calls.filter(
      (call: any[]) =>
        call[0]?.type === "audit-section" && call[0]?.status === "running"
    );
    expect(runningEvents.length).toBe(2);
  });

  it("emits 'running' status before processing each section", async () => {
    mockReaddirSync.mockReturnValue(["visual.md"]);

    const sendFn = jest.fn();
    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      sendFn
    );
    await executor(jest.fn());

    const runningEvent = sendFn.mock.calls.find(
      (call: any[]) =>
        call[0]?.type === "audit-section" &&
        call[0]?.status === "running" &&
        call[0]?.sectionId === "intro"
    );
    expect(runningEvent).toBeDefined();
    expect(runningEvent![0].passCount).toBe(0);
    expect(runningEvent![0].failCount).toBe(0);
  });

  it("emits 'done' status with passCount and failCount after section completes", async () => {
    mockReaddirSync.mockReturnValue(["visual.md", "overlay.md"]);
    mockRunClaudeAnalysis
      .mockResolvedValueOnce({
        severity: "pass",
        fixType: "none",
        technicalAssessment: "All good",
        suggestedFixes: [],
        confidence: 0.9,
      })
      .mockResolvedValueOnce({
        severity: "major",
        fixType: "remotion",
        technicalAssessment: "Text clipped",
        suggestedFixes: ["Fix padding"],
        confidence: 0.85,
      });

    const sendFn = jest.fn();
    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      sendFn
    );
    await executor(jest.fn());

    const doneEvent = sendFn.mock.calls.find(
      (call: any[]) =>
        call[0]?.type === "audit-section" &&
        call[0]?.status === "done" &&
        call[0]?.sectionId === "intro"
    );
    expect(doneEvent).toBeDefined();
    expect(doneEvent![0].passCount).toBe(1);
    expect(doneEvent![0].failCount).toBe(1);
  });

  it("emits 'error' status when auditSection throws", async () => {
    mockReaddirSync.mockImplementation(() => {
      throw new Error("ENOENT: no such directory");
    });

    const sendFn = jest.fn();
    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      sendFn
    );
    await executor(jest.fn());

    const errorEvent = sendFn.mock.calls.find(
      (call: any[]) =>
        call[0]?.type === "audit-section" &&
        call[0]?.status === "error" &&
        call[0]?.sectionId === "intro"
    );
    expect(errorEvent).toBeDefined();
    expect(errorEvent![0].passCount).toBe(0);
    expect(errorEvent![0].failCount).toBe(0);
  });

  it("runs sections concurrently with Promise.all", async () => {
    // Track invocation timing to verify concurrency
    let concurrentCount = 0;
    let maxConcurrent = 0;

    mockReaddirSync.mockReturnValue(["visual.md"]);
    mockExtractFrameAtTime.mockImplementation(async () => {
      concurrentCount++;
      maxConcurrent = Math.max(maxConcurrent, concurrentCount);
      await new Promise((resolve) => setTimeout(resolve, 10));
      concurrentCount--;
    });

    const sendFn = jest.fn();
    const executor = registerCallArgs.factory({}, sendFn);
    await executor(jest.fn());

    // With 3 sections running in parallel, max concurrent should be > 1
    expect(maxConcurrent).toBeGreaterThan(1);
  });

  it("extracts audit frames from the rendered section video when available", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["visual.md"]);

    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      jest.fn()
    );
    await executor(jest.fn());

    expect(mockExtractFrameAtTime).toHaveBeenCalledTimes(1);
    expect(mockRenderStill).not.toHaveBeenCalled();
    const pathMod = require("path");
    expect(mockExtractFrameAtTime.mock.calls[0][0]).toBe(
      pathMod.join(process.cwd(), "output", "sections", "intro.mp4")
    );
    expect(mockExtractFrameAtTime.mock.calls[0][1]).toBe(2.25);
    expect(mockExtractFrameAtTime.mock.calls[0][2]).toBe(
      pathMod.join("outputs", "audit", "intro", "visual_frame.png")
    );
  });

  it("falls back to renderStill when the rendered section video is unavailable", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["visual.md"]);
    const pathMod = require("path");
    const specDir = pathMod.join(process.cwd(), "specs", "intro");
    mockExistsSync.mockImplementation((candidate: string) => candidate === specDir);

    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      jest.fn()
    );
    await executor(jest.fn());

    expect(mockExtractFrameAtTime).not.toHaveBeenCalled();
    expect(mockRenderStill).toHaveBeenCalledTimes(1);
    expect(mockRenderStill.mock.calls[0][0]).toBe("IntroComposition");
    expect(mockRenderStill.mock.calls[0][1]).toBe(67);
    expect(mockRenderStill.mock.calls[0][2]).toBe(
      pathMod.join("outputs", "audit", "intro", "visual_frame.png")
    );
  });

  it("calls runClaudeAnalysis for each spec file", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["visual.md", "overlay.md"]);

    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      jest.fn()
    );
    await executor(jest.fn());

    expect(mockRunClaudeAnalysis).toHaveBeenCalledTimes(2);
  });

  it("writes audit report with correct format", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["visual.md"]);
    mockRunClaudeAnalysis.mockResolvedValue({
      severity: "pass",
      fixType: "none",
      technicalAssessment: "Frame matches spec perfectly",
      suggestedFixes: [],
      confidence: 0.95,
    });

    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      jest.fn()
    );
    await executor(jest.fn());

    expect(mockWriteFileSync).toHaveBeenCalledTimes(1);

    const pathMod = require("path");
    const writePath = mockWriteFileSync.mock.calls[0][0];
    expect(writePath).toBe(
      pathMod.join(process.cwd(), "specs", "intro", "AUDIT_visual.md")
    );

    const content = mockWriteFileSync.mock.calls[0][1];
    expect(content).toContain("## Verdict");
    expect(content).toContain("pass");
    expect(content).toContain("## Summary");
    expect(content).toContain("Frame matches spec perfectly");
  });

  it("writes 'fail' verdict when severity is not 'pass'", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["visual.md"]);
    mockRunClaudeAnalysis.mockResolvedValue({
      severity: "major",
      fixType: "remotion",
      technicalAssessment: "Text is clipped",
      suggestedFixes: ["Fix padding"],
      confidence: 0.85,
    });

    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      jest.fn()
    );
    await executor(jest.fn());

    const content = mockWriteFileSync.mock.calls[0][1];
    expect(content).toContain("## Verdict\nfail");
  });

  it("creates output directory with recursive flag", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["visual.md"]);

    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      jest.fn()
    );
    await executor(jest.fn());

    expect(mockMkdirSync).toHaveBeenCalledWith(
      expect.any(String),
      { recursive: true }
    );
  });

  it("filters out AUDIT_ files from spec directory listing", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue([
      "visual.md",
      "AUDIT_visual.md",
      "overlay.md",
      "AUDIT_overlay.md",
    ]);

    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      jest.fn()
    );
    await executor(jest.fn());

    // Should only process visual.md and overlay.md, not AUDIT_ files
    expect(mockExtractFrameAtTime).toHaveBeenCalledTimes(2);
    expect(mockRunClaudeAnalysis).toHaveBeenCalledTimes(2);
  });

  it("filters out non-.md files from spec directory listing", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["visual.md", "image.png", "data.json"]);

    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      jest.fn()
    );
    await executor(jest.fn());

    // Should only process visual.md
    expect(mockExtractFrameAtTime).toHaveBeenCalledTimes(1);
  });

  it("uses onLog to report rendering progress", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["visual.md"]);

    const onLog = jest.fn();
    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      jest.fn()
    );
    await executor(onLog);

    expect(onLog).toHaveBeenCalled();
    const logMessages = onLog.mock.calls.map((c: any[]) => c[0]);
    expect(logMessages.some((m: string) => m.includes("[audit]"))).toBe(true);
    expect(logMessages.some((m: string) => m.includes("intro"))).toBe(true);
  });

  it("handles section with no spec files gracefully", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // just intro
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue([]);

    const sendFn = jest.fn();
    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      sendFn
    );
    await executor(jest.fn());

    // Should emit done with 0 counts
    const doneEvent = sendFn.mock.calls.find(
      (call: any[]) =>
        call[0]?.type === "audit-section" &&
        call[0]?.status === "done" &&
        call[0]?.sectionId === "intro"
    );
    expect(doneEvent).toBeDefined();
    expect(doneEvent![0].passCount).toBe(0);
    expect(doneEvent![0].failCount).toBe(0);
  });

  it("still output path follows outputs/audit/{sectionId}/{specName}_frame.png", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[1]]; // main
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["transition.md"]);

    const executor = registerCallArgs.factory(
      { sections: ["main"] },
      jest.fn()
    );
    await executor(jest.fn());

    const pathMod = require("path");
    expect(mockExtractFrameAtTime.mock.calls[0][2]).toBe(
      pathMod.join("outputs", "audit", "main", "transition_frame.png")
    );
  });

  it("audit report path follows specs/{specDir}/AUDIT_{specName}.md", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[1]]; // main
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["transition.md"]);

    const executor = registerCallArgs.factory(
      { sections: ["main"] },
      jest.fn()
    );
    await executor(jest.fn());

    const pathMod = require("path");
    expect(mockWriteFileSync.mock.calls[0][0]).toBe(
      pathMod.join(process.cwd(), "specs", "main", "AUDIT_transition.md")
    );
  });

  it("writes audit report into section.specDir even when it differs from section.id", async () => {
    const config = mockProjectConfig();
    config.sections = [
      {
        ...config.sections[0],
        id: "intro",
        specDir: "cold_open",
      },
    ];
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["title_card.md"]);

    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      jest.fn()
    );
    await executor(jest.fn());

    const pathMod = require("path");
    expect(mockWriteFileSync.mock.calls[0][0]).toBe(
      pathMod.join(process.cwd(), "specs", "cold_open", "AUDIT_title_card.md")
    );
  });

  it("uses a late-window timestamp sample rather than the section midpoint", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[1]]; // main
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["visual.md"]);
    mockReadFileSync.mockReturnValue("**Timestamp:** 0:12 - 0:18\n");

    const executor = registerCallArgs.factory(
      { sections: ["main"] },
      jest.fn()
    );
    await executor(jest.fn());

    expect(mockExtractFrameAtTime.mock.calls[0][1]).toBe(16.5);
  });

  it("falls back to animation-sequence frame ranges when timestamp metadata is missing", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // intro
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["visual.md"]);
    mockReadFileSync.mockReturnValue(`
## Animation Sequence
1. Frame 30-90: Intro.
2. Frame 90-150: Hold.
`);

    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      jest.fn()
    );
    await executor(jest.fn());

    expect(mockExtractFrameAtTime.mock.calls[0][1]).toBe(4);
  });

  it("prefers a hold frame range when the spec provides both timestamps and animation ranges", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // intro
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["visual.md"]);
    mockReadFileSync.mockReturnValue(`
**Timestamp:** 0:00 - 0:03

## Animation Sequence
1. Frame 0-15: Fade in.
2. Frame 15-45: Title reveal.
3. Frame 45-65: Rule expansion.
4. Frame 65-90: Hold — all elements static at full opacity.
`);

    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      jest.fn()
    );
    await executor(jest.fn());

    expect(mockExtractFrameAtTime.mock.calls[0][1]).toBeCloseTo(77.5 / 30);
  });

  it("offsets animation-sequence frame ranges by the spec timestamp window", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // intro
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["visual.md"]);
    mockReadFileSync.mockReturnValue(`
**Timestamp:** 0:03 - 0:08

## Animation Sequence
1. Frame 0-20: Circle appears.
2. Frame 20-40: Hold at full size.
3. Frame 40-60: Pulse.
4. Frame 60-90: Circle holds steady.
5. Frame 90-150: Circle remains on screen.
`);

    const executor = registerCallArgs.factory(
      { sections: ["intro"] },
      jest.fn()
    );
    await executor(jest.fn());

    expect(mockExtractFrameAtTime.mock.calls[0][1]).toBeCloseTo(7);
  });

  it("clamps animation-sequence offsets to the end of the timestamp window", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[1]]; // main
    mockLoadProject.mockReturnValue(config);
    mockReaddirSync.mockReturnValue(["visual.md"]);
    mockReadFileSync.mockReturnValue(`
**Timestamp:** 0:03 - 0:06

## Animation Sequence
1. Frame 0-120: Long clip that overruns the timestamp window.
`);

    const executor = registerCallArgs.factory(
      { sections: ["main"] },
      jest.fn()
    );
    await executor(jest.fn());

    expect(mockExtractFrameAtTime.mock.calls[0][1]).toBeCloseTo(4.5);
  });
});

// ---------------------------------------------------------------------------
// 8. GET — audit results response shape
// ---------------------------------------------------------------------------

describe("GET — audit results response", () => {
  it("returns 200 status on success", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReaddirSync.mockReturnValue([]);

    const response = await GET(makeGetRequest() as any);
    expect(response.status).toBe(200);
  });

  it("returns { sections: [...] } in response body", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReaddirSync.mockReturnValue([]);

    const response = await GET(makeGetRequest() as any);
    const body = await response.json();

    expect(body.sections).toBeDefined();
    expect(Array.isArray(body.sections)).toBe(true);
  });

  it("returns one result per section from project config", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReaddirSync.mockReturnValue([]);

    const response = await GET(makeGetRequest() as any);
    const body = await response.json();

    expect(body.sections.length).toBe(3);
    const ids = body.sections.map((s: any) => s.sectionId);
    expect(ids).toEqual(["intro", "main", "outro"]);
  });

  it("returns AuditSectionResult shape for each section", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReaddirSync.mockReturnValue([]);

    const response = await GET(makeGetRequest() as any);
    const body = await response.json();

    for (const section of body.sections) {
      expect(typeof section.sectionId).toBe("string");
      expect(typeof section.passCount).toBe("number");
      expect(typeof section.failCount).toBe("number");
      expect(["done", "pending", "error"]).toContain(section.status);
      expect(Array.isArray(section.specs)).toBe(true);
    }
  });
});

// ---------------------------------------------------------------------------
// 9. GET — parses audit markdown files correctly
// ---------------------------------------------------------------------------

describe("GET — audit markdown parsing", () => {
  it("parses pass verdict from AUDIT_ files", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReaddirSync.mockReturnValue(["AUDIT_visual.md"]);
    mockReadFileSync.mockReturnValue(
      "## Verdict\npass\n## Summary\nFrame matches spec\n"
    );

    const response = await GET(makeGetRequest() as any);
    const body = await response.json();

    const intro = body.sections[0];
    expect(intro.specs.length).toBe(1);
    expect(intro.specs[0].verdict).toBe("PASS");
    expect(intro.specs[0].summary).toBe("Frame matches spec");
    expect(intro.specs[0].specName).toBe("visual");
    expect(intro.passCount).toBe(1);
    expect(intro.failCount).toBe(0);
  });

  it("parses fail verdict from AUDIT_ files", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReaddirSync.mockReturnValue(["AUDIT_visual.md"]);
    mockReadFileSync.mockReturnValue(
      "## Verdict\nfail\n## Summary\nText is clipped on right edge\n"
    );

    const response = await GET(makeGetRequest() as any);
    const body = await response.json();

    const intro = body.sections[0];
    expect(intro.specs[0].verdict).toBe("FAIL");
    expect(intro.specs[0].summary).toBe("Text is clipped on right edge");
    expect(intro.passCount).toBe(0);
    expect(intro.failCount).toBe(1);
  });

  it("includes specName in each spec result", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReaddirSync.mockReturnValue(["AUDIT_visual.md"]);
    mockReadFileSync.mockReturnValue(
      "## Verdict\npass\n## Summary\nOK\n"
    );

    const response = await GET(makeGetRequest() as any);
    const body = await response.json();

    expect(body.sections[0].specs[0].specName).toBe("visual");
  });

  it("handles multiple audit files per section", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReaddirSync.mockReturnValue([
      "AUDIT_visual.md",
      "AUDIT_overlay.md",
      "visual.md",
      "overlay.md",
    ]);
    mockReadFileSync
      .mockReturnValueOnce("## Verdict\npass\n## Summary\nAll good\n")
      .mockReturnValueOnce("## Verdict\nfail\n## Summary\nOverlay off\n");

    const response = await GET(makeGetRequest() as any);
    const body = await response.json();

    const intro = body.sections[0];
    expect(intro.specs.length).toBe(2);
    expect(intro.passCount).toBe(1);
    expect(intro.failCount).toBe(1);
  });

  it("handles parse errors gracefully with fail verdict", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReaddirSync.mockReturnValue(["AUDIT_broken.md"]);
    mockReadFileSync.mockReturnValue("invalid markdown content");

    const response = await GET(makeGetRequest() as any);
    const body = await response.json();

    const intro = body.sections[0];
    expect(intro.specs.length).toBe(1);
    expect(intro.specs[0].verdict).toBe("FAIL");
    expect(intro.specs[0].summary).toBe("Error parsing audit report");
    expect(intro.failCount).toBe(1);
  });

  it("reads audit files from specs/{specDir} when project.json omits the specs/ prefix", async () => {
    const config = mockProjectConfig();
    config.sections = [
      {
        ...config.sections[0],
        specDir: "cold_open",
      },
    ];
    mockLoadProject.mockReturnValue(config);

    const pathMod = require("path");
    const specDir = pathMod.join(process.cwd(), "specs", "cold_open");
    const specPath = pathMod.join(specDir, "title_card.md");
    const auditPath = pathMod.join(specDir, "AUDIT_title_card.md");

    mockExistsSync.mockImplementation((candidate: string) =>
      candidate === specDir || candidate === specPath
    );
    mockReaddirSync.mockImplementation((candidate: string) => {
      if (candidate === specDir) return ["AUDIT_title_card.md", "title_card.md"];
      throw new Error(`Unexpected directory read: ${candidate}`);
    });
    mockReadFileSync.mockImplementation((candidate: string) => {
      if (candidate === auditPath) {
        return "## Verdict\npass\n## Summary\nFrame matches spec\n";
      }
      throw new Error(`Unexpected file read: ${candidate}`);
    });

    const response = await GET(makeGetRequest() as any);
    const body = await response.json();

    expect(mockReaddirSync).toHaveBeenCalledWith(specDir);
    expect(body.sections[0].specs[0].specPath).toBe("specs/cold_open/title_card.md");
    expect(body.sections[0].passCount).toBe(1);
  });
});

// ---------------------------------------------------------------------------
// 10. GET — status logic (done vs pending)
// ---------------------------------------------------------------------------

describe("GET — status determination", () => {
  it("returns 'pending' when no audit files exist but spec files do", async () => {
    mockExistsSync.mockReturnValue(true);
    // Has spec files but no AUDIT_ files
    mockReaddirSync.mockReturnValue(["visual.md", "overlay.md"]);

    const response = await GET(makeGetRequest() as any);
    const body = await response.json();

    expect(body.sections[0].status).toBe("pending");
  });

  it("returns 'done' when audit files exist", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReaddirSync.mockReturnValue([
      "AUDIT_visual.md",
      "visual.md",
    ]);
    mockReadFileSync.mockReturnValue(
      "## Verdict\npass\n## Summary\nOK\n"
    );

    const response = await GET(makeGetRequest() as any);
    const body = await response.json();

    expect(body.sections[0].status).toBe("done");
  });

  it("returns 'done' when specDir is empty", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReaddirSync.mockReturnValue([]);

    const response = await GET(makeGetRequest() as any);
    const body = await response.json();

    expect(body.sections[0].status).toBe("done");
  });

  it("handles non-existent specDir gracefully", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await GET(makeGetRequest() as any);
    const body = await response.json();

    expect(body.sections[0].status).toBe("done");
    expect(body.sections[0].passCount).toBe(0);
    expect(body.sections[0].failCount).toBe(0);
    expect(body.sections[0].specs).toEqual([]);
  });
});

// ---------------------------------------------------------------------------
// 10b. GET — specPath compatibility with /api/pipeline/specs/file
// ---------------------------------------------------------------------------

describe("GET — specPath must start with specs/ for specs/file route compatibility", () => {
  it("returns specPath prefixed with specs/ even when specDir has no prefix", async () => {
    // Simulate project config where specDir is NOT prefixed with "specs/"
    // (as in the real project.json: specDir: "cold_open")
    const config = mockProjectConfig();
    config.sections = [
      {
        ...config.sections[0],
        specDir: "cold_open", // no specs/ prefix
      },
    ];
    mockLoadProject.mockReturnValue(config);

    mockExistsSync.mockReturnValue(true);
    mockReaddirSync.mockReturnValue(["AUDIT_title_card.md", "title_card.md"]);
    mockReadFileSync.mockReturnValue(
      "## Verdict\nfail\n## Summary\nColors wrong\n"
    );

    const response = await GET(makeGetRequest() as any);
    const body = await response.json();

    const section = body.sections[0];
    expect(section.specs[0].specPath).toBeDefined();
    // The specPath MUST start with "specs/" so the /api/pipeline/specs/file
    // route's resolveSafePath validation accepts it
    expect(section.specs[0].specPath).toMatch(/^specs\//);
  });

  it("returns specPath prefixed with specs/ when specDir already has prefix", async () => {
    const config = mockProjectConfig();
    config.sections = [config.sections[0]]; // specDir: "specs/intro"
    mockLoadProject.mockReturnValue(config);

    mockExistsSync.mockReturnValue(true);
    mockReaddirSync.mockReturnValue(["AUDIT_visual.md", "visual.md"]);
    mockReadFileSync.mockReturnValue(
      "## Verdict\nfail\n## Summary\nBad frame\n"
    );

    const response = await GET(makeGetRequest() as any);
    const body = await response.json();

    const section = body.sections[0];
    expect(section.specs[0].specPath).toMatch(/^specs\//);
    // Should NOT double-prefix: "specs/specs/intro/..."
    expect(section.specs[0].specPath).not.toMatch(/^specs\/specs\//);
  });
});

// ---------------------------------------------------------------------------
// 11. GET — error handling
// ---------------------------------------------------------------------------

describe("GET — error handling", () => {
  it("returns 500 when loadProject throws", async () => {
    mockLoadProject.mockImplementation(() => {
      throw new Error("project.json not found");
    });

    const response = await GET(makeGetRequest() as any);
    expect(response.status).toBe(500);

    const body = await response.json();
    expect(body.error).toBe("Internal Server Error");
  });

  it("does not require authentication", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReaddirSync.mockReturnValue([]);

    const request = new Request(
      "http://localhost/api/pipeline/audit/results",
      {
        method: "GET",
        headers: { Authorization: "Bearer fake-token" },
      }
    );

    const response = await GET(request as any);
    expect(response.status).toBe(200);
  });
});

// ---------------------------------------------------------------------------
// 12. POST — SSE event format
// ---------------------------------------------------------------------------

describe("POST — SSE event format", () => {
  it("formats events as SSE blocks ending in a JSON data payload", async () => {
    const response = await POST(makeRequest() as any);
    await flushPromises();

    const reader = response.body!.getReader();
    const decoder = new TextDecoder();
    let raw = "";
    try {
      while (true) {
        const { done, value } = await reader.read();
        if (done) break;
        const chunk =
          typeof value === "string"
            ? value
            : decoder.decode(value, { stream: true });
        raw += chunk;
      }
    } catch {
      // stream closed
    }

    const eventBlocks = raw.split("\n\n").filter((b) => b.trim().length > 0);
    for (const block of eventBlocks) {
      expect(block).toMatch(/data:\s*\{/);
    }
  });
});

// ---------------------------------------------------------------------------
// 13. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/pipeline/audit/run/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    const realFs = jest.requireActual("fs");
    const pathMod = require("path");
    sourceCode = realFs.readFileSync(
      pathMod.join(
        __dirname,
        "..",
        "app",
        "api",
        "pipeline",
        "audit",
        "run",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async function POST", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+POST/);
  });

  it("GET handler lives in separate results route file", () => {
    const realFs = jest.requireActual("fs");
    const pathMod = require("path");
    const resultsSource = realFs.readFileSync(
      pathMod.join(
        __dirname,
        "..",
        "app",
        "api",
        "pipeline",
        "audit",
        "results",
        "route.ts"
      ),
      "utf-8"
    );
    expect(resultsSource).toMatch(/export\s+async\s+function\s+GET/);
  });

  it("imports registerExecutor and runPipelineStage from @/lib/jobs", () => {
    expect(sourceCode).toMatch(/@\/lib\/jobs/);
    expect(sourceCode).toMatch(/registerExecutor/);
    expect(sourceCode).toMatch(/runPipelineStage/);
  });

  it("imports frame extraction helpers from @/lib/render", () => {
    expect(sourceCode).toMatch(/@\/lib\/render/);
    expect(sourceCode).toMatch(/renderStill/);
    expect(sourceCode).toMatch(/extractFrameAtTime/);
  });

  it("imports createSseStream from @/lib/sse instead of defining a local stream helper", () => {
    expect(sourceCode).toMatch(
      /import\s+\{\s*createSseStream\s*\}\s+from\s+["']@\/lib\/sse["']/
    );
    expect(sourceCode).not.toMatch(/function\s+createSseStream\s*\(/);
  });

  it("imports resolveAuditSampleWindow from @/lib/audit-timing", () => {
    expect(sourceCode).toMatch(/@\/lib\/audit-timing/);
    expect(sourceCode).toMatch(/resolveAuditSampleWindow/);
  });

  it("imports runClaudeAnalysis from @/lib/claude", () => {
    expect(sourceCode).toMatch(/@\/lib\/claude/);
    expect(sourceCode).toMatch(/runClaudeAnalysis/);
  });

  it("imports loadProject from @/lib/project", () => {
    expect(sourceCode).toMatch(/@\/lib\/project/);
    expect(sourceCode).toMatch(/loadProject/);
  });

  it("imports AnnotationAnalysis, Section, and SseSend from @/lib/types", () => {
    expect(sourceCode).toMatch(/@\/lib\/types/);
    expect(sourceCode).toMatch(/AnnotationAnalysis/);
    expect(sourceCode).toMatch(/Section/);
    expect(sourceCode).toMatch(/SseSend/);
  });

  it("calls registerExecutor('audit', ...)", () => {
    expect(sourceCode).toMatch(
      /registerExecutor\s*\(\s*["']audit["']/
    );
  });

  it("calls runPipelineStage('audit', ...)", () => {
    expect(sourceCode).toMatch(
      /runPipelineStage\s*\(\s*["']audit["']/
    );
  });

  it("uses outputs/audit path for still images", () => {
    expect(sourceCode).toMatch(/outputs[\s\S]*audit/);
  });

  it("uses AUDIT_ prefix for audit report files", () => {
    expect(sourceCode).toMatch(/AUDIT_/);
  });

  it("uses Promise.all for concurrent section auditing", () => {
    expect(sourceCode).toMatch(/Promise\.all/);
  });

  it("emits audit-section events", () => {
    expect(sourceCode).toMatch(/audit-section/);
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

  it("creates SSE stream with the shared helper", () => {
    expect(sourceCode).toMatch(/createSseStream\(\)/);
  });

  it("parses ## Verdict heading from audit markdown", () => {
    expect(sourceCode).toMatch(/## Verdict/);
  });

  it("parses ## Summary heading from audit markdown", () => {
    expect(sourceCode).toMatch(/## Summary/);
  });

  it("uses extractFrameAtTime for rendered video audits", () => {
    expect(sourceCode).toMatch(/extractFrameAtTime/);
  });

  it("keeps renderStill as a fallback when rendered video is unavailable", () => {
    expect(sourceCode).toMatch(/renderStill/);
  });

  it("uses runClaudeAnalysis for comparing stills against specs", () => {
    expect(sourceCode).toMatch(/runClaudeAnalysis/);
  });
});

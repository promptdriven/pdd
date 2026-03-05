/**
 * Tests for app/api/pipeline/specs/run/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_pipeline_specs_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. POST /api/pipeline/specs/run — accepts { sections?: string[], files?: string[] }
 *   2. If sections omitted, generates all sections from loadProject()
 *   3. Calls runClaudeFix with a spec generation prompt scoped to specs/
 *   4. Returns SSE stream with { jobId }
 *   5. registerExecutor('specs', ...) called at module load time
 *   6. No authentication required
 *   7. Prompt includes visual type markers: [Remotion], [veo:], [title:], [split:]
 *   8. Scope directory is path.join(process.cwd(), 'specs')
 *   9. SSE headers: Content-Type, Cache-Control, Connection
 *  10. Error handling: emits error event on failure
 *  11. Executor uses loadProject() to determine section list
 *  12. Executor reports progress via onLog.progress callback
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

// Import after mocking
import { POST } from "../app/api/pipeline/specs/run/route";

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
    return new Request("http://localhost/api/pipeline/specs/run", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(body),
    });
  }
  return new Request("http://localhost/api/pipeline/specs/run", {
    method: "POST",
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
    veo: { model: "veo-2.0-generate-001", aspectRatio: "16:9", referenceImages: {} },
    render: { maxParallelRenders: 3, outputDir: "output/final", fps: 30, width: 1920, height: 1080 },
  };
}

// ---------------------------------------------------------------------------
// Setup
// ---------------------------------------------------------------------------

beforeEach(() => {
  mockRunPipelineStage.mockReset();
  mockRunClaudeFix.mockReset();
  mockLoadProject.mockReset();

  mockRunPipelineStage.mockResolvedValue("test-job-specs-001");
  mockRunClaudeFix.mockResolvedValue(undefined);
  mockLoadProject.mockReturnValue(mockProjectConfig());
});

// ---------------------------------------------------------------------------
// 1. registerExecutor — module load side effect
// ---------------------------------------------------------------------------

describe("registerExecutor at module load", () => {
  it("registers executor for 'specs' stage", () => {
    expect(registerCallArgs.stage).toBe("specs");
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
    mockRunPipelineStage.mockResolvedValue("test-job-specs-42");
  });

  it("calls runPipelineStage with 'specs' stage", async () => {
    await POST(makeRequest() as any);
    await flushPromises();

    expect(mockRunPipelineStage).toHaveBeenCalledTimes(1);
    expect(mockRunPipelineStage.mock.calls[0][0]).toBe("specs");
  });

  it("passes sections and files params from body to runPipelineStage", async () => {
    await POST(
      makeRequest({ sections: ["intro", "outro"], files: ["spec1.md"] }) as any
    );
    await flushPromises();

    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.sections).toEqual(["intro", "outro"]);
    expect(params.files).toEqual(["spec1.md"]);
  });

  it("passes undefined sections when body has no sections array", async () => {
    await POST(makeRequest({}) as any);
    await flushPromises();

    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.sections).toBeUndefined();
  });

  it("passes undefined files when body has no files array", async () => {
    await POST(makeRequest({}) as any);
    await flushPromises();

    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.files).toBeUndefined();
  });

  it("passes a send function to runPipelineStage", async () => {
    await POST(makeRequest() as any);
    await flushPromises();

    expect(typeof mockRunPipelineStage.mock.calls[0][2]).toBe("function");
  });

  it("emits complete event with jobId after runPipelineStage resolves", async () => {
    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const completeEvent = events.find((e: any) => e.type === "complete") as any;
    expect(completeEvent).toBeDefined();
    expect(completeEvent.jobId).toBe("test-job-specs-42");
  });
});

// ---------------------------------------------------------------------------
// 4. POST — accepts optional body parameters
// ---------------------------------------------------------------------------

describe("POST — body parameter handling", () => {
  it("works with no body (generates all sections)", async () => {
    const response = await POST(makeRequest() as any);
    expect(response).toBeInstanceOf(Response);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("works with empty sections array", async () => {
    const response = await POST(makeRequest({ sections: [] }) as any);
    expect(response).toBeInstanceOf(Response);
  });

  it("accepts specific sections array", async () => {
    const response = await POST(
      makeRequest({ sections: ["intro", "outro"] }) as any
    );
    expect(response).toBeInstanceOf(Response);
  });

  it("accepts files array alongside sections", async () => {
    const response = await POST(
      makeRequest({
        sections: ["intro"],
        files: ["specs/intro/visual.md"],
      }) as any
    );
    expect(response).toBeInstanceOf(Response);
  });

  it("handles invalid body gracefully (non-JSON)", async () => {
    const request = new Request("http://localhost/api/pipeline/specs/run", {
      method: "POST",
      body: "not json",
    });

    const response = await POST(request as any);
    expect(response).toBeInstanceOf(Response);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("handles body with sections as non-array gracefully", async () => {
    const response = await POST(
      makeRequest({ sections: "not-an-array" }) as any
    );
    await flushPromises();

    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.sections).toBeUndefined();
  });

  it("handles body with files as non-array gracefully", async () => {
    const response = await POST(
      makeRequest({ files: "not-an-array" }) as any
    );
    await flushPromises();

    const params = mockRunPipelineStage.mock.calls[0][1];
    expect(params.files).toBeUndefined();
  });
});

// ---------------------------------------------------------------------------
// 5. POST — error handling
// ---------------------------------------------------------------------------

describe("POST — error handling", () => {
  it("emits error event when runPipelineStage rejects with Error", async () => {
    mockRunPipelineStage.mockRejectedValue(new Error("Pipeline failed"));

    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const errorEvent = events.find((e: any) => e.message) as any;
    expect(errorEvent).toBeDefined();
    expect(errorEvent.message).toBe("Pipeline failed");
  });

  it("emits generic error for non-Error throws", async () => {
    mockRunPipelineStage.mockRejectedValue("string error");

    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const errorEvent = events.find((e: any) => e.message) as any;
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
    const request = new Request("http://localhost/api/pipeline/specs/run", {
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
// 7. Executor factory — registered with pipeline job system
// ---------------------------------------------------------------------------

describe("specs executor factory", () => {
  it("returns an async function when called with params and send", () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    expect(typeof executor).toBe("function");
  });

  it("calls loadProject() to get section list", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    expect(mockLoadProject).toHaveBeenCalledTimes(1);
  });

  it("uses all sections from loadProject when params.sections is empty", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    // Per-section invocation: one runClaudeFix call per section
    expect(mockRunClaudeFix).toHaveBeenCalledTimes(3);
    const allPrompts = mockRunClaudeFix.mock.calls.map((c: any[]) => c[0]).join("\n");
    expect(allPrompts).toContain("intro");
    expect(allPrompts).toContain("main");
    expect(allPrompts).toContain("outro");
  });

  it("uses all sections from loadProject when params.sections is not provided", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const allPrompts = mockRunClaudeFix.mock.calls.map((c: any[]) => c[0]).join("\n");
    expect(allPrompts).toContain("intro");
    expect(allPrompts).toContain("main");
    expect(allPrompts).toContain("outro");
  });

  it("uses specified sections from params when provided", async () => {
    const executor = registerCallArgs.factory(
      { sections: ["intro", "outro"] },
      jest.fn()
    );
    await executor(jest.fn());

    // Only 2 calls (intro + outro), no main
    expect(mockRunClaudeFix).toHaveBeenCalledTimes(2);
    const allPrompts = mockRunClaudeFix.mock.calls.map((c: any[]) => c[0]).join("\n");
    expect(allPrompts).toContain("intro");
    expect(allPrompts).toContain("outro");
    expect(allPrompts).not.toContain("### Section: main");
  });

  it("includes specDir paths in prompt for each section", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    // Each per-section prompt references its own specDir
    const allPrompts = mockRunClaudeFix.mock.calls.map((c: any[]) => c[0]).join("\n");
    expect(allPrompts).toContain("specs/specs/intro/");
    expect(allPrompts).toContain("specs/specs/main/");
    expect(allPrompts).toContain("specs/specs/outro/");
  });

  it("uses empty files list when params.files is not provided", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0];
    expect(prompt).toContain("ALL spec files needed for the section.");
  });

  it("lists specific files in prompt when params.files is provided", async () => {
    const executor = registerCallArgs.factory(
      { files: ["specs/intro/visual.md", "specs/main/overlay.md"] },
      jest.fn()
    );
    await executor(jest.fn());

    const allPrompts = mockRunClaudeFix.mock.calls.map((c: any[]) => c[0]).join("\n");
    expect(allPrompts).toContain("specs/intro/visual.md");
    expect(allPrompts).toContain("specs/main/overlay.md");
  });

  it("calls runClaudeFix with prompt scoped to specs/ directory", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    // Each per-section call is scoped to specs/ base directory
    expect(mockRunClaudeFix).toHaveBeenCalledTimes(3);
    const pathMod = require("path");
    for (const call of mockRunClaudeFix.mock.calls) {
      expect(call[1]).toBe(pathMod.join(process.cwd(), "specs"));
    }
  });

  it("passes onLog callback to runClaudeFix", async () => {
    const onLog = jest.fn();
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(onLog);

    expect(mockRunClaudeFix.mock.calls[0][2]).toBe(onLog);
  });

  it("prompt includes visual type markers", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0];
    expect(prompt).toContain("[Remotion]");
    expect(prompt).toContain("[veo:]");
    expect(prompt).toContain("[title:]");
    expect(prompt).toContain("[split:]");
  });

  it("prompt instructs to generate specs under specs/ directory", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0];
    expect(prompt).toContain("specs/");
  });

  it("prompt instructs to generate only markdown spec files", async () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0];
    expect(prompt).toMatch(/markdown/i);
  });

  it("reports progress 0 before running and 100 after", async () => {
    const progressFn = jest.fn();
    const onLog = Object.assign(jest.fn(), { progress: progressFn });

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(onLog as any);

    expect(progressFn).toHaveBeenCalledWith(0);
    expect(progressFn).toHaveBeenCalledWith(100);

    const calls = progressFn.mock.calls.map((c: any[]) => c[0]);
    const idx0 = calls.indexOf(0);
    const idx100 = calls.indexOf(100);
    expect(idx0).toBeLessThan(idx100);
  });

  it("propagates runClaudeFix errors", async () => {
    mockRunClaudeFix.mockRejectedValue(new Error("Claude failed"));

    const executor = registerCallArgs.factory({}, jest.fn());
    await expect(executor(jest.fn())).rejects.toThrow("Claude failed");
  });

  it("handles loadProject returning a single section", async () => {
    mockLoadProject.mockReturnValue({
      ...mockProjectConfig(),
      sections: [{ id: "only-section", label: "Only", specDir: "only-section" }],
    });

    const executor = registerCallArgs.factory({}, jest.fn());
    await executor(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0];
    expect(prompt).toContain("only-section");
  });

  it("ignores empty sections array in params (uses all from project)", async () => {
    const executor = registerCallArgs.factory(
      { sections: [] },
      jest.fn()
    );
    await executor(jest.fn());

    // Falls back to all sections → 3 calls
    expect(mockRunClaudeFix).toHaveBeenCalledTimes(3);
    const allPrompts = mockRunClaudeFix.mock.calls.map((c: any[]) => c[0]).join("\n");
    expect(allPrompts).toContain("intro");
    expect(allPrompts).toContain("main");
    expect(allPrompts).toContain("outro");
  });

  it("ignores empty files array in params", async () => {
    const executor = registerCallArgs.factory(
      { files: [] },
      jest.fn()
    );
    await executor(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0];
    expect(prompt).toContain("ALL spec files needed for the section.");
  });

  it("does not crash when onLog has no progress callback", async () => {
    const onLog = jest.fn();
    const executor = registerCallArgs.factory({}, jest.fn());
    await expect(executor(onLog)).resolves.not.toThrow();
  });

  it("builds specDirMap from project config to resolve section ID to specDir", () => {
    const fs = require("fs");
    const pathMod = require("path");
    const src = fs.readFileSync(
      pathMod.join(__dirname, "..", "app", "api", "pipeline", "specs", "run", "route.ts"),
      "utf-8"
    );
    expect(src).toMatch(/specDirMap\.get\(sid\)\s*\?\?\s*sid/);
  });
});

// ---------------------------------------------------------------------------
// 8. POST — SSE event format (data: JSON\n\n)
// ---------------------------------------------------------------------------

describe("POST — SSE event format", () => {
  it("formats events as 'data: <JSON>\\n\\n'", async () => {
    const response = await POST(makeRequest() as any);
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
      // Each SSE block should contain a data: line
      expect(block).toMatch(/data:\s*/);
    }
  });
});

// ---------------------------------------------------------------------------
// 9. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/pipeline/specs/run/route.ts source structure", () => {
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
        "specs",
        "run",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async function POST", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+POST/);
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

  it("imports createSseStream from @/lib/sse", () => {
    expect(sourceCode).toMatch(/@\/lib\/sse/);
    expect(sourceCode).toMatch(/createSseStream/);
  });

  it("imports path from 'path'", () => {
    expect(sourceCode).toMatch(/import\s+path\s+from\s+["']path["']/);
  });

  it("calls registerExecutor('specs', ...)", () => {
    expect(sourceCode).toMatch(
      /registerExecutor\s*\(\s*["']specs["']/
    );
  });

  it("calls runPipelineStage('specs', ...)", () => {
    expect(sourceCode).toMatch(/runPipelineStage\s*\(/);
  });

  it("scopes runClaudeFix to specs/ directory via path.join", () => {
    expect(sourceCode).toMatch(
      /path\.join\s*\(\s*process\.cwd\(\)\s*,\s*["']specs["']\s*\)/
    );
  });

  it("uses new Response(stream, ...) for SSE streaming", () => {
    expect(sourceCode).toMatch(/new\s+Response\s*\(\s*stream/);
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

  it("includes visual type markers in spec prompt", () => {
    expect(sourceCode).toMatch(/\[Remotion\]/);
    expect(sourceCode).toMatch(/\[veo:\]/);
    expect(sourceCode).toMatch(/\[title:\]/);
    expect(sourceCode).toMatch(/\[split:\]/);
  });

  it("prompt references specs/ directory structure with specDir variable", () => {
    expect(sourceCode).toMatch(/specs\/\$\{dir\}/);
  });

  it("uses loadProject to get section list", () => {
    expect(sourceCode).toMatch(/loadProject\(\)/);
  });

  it("creates SSE stream with createSseStream()", () => {
    expect(sourceCode).toMatch(/createSseStream\(\)/);
  });

  it("uses send() for emitting SSE events", () => {
    expect(sourceCode).toMatch(/send\(/);
  });

  it("imports NextRequest from next/server", () => {
    expect(sourceCode).toMatch(/import.*NextRequest.*from\s+["']next\/server["']/);
  });
});

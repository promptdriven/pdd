/**
 * Tests for app/api/sections/[id]/resolve-batch/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_sections_id_resolve_batch_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. POST /api/sections/[id]/resolve-batch — batches all unresolved annotations
 *      - Loads all unresolved annotations for the section from DB
 *      - Groups annotations by fixType: remotion, veo, tts, manual
 *      - For remotion fixType: calls runClaudeFix() scoped to 'remotion/src/remotion/'
 *      - For veo fixType: triggers a Veo clip regeneration job (placeholder log)
 *      - For tts fixType: triggers TTS re-render (placeholder log)
 *      - manual fixType: skipped (human intervention required)
 *      - After fixes: triggers re-render of the affected section
 *      - Creates a single parent job, returns { jobId } immediately (non-blocking)
 *      - Updates annotation.resolveJobId for each annotation with the job ID
 *   2. No authentication required
 *   3. Exports dynamic = 'force-dynamic'
 *   4. Returns 200 with { jobId: null, message: 'No unresolved annotations' } when no unresolved
 *   5. Deserializes analysis_json → analysis for each annotation
 *   6. Creates job with createJob('audit', { sectionId })
 *   7. Runs all fixes inside runJob() executor
 *   8. buildRemotionPrompt() generates prompt with annotation details
 *   9. Error handling returns 500 with { error: 'Internal Server Error' }
 */

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockAll = jest.fn();
const mockRun = jest.fn();
const mockPrepare = jest.fn(() => ({
  all: mockAll,
  run: mockRun,
}));
const mockDb = { prepare: mockPrepare };
const mockGetDb = jest.fn(() => mockDb);

jest.mock("@/lib/db", () => ({
  getDb: () => mockGetDb(),
}));

const mockRunClaudeFix = jest.fn();

jest.mock("@/lib/claude", () => ({
  runClaudeFix: (...args: unknown[]) => mockRunClaudeFix(...args),
}));

const MOCK_JOB_ID = "job-resolve-batch-001";
const mockCreateJob = jest.fn(() => MOCK_JOB_ID);
const mockRunJob = jest.fn();

jest.mock("@/lib/jobs", () => ({
  createJob: (...args: unknown[]) => mockCreateJob(...args),
  runJob: (...args: unknown[]) => mockRunJob(...args),
}));

const mockRenderSection = jest.fn();

jest.mock("@/lib/render", () => ({
  renderSection: (...args: unknown[]) => mockRenderSection(...args),
}));

const mockLoadProject = jest.fn();
const mockGetSection = jest.fn();

jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
  getSection: (...args: unknown[]) => mockGetSection(...args),
}));

// Import after mock setup
import { POST, dynamic } from "../app/api/sections/[id]/resolve-batch/route";
import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Creates a route params object with the given section ID. */
function makeParams(id: string) {
  return { params: { id } };
}

/** Creates a minimal Request for POST. */
function makeRequest(): Request {
  return new Request("http://localhost/api/sections/section-1/resolve-batch", {
    method: "POST",
  });
}

/** Returns a mock DB row representing an unresolved annotation. */
function makeDbRow(overrides: Record<string, unknown> = {}) {
  return {
    id: "ann-001",
    sectionId: "section-1",
    timestamp: 5.0,
    text: "Fix the color grading",
    videoFile: "output/sections/intro.mp4",
    drawingDataUrl: "data:image/png;base64,draw",
    compositeDataUrl: "data:image/png;base64,comp",
    analysis: JSON.stringify({
      severity: "major",
      fixType: "remotion",
      technicalAssessment: "Color issue",
      suggestedFixes: ["Adjust contrast"],
      confidence: 0.85,
    }),
    resolved: 0,
    resolveJobId: null,
    createdAt: "2025-01-15T10:00:00.000Z",
    ...overrides,
  };
}

/** Returns a mock section object. */
function mockSection() {
  return {
    id: "section-1",
    label: "Introduction",
    videoFile: "output/sections/intro.mp4",
    specDir: "specs/intro",
    remotionDir: "remotion/intro",
    compositionId: "IntroComposition",
    durationSeconds: 12.5,
    offsetSeconds: 0,
  };
}

/** Flush microtask queue so fire-and-forget callbacks complete. */
function flushPromises(): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, 50));
}

// ---------------------------------------------------------------------------
// Setup / Teardown
// ---------------------------------------------------------------------------

beforeEach(() => {
  mockGetDb.mockReset();
  mockGetDb.mockReturnValue(mockDb);
  mockPrepare.mockReset();
  mockPrepare.mockReturnValue({ all: mockAll, run: mockRun });
  mockAll.mockReset();
  mockRun.mockReset();
  mockCreateJob.mockReset();
  mockCreateJob.mockReturnValue(MOCK_JOB_ID);
  mockRunJob.mockReset();
  mockRunJob.mockResolvedValue(undefined);
  mockRunClaudeFix.mockReset();
  mockRunClaudeFix.mockResolvedValue(undefined);
  mockRenderSection.mockReset();
  mockRenderSection.mockResolvedValue(undefined);
  mockLoadProject.mockReset();
  mockLoadProject.mockReturnValue({ sections: [mockSection()] });
  mockGetSection.mockReset();
  mockGetSection.mockReturnValue(mockSection());
  jest.spyOn(console, "error").mockImplementation(() => {});
});

afterEach(() => {
  jest.restoreAllMocks();
});

// ---------------------------------------------------------------------------
// 1. dynamic export
// ---------------------------------------------------------------------------

describe("dynamic export", () => {
  it("exports dynamic = 'force-dynamic'", () => {
    expect(dynamic).toBe("force-dynamic");
  });
});

// ---------------------------------------------------------------------------
// 2. POST — no unresolved annotations
// ---------------------------------------------------------------------------

describe("POST — no unresolved annotations", () => {
  it("returns 200 with { jobId: null, message } when no rows found", async () => {
    mockAll.mockReturnValue([]);

    const response = await POST(makeRequest(), makeParams("section-1"));
    const body = await response.json();

    expect(response.status).toBe(200);
    expect(body.jobId).toBeNull();
    expect(body.message).toBe("No unresolved annotations");
  });

  it("returns 200 with { jobId: null } when rows is null-ish", async () => {
    mockAll.mockReturnValue(null);

    const response = await POST(makeRequest(), makeParams("section-1"));
    const body = await response.json();

    expect(response.status).toBe(200);
    expect(body.jobId).toBeNull();
  });

  it("does not call createJob when no unresolved annotations", async () => {
    mockAll.mockReturnValue([]);

    await POST(makeRequest(), makeParams("section-1"));

    expect(mockCreateJob).not.toHaveBeenCalled();
  });

  it("does not call runJob when no unresolved annotations", async () => {
    mockAll.mockReturnValue([]);

    await POST(makeRequest(), makeParams("section-1"));

    expect(mockRunJob).not.toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 3. POST — queries DB for unresolved annotations
// ---------------------------------------------------------------------------

describe("POST — DB query for unresolved annotations", () => {
  beforeEach(() => {
    mockAll.mockReturnValue([makeDbRow()]);
  });

  it("calls getDb() to obtain the database", async () => {
    await POST(makeRequest(), makeParams("section-1"));

    expect(mockGetDb).toHaveBeenCalledTimes(1);
  });

  it("queries annotations with WHERE sectionId = ? AND resolved = 0", async () => {
    await POST(makeRequest(), makeParams("section-1"));

    const sql = mockPrepare.mock.calls[0][0] as string;
    expect(sql).toContain("sectionId = ?");
    expect(sql).toContain("resolved = 0");
  });

  it("passes the section id from params to .all()", async () => {
    await POST(makeRequest(), makeParams("my-section"));

    expect(mockAll).toHaveBeenCalledWith("my-section");
  });

  it("orders results by timestamp ASC", async () => {
    await POST(makeRequest(), makeParams("section-1"));

    const sql = mockPrepare.mock.calls[0][0] as string;
    expect(sql).toContain("ORDER BY timestamp ASC");
  });

  it("uses SELECT * FROM annotations", async () => {
    await POST(makeRequest(), makeParams("section-1"));

    const sql = mockPrepare.mock.calls[0][0] as string;
    expect(sql).toContain("SELECT * FROM annotations");
  });
});

// ---------------------------------------------------------------------------
// 4. POST — deserialization of analysis_json
// ---------------------------------------------------------------------------

describe("POST — annotation deserialization", () => {
  it("deserializes analysis JSON string into object", async () => {
    const analysisData = {
      severity: "major",
      fixType: "remotion",
      technicalAssessment: "Color issue",
      suggestedFixes: ["Adjust contrast"],
      confidence: 0.85,
    };
    mockAll.mockReturnValue([
      makeDbRow({ analysis: JSON.stringify(analysisData) }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    // Verify by checking that the executor receives the correct analysis
    expect(mockRunJob).toHaveBeenCalled();
    const executorFn = mockRunJob.mock.calls[0][1];
    const onLog = jest.fn();
    await executorFn(onLog);

    // runClaudeFix should be called since fixType is 'remotion'
    expect(mockRunClaudeFix).toHaveBeenCalled();
  });

  it("sets analysis to null when DB value is null", async () => {
    mockAll.mockReturnValue([makeDbRow({ analysis: null })]);

    await POST(makeRequest(), makeParams("section-1"));

    // With null analysis, fixType defaults to 'manual', which is skipped
    const executorFn = mockRunJob.mock.calls[0][1];
    const onLog = jest.fn();
    await executorFn(onLog);

    // Should log that it was skipped as manual
    expect(onLog).toHaveBeenCalledWith(
      expect.stringContaining("Skipped manual")
    );
  });

  it("maps all DB row fields to Annotation properties", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-xyz",
        sectionId: "section-2",
        timestamp: 7.5,
        text: "Fix this",
        videoFile: "video.mp4",
        drawingDataUrl: null,
        compositeDataUrl: null,
        analysis: null,
        resolved: 0,
        resolveJobId: null,
        createdAt: "2025-06-01T12:00:00Z",
      }),
    ]);

    await POST(makeRequest(), makeParams("section-2"));

    // Verify update statement uses the correct annotation id
    expect(mockRun).toHaveBeenCalledWith(MOCK_JOB_ID, "ann-xyz");
  });
});

// ---------------------------------------------------------------------------
// 5. POST — job creation
// ---------------------------------------------------------------------------

describe("POST — job creation", () => {
  beforeEach(() => {
    mockAll.mockReturnValue([makeDbRow()]);
  });

  it("creates a job with createJob('audit', { sectionId })", async () => {
    await POST(makeRequest(), makeParams("section-1"));

    expect(mockCreateJob).toHaveBeenCalledTimes(1);
    expect(mockCreateJob).toHaveBeenCalledWith("audit", {
      sectionId: "section-1",
    });
  });

  it("returns { jobId } in response body", async () => {
    const response = await POST(makeRequest(), makeParams("section-1"));
    const body = await response.json();

    expect(body.jobId).toBe(MOCK_JOB_ID);
  });

  it("returns 200 status", async () => {
    const response = await POST(makeRequest(), makeParams("section-1"));

    expect(response.status).toBe(200);
  });

  it("returns immediately (non-blocking) — response before runJob completes", async () => {
    let runJobResolved = false;
    mockRunJob.mockImplementation(async () => {
      await new Promise((resolve) => setTimeout(resolve, 100));
      runJobResolved = true;
    });

    const response = await POST(makeRequest(), makeParams("section-1"));

    // Response is available before runJob completes
    expect(response.status).toBe(200);
    expect(runJobResolved).toBe(false);
  });
});

// ---------------------------------------------------------------------------
// 6. POST — updates resolveJobId for all annotations
// ---------------------------------------------------------------------------

describe("POST — updates resolveJobId for all annotations", () => {
  it("prepares an UPDATE statement for resolveJobId", async () => {
    mockAll.mockReturnValue([makeDbRow()]);

    await POST(makeRequest(), makeParams("section-1"));

    const updateCalls = mockPrepare.mock.calls.filter((call: any) =>
      (call[0] as string).includes("UPDATE annotations SET resolveJobId")
    );
    expect(updateCalls.length).toBeGreaterThan(0);
  });

  it("updates each annotation with the job ID", async () => {
    mockAll.mockReturnValue([
      makeDbRow({ id: "ann-1" }),
      makeDbRow({ id: "ann-2" }),
      makeDbRow({ id: "ann-3" }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    // First prepare call is SELECT, second is UPDATE
    // mockRun is called once per annotation for the UPDATE
    expect(mockRun).toHaveBeenCalledWith(MOCK_JOB_ID, "ann-1");
    expect(mockRun).toHaveBeenCalledWith(MOCK_JOB_ID, "ann-2");
    expect(mockRun).toHaveBeenCalledWith(MOCK_JOB_ID, "ann-3");
  });

  it("updates annotations before starting the job (runJob called after updates)", async () => {
    mockAll.mockReturnValue([makeDbRow()]);

    const callOrder: string[] = [];
    mockRun.mockImplementation(() => {
      callOrder.push("update");
    });
    mockRunJob.mockImplementation(() => {
      callOrder.push("runJob");
      return Promise.resolve();
    });

    await POST(makeRequest(), makeParams("section-1"));

    const firstUpdate = callOrder.indexOf("update");
    const firstRunJob = callOrder.indexOf("runJob");
    expect(firstUpdate).toBeLessThan(firstRunJob);
  });
});

// ---------------------------------------------------------------------------
// 7. POST — runJob executor: grouping by fixType
// ---------------------------------------------------------------------------

describe("POST — runJob executor: fixType grouping", () => {
  it("calls runJob with the job ID and an executor function", async () => {
    mockAll.mockReturnValue([makeDbRow()]);

    await POST(makeRequest(), makeParams("section-1"));

    expect(mockRunJob).toHaveBeenCalledTimes(1);
    expect(mockRunJob.mock.calls[0][0]).toBe(MOCK_JOB_ID);
    expect(typeof mockRunJob.mock.calls[0][1]).toBe("function");
  });

  it("groups remotion annotations and calls runClaudeFix for each", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-r1",
        analysis: JSON.stringify({ fixType: "remotion", severity: "major", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
      makeDbRow({
        id: "ann-r2",
        analysis: JSON.stringify({ fixType: "remotion", severity: "minor", technicalAssessment: "", suggestedFixes: [], confidence: 0.8 }),
      }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    const onLog = jest.fn();
    await executorFn(onLog);

    expect(mockRunClaudeFix).toHaveBeenCalledTimes(2);
  });

  it("calls runClaudeFix with buildRemotionPrompt, 'remotion/src/remotion/', and onLog", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-r1",
        text: "Fix the intro text",
        timestamp: 3.5,
        sectionId: "section-1",
        analysis: JSON.stringify({ fixType: "remotion", severity: "major", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    const onLog = jest.fn();
    await executorFn(onLog);

    expect(mockRunClaudeFix).toHaveBeenCalledTimes(1);
    const [prompt, scopePath, logFn] = mockRunClaudeFix.mock.calls[0];
    expect(prompt).toContain("ann-r1");
    expect(prompt).toContain("section-1");
    expect(prompt).toContain("3.5s");
    expect(prompt).toContain("Fix the intro text");
    expect(scopePath).toBe("remotion/src/remotion/");
    expect(logFn).toBe(onLog);
  });

  it("logs veo annotations as pending (placeholder)", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-v1",
        analysis: JSON.stringify({ fixType: "veo", severity: "major", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    const onLog = jest.fn();
    await executorFn(onLog);

    expect(onLog).toHaveBeenCalledWith(
      expect.stringContaining("Veo regeneration")
    );
    expect(onLog).toHaveBeenCalledWith(
      expect.stringContaining("ann-v1")
    );
  });

  it("logs tts annotations as pending (placeholder)", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-t1",
        analysis: JSON.stringify({ fixType: "tts", severity: "minor", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    const onLog = jest.fn();
    await executorFn(onLog);

    expect(onLog).toHaveBeenCalledWith(
      expect.stringContaining("TTS re-render")
    );
    expect(onLog).toHaveBeenCalledWith(
      expect.stringContaining("ann-t1")
    );
  });

  it("skips manual annotations (logs them as skipped)", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-m1",
        analysis: JSON.stringify({ fixType: "none", severity: "pass", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
      makeDbRow({
        id: "ann-m2",
        analysis: null, // null analysis defaults to manual
      }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    const onLog = jest.fn();
    await executorFn(onLog);

    // ann-m2 (null analysis → manual) should be skipped
    expect(onLog).toHaveBeenCalledWith(
      expect.stringContaining("Skipped manual annotation ann-m2")
    );
    // runClaudeFix should NOT be called for manual or none
    expect(mockRunClaudeFix).not.toHaveBeenCalled();
  });

  it("handles annotations with mixed fixTypes correctly", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-r1",
        analysis: JSON.stringify({ fixType: "remotion", severity: "major", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
      makeDbRow({
        id: "ann-v1",
        analysis: JSON.stringify({ fixType: "veo", severity: "major", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
      makeDbRow({
        id: "ann-t1",
        analysis: JSON.stringify({ fixType: "tts", severity: "minor", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
      makeDbRow({
        id: "ann-m1",
        analysis: null,
      }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    const onLog = jest.fn();
    await executorFn(onLog);

    // 1 remotion fix
    expect(mockRunClaudeFix).toHaveBeenCalledTimes(1);
    // veo, tts, manual all logged
    expect(onLog).toHaveBeenCalledWith(expect.stringContaining("Veo regeneration"));
    expect(onLog).toHaveBeenCalledWith(expect.stringContaining("TTS re-render"));
    expect(onLog).toHaveBeenCalledWith(expect.stringContaining("Skipped manual"));
  });
});

// ---------------------------------------------------------------------------
// 8. POST — runJob executor: section rendering
// ---------------------------------------------------------------------------

describe("POST — runJob executor: section rendering after fixes", () => {
  beforeEach(() => {
    mockAll.mockReturnValue([makeDbRow()]);
  });

  it("calls loadProject() inside executor", async () => {
    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    await executorFn(jest.fn());

    expect(mockLoadProject).toHaveBeenCalled();
  });

  it("calls getSection(sectionId, project) inside executor", async () => {
    const project = { sections: [mockSection()] };
    mockLoadProject.mockReturnValue(project);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    await executorFn(jest.fn());

    expect(mockGetSection).toHaveBeenCalledWith("section-1", project);
  });

  it("calls renderSection with compositionId, videoFile, and progress callback", async () => {
    const section = mockSection();
    mockGetSection.mockReturnValue(section);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    await executorFn(jest.fn());

    expect(mockRenderSection).toHaveBeenCalledTimes(1);
    expect(mockRenderSection.mock.calls[0][0]).toBe("IntroComposition");
    expect(mockRenderSection.mock.calls[0][1]).toBe("output/sections/intro.mp4");
    expect(typeof mockRenderSection.mock.calls[0][2]).toBe("function");
  });

  it("logs rendering message before calling renderSection", async () => {
    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    const onLog = jest.fn();
    await executorFn(onLog);

    expect(onLog).toHaveBeenCalledWith(
      expect.stringContaining("Rendering section section-1")
    );
  });

  it("throws error when section is not found", async () => {
    mockGetSection.mockReturnValue(null);

    await POST(makeRequest(), makeParams("nonexistent"));

    const executorFn = mockRunJob.mock.calls[0][1];

    await expect(executorFn(jest.fn())).rejects.toThrow(
      'Section "nonexistent" not found'
    );
  });

  it("renders after all fixes complete (remotion, veo, tts)", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-r1",
        analysis: JSON.stringify({ fixType: "remotion", severity: "major", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
    ]);

    const callOrder: string[] = [];
    mockRunClaudeFix.mockImplementation(async () => {
      callOrder.push("claudeFix");
    });
    mockRenderSection.mockImplementation(async () => {
      callOrder.push("renderSection");
    });

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    await executorFn(jest.fn());

    expect(callOrder).toEqual(["claudeFix", "renderSection"]);
  });
});

// ---------------------------------------------------------------------------
// 9. POST — buildRemotionPrompt
// ---------------------------------------------------------------------------

describe("POST — buildRemotionPrompt content", () => {
  it("includes annotation ID in the prompt", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-prompt-test",
        analysis: JSON.stringify({ fixType: "remotion", severity: "major", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    await executorFn(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0] as string;
    expect(prompt).toContain("Annotation ID: ann-prompt-test");
  });

  it("includes section ID in the prompt", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-1",
        sectionId: "section-1",
        analysis: JSON.stringify({ fixType: "remotion", severity: "major", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    await executorFn(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0] as string;
    expect(prompt).toContain("Section ID: section-1");
  });

  it("includes timestamp with 's' suffix in the prompt", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-1",
        timestamp: 12.5,
        analysis: JSON.stringify({ fixType: "remotion", severity: "major", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    await executorFn(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0] as string;
    expect(prompt).toContain("Timestamp: 12.5s");
  });

  it("includes user note text in the prompt", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-1",
        text: "The background color is wrong",
        analysis: JSON.stringify({ fixType: "remotion", severity: "major", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    await executorFn(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0] as string;
    expect(prompt).toContain("User note: The background color is wrong");
  });

  it("prompt starts with 'You are applying a Remotion fix'", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        analysis: JSON.stringify({ fixType: "remotion", severity: "major", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    await executorFn(jest.fn());

    const prompt = mockRunClaudeFix.mock.calls[0][0] as string;
    expect(prompt).toMatch(/^You are applying a Remotion fix/);
  });
});

// ---------------------------------------------------------------------------
// 10. POST — error handling
// ---------------------------------------------------------------------------

describe("POST — error handling", () => {
  it("returns 500 when db.prepare().all() throws", async () => {
    mockAll.mockImplementation(() => {
      throw new Error("SQLITE_ERROR");
    });

    const response = await POST(makeRequest(), makeParams("section-1"));

    expect(response.status).toBe(500);
  });

  it("returns { error: 'Internal Server Error' } on db query failure", async () => {
    mockAll.mockImplementation(() => {
      throw new Error("SQLITE_ERROR");
    });

    const response = await POST(makeRequest(), makeParams("section-1"));
    const body = await response.json();

    expect(body).toEqual({ error: "Internal Server Error" });
  });

  it("returns 500 when createJob throws", async () => {
    mockAll.mockReturnValue([makeDbRow()]);
    mockCreateJob.mockImplementation(() => {
      throw new Error("Job creation failed");
    });

    const response = await POST(makeRequest(), makeParams("section-1"));

    expect(response.status).toBe(500);
  });

  it("logs error to console.error on failure", async () => {
    mockAll.mockImplementation(() => {
      throw new Error("Unexpected error");
    });

    await POST(makeRequest(), makeParams("section-1"));

    expect(console.error).toHaveBeenCalled();
  });

  it("getDb is called before try/catch — errors propagate", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("DB connection failed");
    });

    await expect(
      POST(makeRequest(), makeParams("section-1"))
    ).rejects.toThrow("DB connection failed");
  });
});

// ---------------------------------------------------------------------------
// 11. POST — no authentication required
// ---------------------------------------------------------------------------

describe("POST — no authentication required", () => {
  it("succeeds without any authorization header", async () => {
    mockAll.mockReturnValue([]);

    const response = await POST(makeRequest(), makeParams("section-1"));

    expect(response.status).toBe(200);
  });

  it("succeeds with an authorization header present", async () => {
    mockAll.mockReturnValue([]);

    const request = new Request(
      "http://localhost/api/sections/section-1/resolve-batch",
      {
        method: "POST",
        headers: { Authorization: "Bearer fake-token" },
      }
    );

    const response = await POST(request, makeParams("section-1"));

    expect(response.status).toBe(200);
  });
});

// ---------------------------------------------------------------------------
// 12. POST — uses section id from params
// ---------------------------------------------------------------------------

describe("POST — uses section id from params", () => {
  it("passes params.id to DB query", async () => {
    mockAll.mockReturnValue([]);

    await POST(makeRequest(), makeParams("custom-section-id"));

    expect(mockAll).toHaveBeenCalledWith("custom-section-id");
  });

  it("passes params.id to createJob params", async () => {
    mockAll.mockReturnValue([makeDbRow()]);

    await POST(makeRequest(), makeParams("my-section"));

    expect(mockCreateJob).toHaveBeenCalledWith("audit", {
      sectionId: "my-section",
    });
  });
});

// ---------------------------------------------------------------------------
// 13. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/sections/[id]/resolve-batch/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    sourceCode = fs.readFileSync(
      path.join(
        __dirname,
        "..",
        "app",
        "api",
        "sections",
        "[id]",
        "resolve-batch",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async function POST", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+POST/);
  });

  it("exports const dynamic = 'force-dynamic'", () => {
    expect(sourceCode).toMatch(/export\s+const\s+dynamic\s*=\s*["']force-dynamic["']/);
  });

  it("imports getDb from @/lib/db", () => {
    expect(sourceCode).toMatch(/@\/lib\/db/);
    expect(sourceCode).toMatch(/getDb/);
  });

  it("imports runClaudeFix from @/lib/claude", () => {
    expect(sourceCode).toMatch(/@\/lib\/claude/);
    expect(sourceCode).toMatch(/runClaudeFix/);
  });

  it("imports createJob and runJob from @/lib/jobs", () => {
    expect(sourceCode).toMatch(/@\/lib\/jobs/);
    expect(sourceCode).toMatch(/createJob/);
    expect(sourceCode).toMatch(/runJob/);
  });

  it("imports renderSection from @/lib/render", () => {
    expect(sourceCode).toMatch(/@\/lib\/render/);
    expect(sourceCode).toMatch(/renderSection/);
  });

  it("imports loadProject and getSection from @/lib/project", () => {
    expect(sourceCode).toMatch(/@\/lib\/project/);
    expect(sourceCode).toMatch(/loadProject/);
    expect(sourceCode).toMatch(/getSection/);
  });

  it("imports Annotation type from @/lib/types", () => {
    expect(sourceCode).toMatch(/@\/lib\/types/);
    expect(sourceCode).toMatch(/Annotation/);
  });

  it("uses NextResponse.json() for responses", () => {
    expect(sourceCode).toMatch(/NextResponse\.json\(/);
  });

  it("queries annotations table for unresolved entries", () => {
    expect(sourceCode).toMatch(/SELECT.*FROM annotations/);
    expect(sourceCode).toMatch(/resolved = 0/);
  });

  it("updates annotations with resolveJobId", () => {
    expect(sourceCode).toMatch(/UPDATE annotations SET resolveJobId/);
  });

  it("uses createJob('audit', ...)", () => {
    expect(sourceCode).toMatch(/createJob\s*\(\s*["']audit["']/);
  });

  it("calls runClaudeFix with 'remotion/src/remotion/' scope", () => {
    expect(sourceCode).toMatch(/remotion\/src\/remotion\//);
  });

  it("contains buildRemotionPrompt function", () => {
    expect(sourceCode).toMatch(/function\s+buildRemotionPrompt/);
  });

  it("handles manual fixType by skipping", () => {
    expect(sourceCode).toMatch(/manual/);
    expect(sourceCode).toMatch(/[Ss]kip/);
  });

  it("calls renderSection after fixes", () => {
    expect(sourceCode).toMatch(/renderSection/);
  });
});

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
const mockRunPipelineStage = jest.fn();
const mockApplyVeoPromptFixForAnnotation = jest.fn();
const mockApplyRemotionSpecFixForAnnotation = jest.fn();
const mockIsGitAvailable = jest.fn();
const mockPreFixCommit = jest.fn();
const mockFixCommit = jest.fn();

jest.mock("@/lib/jobs", () => ({
  createJob: (...args: unknown[]) => mockCreateJob(...args),
  runJob: (...args: unknown[]) => mockRunJob(...args),
  runPipelineStage: (...args: unknown[]) => mockRunPipelineStage(...args),
}));

const mockRenderSection = jest.fn();
const mockStitchFullVideo = jest.fn();

jest.mock("@/lib/render", () => ({
  renderSection: (...args: unknown[]) => mockRenderSection(...args),
  stitchFullVideo: (...args: unknown[]) => mockStitchFullVideo(...args),
}));

const mockLoadProject = jest.fn();
const mockGetSection = jest.fn();

jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
  getSection: (...args: unknown[]) => mockGetSection(...args),
}));

jest.mock("@/lib/veo-prompt-fix", () => ({
  applyVeoPromptFixForAnnotation: (...args: unknown[]) =>
    mockApplyVeoPromptFixForAnnotation(...args),
}));

jest.mock("@/lib/remotion-spec-fix", () => ({
  applyRemotionSpecFixForAnnotation: (...args: unknown[]) =>
    mockApplyRemotionSpecFixForAnnotation(...args),
}));

jest.mock("@/lib/git", () => ({
  isGitAvailable: (...args: unknown[]) => mockIsGitAvailable(...args),
  preFixCommit: (...args: unknown[]) => mockPreFixCommit(...args),
  fixCommit: (...args: unknown[]) => mockFixCommit(...args),
}));

const mockExecSync = jest.fn();

jest.mock("child_process", () => ({
  execSync: (...args: unknown[]) => mockExecSync(...args),
}));

jest.mock("@/lib/projects", () => ({
  getProjectDir: () => process.cwd(),
}));

// Import after mock setup
import { POST, dynamic } from "../app/api/sections/[id]/resolve-batch/route";
import fs from "fs";
import fsPromises from "fs/promises";
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
  mockRunPipelineStage.mockReset();
  mockRunPipelineStage.mockResolvedValue("job-veo-001");
  mockApplyVeoPromptFixForAnnotation.mockReset();
  mockApplyVeoPromptFixForAnnotation.mockReturnValue(null);
  mockApplyRemotionSpecFixForAnnotation.mockReset();
  mockApplyRemotionSpecFixForAnnotation.mockReturnValue(null);
  mockIsGitAvailable.mockReset();
  mockIsGitAvailable.mockReturnValue(true);
  mockPreFixCommit.mockReset();
  mockPreFixCommit.mockReturnValue("pre-fix-commit");
  mockFixCommit.mockReset();
  mockFixCommit.mockReturnValue("fix-commit-sha");
  mockExecSync.mockReset();
  mockExecSync.mockReturnValue(Buffer.from(""));
  mockRunClaudeFix.mockReset();
  mockRunClaudeFix.mockResolvedValue(undefined);
  mockRenderSection.mockReset();
  mockRenderSection.mockResolvedValue(undefined);
  mockStitchFullVideo.mockReset();
  mockStitchFullVideo.mockResolvedValue(undefined);
  mockLoadProject.mockReset();
  mockLoadProject.mockReturnValue({ sections: [mockSection()] });
  mockGetSection.mockReset();
  mockGetSection.mockReturnValue(mockSection());
  jest.spyOn(fsPromises, "access").mockResolvedValue(undefined);
  jest.spyOn(fsPromises, "readdir").mockResolvedValue([]);
  jest.spyOn(fsPromises, "mkdir").mockResolvedValue(undefined);
  jest.spyOn(fsPromises, "copyFile").mockResolvedValue(undefined);
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

  it("updates the targeted Remotion spec before running the code fix", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-rspec",
        sectionId: "section-1",
        timestamp: 3.4,
        analysis: JSON.stringify({
          fixType: "remotion",
          severity: "major",
          technicalAssessment: "square should be yellow",
          suggestedFixes: ["Change the square fill to yellow in the spec and component"],
          confidence: 0.9,
        }),
      }),
    ]);
    mockApplyRemotionSpecFixForAnnotation.mockReturnValue({
      specPath: path.join(process.cwd(), "specs", "section-1", "03_square.md"),
      note: "square should be yellow",
    });

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    const onLog = jest.fn();
    await executorFn(onLog);

    expect(mockApplyRemotionSpecFixForAnnotation).toHaveBeenCalledWith(
      process.cwd(),
      expect.objectContaining({ id: "section-1" }),
      expect.objectContaining({ id: "ann-rspec", timestamp: 3.4 })
    );
    expect(onLog).toHaveBeenCalledWith(
      expect.stringContaining("Updated Remotion spec")
    );
    expect(mockRunClaudeFix).toHaveBeenCalledWith(
      expect.any(String),
      "remotion/src/remotion/",
      onLog
    );
    expect(mockFixCommit).toHaveBeenCalledWith(
      "ann-rspec",
      expect.any(String),
      expect.arrayContaining([
        "remotion/src/remotion/",
        path.join("specs", "section-1", "03_square.md"),
      ])
    );
  });

  it("runs veo regeneration for affected sections", async () => {
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
    expect(mockRunPipelineStage).toHaveBeenCalledWith(
      "veo",
      { clips: ["section-1"] },
      expect.any(Function)
    );
  });

  it("rewrites the targeted Veo prompt before regenerating the resolved clip", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-v1",
        sectionId: "section-1",
        timestamp: 1.3,
        analysis: JSON.stringify({
          fixType: "veo",
          severity: "major",
          technicalAssessment: "add birds",
          suggestedFixes: [
            'Update the Veo prompt to: "Ocean wave at sunset with birds in the sky"',
          ],
          confidence: 0.9,
        }),
      }),
    ]);
    mockApplyVeoPromptFixForAnnotation.mockReturnValue({
      clipId: "ocean_wave_sunset",
      specPath: path.join(process.cwd(), "specs", "section-1", "02_ocean_wave_sunset.md"),
      prompt: "Ocean wave at sunset with birds in the sky",
    });

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    const onLog = jest.fn();
    await executorFn(onLog);

    expect(mockApplyVeoPromptFixForAnnotation).toHaveBeenCalledWith(
      process.cwd(),
      expect.objectContaining({ id: "section-1" }),
      expect.objectContaining({ id: "ann-v1", timestamp: 1.3 })
    );
    expect(mockRunPipelineStage).toHaveBeenCalledWith(
      "veo",
      { clips: ["ocean_wave_sunset"] },
      expect.any(Function)
    );
    expect(mockFixCommit).toHaveBeenCalledWith(
      "ann-v1",
      expect.any(String),
      [path.join("specs", "section-1", "02_ocean_wave_sunset.md")]
    );
    expect(mockRun).toHaveBeenCalledWith("fix-commit-sha", "ann-v1");
    expect(onLog).toHaveBeenCalledWith(
      expect.stringContaining("Updated Veo prompt for ocean_wave_sunset")
    );
    expect(onLog).toHaveBeenCalledWith(
      expect.stringContaining("Fix committed: fix-comm")
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

  it("marks processed fix annotations as resolved after successful completion", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-rdone",
        analysis: JSON.stringify({
          fixType: "remotion",
          severity: "major",
          technicalAssessment: "update shape",
          suggestedFixes: [],
          confidence: 0.9,
        }),
      }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    mockRun.mockClear();
    await executorFn(jest.fn());

    const resolvedUpdate = mockPrepare.mock.calls.find((call: any[]) =>
      (call[0] as string).includes("UPDATE annotations SET resolved = 1 WHERE id = ?")
    );

    expect(resolvedUpdate).toBeDefined();
    expect(mockRun).toHaveBeenCalledWith("ann-rdone");
  });

  it("does not mark a veo annotation resolved when no prompt rewrite was derived", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-veo-unresolved",
        analysis: JSON.stringify({
          fixType: "veo",
          severity: "major",
          technicalAssessment: "add balloons",
          suggestedFixes: [
            "Update the Veo prompt from 'old prompt' to 'new prompt with balloons'",
          ],
          confidence: 0.9,
        }),
      }),
    ]);
    mockApplyVeoPromptFixForAnnotation.mockReturnValue(null);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    const onLog = jest.fn();
    mockRun.mockClear();
    await executorFn(onLog);

    const resolvedUpdate = mockPrepare.mock.calls.find((call: any[]) =>
      (call[0] as string).includes("UPDATE annotations SET resolved = 1 WHERE id = ?")
    );

    expect(resolvedUpdate).toBeUndefined();
    expect(mockRun).not.toHaveBeenCalledWith("ann-veo-unresolved");
    expect(onLog).toHaveBeenCalledWith(
      expect.stringContaining("Leaving annotation ann-veo-unresolved unresolved")
    );
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
    expect(mockRenderSection.mock.calls[0][1]).toBe("outputs/sections/section-1.mp4");
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

  it("falls back to a PascalCase Section composition when project metadata is missing", async () => {
    mockGetSection.mockReturnValue(null);
    mockAll.mockReturnValue([
      makeDbRow({
        sectionId: "cold_open",
        analysis: JSON.stringify({ fixType: "remotion", severity: "major", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
    ]);

    await POST(makeRequest(), makeParams("cold_open"));

    const executorFn = mockRunJob.mock.calls[0][1];
    await executorFn(jest.fn());

    expect(mockRenderSection).toHaveBeenCalledWith(
      "ColdOpenSection",
      "outputs/sections/cold_open.mp4",
      expect.any(Function),
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
    mockStitchFullVideo.mockImplementation(async () => {
      callOrder.push("stitchFullVideo");
    });

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    await executorFn(jest.fn());

    expect(callOrder).toEqual(["claudeFix", "renderSection", "stitchFullVideo"]);
  });

  it("normalizes stale full-video annotations to the effective section before rendering", async () => {
    const project = {
      sections: [
        {
          id: "section-1",
          label: "Section One",
          compositionId: "SectionOneComposition",
          durationSeconds: 11,
          offsetSeconds: 0,
        },
        {
          id: "section-2",
          label: "Section Two",
          compositionId: "SectionTwoComposition",
          durationSeconds: 12,
          offsetSeconds: 11,
        },
      ],
    };
    mockLoadProject.mockReturnValue(project);
    mockGetSection.mockImplementation((targetSectionId: string) =>
      project.sections.find((section) => section.id === targetSectionId) ?? null
    );
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-global",
        sectionId: "section-1",
        timestamp: 16.8,
        videoFile: "/api/video/outputs/full_video.mp4?v=123",
        analysis: JSON.stringify({
          fixType: "remotion",
          severity: "major",
          technicalAssessment: "",
          suggestedFixes: [],
          confidence: 0.9,
        }),
      }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    await executorFn(jest.fn());

    expect(mockRunClaudeFix.mock.calls[0][0]).toContain('"section-2" section');
    expect(mockRenderSection).toHaveBeenCalledWith(
      "SectionTwoComposition",
      "outputs/sections/section-2.mp4",
      expect.any(Function)
    );
    expect(mockRun).toHaveBeenCalledWith("section-2", 5.800000000000001, "ann-global");
  });

  it("queries explicit annotationIds across sections instead of filtering to the route section", async () => {
    const request = new Request("http://localhost/api/sections/section-1/resolve-batch", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ annotationIds: ["ann-a", "ann-b"] }),
    });
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-a",
        sectionId: "section-1",
        analysis: JSON.stringify({ fixType: "remotion", severity: "major", technicalAssessment: "", suggestedFixes: [], confidence: 0.9 }),
      }),
    ]);

    await POST(request, makeParams("section-1"));

    const sql = mockPrepare.mock.calls[0][0] as string;
    expect(sql).toContain("WHERE id IN");
    expect(sql).not.toContain("sectionId = ?");
    expect(mockAll).toHaveBeenCalledWith("ann-a", "ann-b");
  });

  it("runs the veo stage for normalized veo annotations and renders the normalized section", async () => {
    const project = {
      sections: [
        {
          id: "section-1",
          label: "Section One",
          compositionId: "SectionOneComposition",
          durationSeconds: 11,
          offsetSeconds: 0,
        },
        {
          id: "section-2",
          label: "Section Two",
          compositionId: "SectionTwoComposition",
          durationSeconds: 12,
          offsetSeconds: 11,
        },
      ],
    };
    mockLoadProject.mockReturnValue(project);
    mockGetSection.mockImplementation((targetSectionId: string) =>
      project.sections.find((section) => section.id === targetSectionId) ?? null
    );
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-veo",
        sectionId: "section-1",
        timestamp: 16.5,
        videoFile: "/api/video/outputs/full_video.mp4?v=123",
        analysis: JSON.stringify({
          fixType: "veo",
          severity: "major",
          technicalAssessment: "",
          suggestedFixes: [],
          confidence: 0.9,
        }),
      }),
    ]);

    await POST(makeRequest(), makeParams("section-1"));

    const executorFn = mockRunJob.mock.calls[0][1];
    await executorFn(jest.fn());

    expect(mockRunPipelineStage).toHaveBeenCalledWith(
      "veo",
      { clips: ["section-2"] },
      expect.any(Function)
    );
    expect(mockRenderSection).toHaveBeenCalledWith(
      "SectionTwoComposition",
      "outputs/sections/section-2.mp4",
      expect.any(Function)
    );
  });

  it("syncs regenerated Veo outputs into remotion/public before rerendering", async () => {
    const project = {
      sections: [
        {
          id: "veo_section",
          label: "Veo Section",
          compositionId: "VeoSection",
          durationSeconds: 12,
          offsetSeconds: 0,
          specDir: "veo_section",
        },
      ],
    };
    mockLoadProject.mockReturnValue(project);
    mockGetSection.mockImplementation((targetSectionId: string) =>
      project.sections.find((section) => section.id === targetSectionId) ?? null
    );
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-veo-sync",
        sectionId: "veo_section",
        timestamp: 1.3,
        analysis: JSON.stringify({
          fixType: "veo",
          severity: "major",
          technicalAssessment: "add birds",
          suggestedFixes: [
            'Update the Veo prompt to: "Ocean wave at sunset with birds in the sky"',
          ],
          confidence: 0.9,
        }),
      }),
    ]);
    mockApplyVeoPromptFixForAnnotation.mockReturnValue({
      clipId: "ocean_wave_sunset",
      specPath: path.join(process.cwd(), "specs", "veo_section", "02_ocean_wave_sunset.md"),
      prompt: "Ocean wave at sunset with birds in the sky",
    });
    (fsPromises.readdir as jest.Mock).mockResolvedValue([
      {
        name: "ocean_wave_sunset.mp4",
        isFile: () => true,
      },
      {
        name: "ocean_wave_sunset_validation_frame.png",
        isFile: () => true,
      },
    ]);

    await POST(makeRequest(), makeParams("veo_section"));

    const executorFn = mockRunJob.mock.calls[0][1];
    const onLog = jest.fn();
    await executorFn(onLog);

    expect(fsPromises.copyFile).toHaveBeenCalledWith(
      path.join(process.cwd(), "outputs", "veo", "ocean_wave_sunset.mp4"),
      path.join(process.cwd(), "remotion", "public", "veo", "ocean_wave_sunset.mp4")
    );
    expect(fsPromises.copyFile).not.toHaveBeenCalledWith(
      expect.stringContaining("validation_frame"),
      expect.any(String)
    );
    expect(onLog).toHaveBeenCalledWith("Syncing staged Veo assets...");
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
    expect(prompt).toContain("section-1");
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
    expect(prompt).toMatch(/^You are a Remotion developer/);
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

/**
 * Tests for app/api/pipeline/status/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_pipeline_status_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. GET /api/pipeline/status — returns { stages: Record<PipelineStage, StageStatusEntry> }
 *   2. Missing stages filled with { status: 'not_started', lastJobId: null, error: null }
 *   3. No authentication required (GET takes no request parameter)
 *   4. Returns HTTP 500 with { error: string } on DB errors
 *   5. export const dynamic = 'force-dynamic'
 *   6. PIPELINE_STAGES lists all 10 stages
 *   7. Uses NextResponse.json() for responses
 *   8. Simple SELECT query from pipeline_status table
 */

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockAll = jest.fn();
const mockPrepare = jest.fn(() => ({ all: mockAll }));
const mockGetDb = jest.fn(() => ({ prepare: mockPrepare }));
const mockIsCompositionArtifactSetStale = jest.fn();
const mockExistsSync = jest.fn();
const mockReadFileSync = jest.fn();
const mockReaddirSync = jest.fn();
const mockStatSync = jest.fn();
const mockLoadProject = jest.fn();

jest.mock("@/lib/db", () => ({
  getDb: (...args: unknown[]) => mockGetDb(...args),
}));

jest.mock("@/app/api/pipeline/_lib/composition-manifest", () => ({
  isCompositionArtifactSetStale: (...args: unknown[]) =>
    mockIsCompositionArtifactSetStale(...args),
}));

jest.mock("fs", () => ({
  __esModule: true,
  default: {
    existsSync: (...args: unknown[]) => mockExistsSync(...args),
    readFileSync: (...args: unknown[]) => mockReadFileSync(...args),
    readdirSync: (...args: unknown[]) => mockReaddirSync(...args),
    statSync: (...args: unknown[]) => mockStatSync(...args),
  },
  existsSync: (...args: unknown[]) => mockExistsSync(...args),
  readFileSync: (...args: unknown[]) => mockReadFileSync(...args),
  readdirSync: (...args: unknown[]) => mockReaddirSync(...args),
  statSync: (...args: unknown[]) => mockStatSync(...args),
}));

jest.mock("@/lib/projects", () => ({
  getProjectDir: () => "/test/project",
}));

jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
}));

// Import after mocking
import { GET, dynamic } from "../app/api/pipeline/status/route";

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

const ALL_STAGES = [
  "setup",
  "script",
  "tts-script",
  "tts-render",
  "audio-sync",
  "specs",
  "veo",
  "compositions",
  "render",
  "audit",
] as const;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Extracts JSON body and status from a NextResponse. */
async function parseResponse(
  response: Response
): Promise<{ status: number; body: any }> {
  const body = await response.json();
  return { status: response.status, body };
}

// ---------------------------------------------------------------------------
// Setup
// ---------------------------------------------------------------------------

beforeEach(() => {
  jest.resetAllMocks();
  // Re-wire mockPrepare after resetAllMocks
  mockPrepare.mockReturnValue({ all: mockAll });
  mockGetDb.mockReturnValue({ prepare: mockPrepare });
  mockIsCompositionArtifactSetStale.mockReturnValue(false);
  mockExistsSync.mockReturnValue(false);
  mockReadFileSync.mockReset();
  mockReaddirSync.mockReturnValue([]);
  mockStatSync.mockReset();
  mockLoadProject.mockReturnValue({
    sections: [],
  });
  // Suppress console.error during tests
  jest.spyOn(console, "error").mockImplementation(() => {});
});

afterEach(() => {
  jest.restoreAllMocks();
});

// ---------------------------------------------------------------------------
// 1. dynamic export
// ---------------------------------------------------------------------------

describe("dynamic export", () => {
  it("exports dynamic = 'force-dynamic' to prevent static optimization", () => {
    expect(dynamic).toBe("force-dynamic");
  });
});

// ---------------------------------------------------------------------------
// 2. GET /api/pipeline/status — all stages present in DB
// ---------------------------------------------------------------------------

describe("GET /api/pipeline/status — all stages in DB", () => {
  it("returns status 200 with stages map", async () => {
    mockAll.mockReturnValue(
      ALL_STAGES.map((stage) => ({
        stage,
        status: "done",
        lastJobId: `job-${stage}`,
        error: null,
        updatedAt: "2026-03-13T23:50:47.344Z",
      }))
    );

    const response = await GET();
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body.stages).toBeDefined();
  });

  it("returns all 10 stages in the response", async () => {
    mockAll.mockReturnValue(
      ALL_STAGES.map((stage) => ({
        stage,
        status: "done",
        lastJobId: `job-${stage}`,
        error: null,
        updatedAt: "2026-03-13T23:50:47.344Z",
      }))
    );

    const response = await GET();
    const { body } = await parseResponse(response);

    const stageKeys = Object.keys(body.stages);
    expect(stageKeys).toHaveLength(10);
    for (const stage of ALL_STAGES) {
      expect(body.stages[stage]).toBeDefined();
    }
  });

  it("maps DB rows to StageStatusEntry shape", async () => {
    mockAll.mockReturnValue([
      {
        stage: "render",
        status: "running",
        lastJobId: "job-42",
        error: null,
        updatedAt: "2026-03-13T23:50:47.344Z",
      },
    ]);

    const response = await GET();
    const { body } = await parseResponse(response);

    expect(body.stages["render"]).toEqual({
      status: "running",
      lastJobId: "job-42",
      error: null,
      updatedAt: "2026-03-13T23:50:47.344Z",
    });
  });

  it("preserves error message from DB row", async () => {
    mockAll.mockReturnValue([
      {
        stage: "veo",
        status: "error",
        lastJobId: "job-99",
        error: "API rate limit exceeded",
        updatedAt: "2026-03-13T23:50:47.344Z",
      },
    ]);

    const response = await GET();
    const { body } = await parseResponse(response);

    expect(body.stages["veo"]).toEqual({
      status: "error",
      lastJobId: "job-99",
      error: "API rate limit exceeded",
      updatedAt: "2026-03-13T23:50:47.344Z",
    });
  });

  it("includes updatedAt from the pipeline_status table", async () => {
    mockAll.mockReturnValue([
      {
        stage: "compositions",
        status: "done",
        lastJobId: "job-101",
        error: null,
        updatedAt: "2026-03-13T21:47:24.446Z",
      },
    ]);

    const response = await GET();
    const { body } = await parseResponse(response);

    expect(body.stages["compositions"].updatedAt).toBe("2026-03-13T21:47:24.446Z");
  });

  it("marks the compositions stage as stale when generated artifacts are out of date", async () => {
    mockIsCompositionArtifactSetStale.mockReturnValue(true);
    mockAll.mockReturnValue([
      {
        stage: "compositions",
        status: "done",
        lastJobId: "job-101",
        error: null,
        updatedAt: "2026-03-13T21:47:24.446Z",
      },
    ]);

    const response = await GET();
    const { body } = await parseResponse(response);

    expect(body.stages["compositions"].stale).toBe(true);
  });

  it("marks tts-render stale when the current manifest has segments without WAV outputs", async () => {
    mockAll.mockReturnValue([
      {
        stage: "tts-render",
        status: "done",
        lastJobId: "job-tts",
        error: null,
        updatedAt: "2026-03-25T20:00:00.000Z",
      },
    ]);
    mockExistsSync.mockImplementation((filePath: string) =>
      filePath.endsWith("/outputs/tts/segments.json")
    );
    mockReadFileSync.mockImplementation((filePath: string) => {
      if (filePath.endsWith("/outputs/tts/segments.json")) {
        return JSON.stringify({
          segments: [{ id: "part3_mold_parts_001", text: "First line." }],
        });
      }
      return "";
    });
    mockStatSync.mockImplementation((filePath: string) => {
      if (filePath.endsWith("/outputs/tts/segments.json")) {
        return { mtimeMs: 2000 };
      }
      throw Object.assign(new Error("ENOENT"), { code: "ENOENT" });
    });

    const response = await GET();
    const { body } = await parseResponse(response);

    expect(body.stages["tts-render"].stale).toBe(true);
  });

  it("marks audio-sync stale when section audio is newer than sync artifacts", async () => {
    mockAll.mockReturnValue([
      {
        stage: "audio-sync",
        status: "done",
        lastJobId: "job-sync",
        error: null,
        updatedAt: "2026-03-25T20:00:00.000Z",
      },
    ]);
    mockLoadProject.mockReturnValue({
      sections: [{ id: "part1_economics" }],
    });
    mockExistsSync.mockImplementation((filePath: string) =>
      filePath.endsWith("/outputs/tts/segments.json")
    );
    mockReadFileSync.mockImplementation((filePath: string) => {
      if (filePath.endsWith("/outputs/tts/segments.json")) {
        return JSON.stringify({
          segments: [
            {
              id: "part1_economics_001",
              sectionId: "part1_economics",
              text: "Line one.",
            },
          ],
        });
      }
      return "";
    });
    mockReaddirSync.mockImplementation((dirPath: string) => {
      if (dirPath.endsWith("/outputs/tts")) {
        return ["part1_economics_001.wav"];
      }
      return [];
    });
    mockStatSync.mockImplementation((filePath: string) => {
      if (filePath.endsWith("/outputs/tts/segments.json")) {
        return { mtimeMs: 1000 };
      }
      if (filePath.endsWith("/outputs/tts/part1_economics_001.wav")) {
        return { mtimeMs: 3000 };
      }
      if (
        filePath.endsWith("/outputs/tts/part1_economics/word_timestamps.json") ||
        filePath.endsWith("/outputs/tts/part1_economics/segment_validation.json")
      ) {
        return { mtimeMs: 2000 };
      }
      throw Object.assign(new Error("ENOENT"), { code: "ENOENT" });
    });

    const response = await GET();
    const { body } = await parseResponse(response);

    expect(body.stages["audio-sync"].stale).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// 3. GET — missing stages filled with defaults
// ---------------------------------------------------------------------------

describe("GET /api/pipeline/status — missing stages default", () => {
  it("fills missing stages with not_started defaults when DB returns empty", async () => {
    mockAll.mockReturnValue([]);

    const response = await GET();
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    for (const stage of ALL_STAGES) {
      expect(body.stages[stage]).toEqual({
        status: "not_started",
        lastJobId: null,
        error: null,
        updatedAt: null,
      });
    }
  });

  it("fills only missing stages while preserving existing ones", async () => {
    mockAll.mockReturnValue([
      {
        stage: "setup",
        status: "done",
        lastJobId: "job-1",
        error: null,
        updatedAt: "2026-03-13T21:47:24.446Z",
      },
      {
        stage: "script",
        status: "error",
        lastJobId: "job-2",
        error: "Script parse error",
        updatedAt: "2026-03-13T22:47:24.446Z",
      },
    ]);

    const response = await GET();
    const { body } = await parseResponse(response);

    // Existing stages preserved
    expect(body.stages["setup"]).toEqual({
      status: "done",
      lastJobId: "job-1",
      error: null,
      updatedAt: "2026-03-13T21:47:24.446Z",
    });
    expect(body.stages["script"]).toEqual({
      status: "error",
      lastJobId: "job-2",
      error: "Script parse error",
      updatedAt: "2026-03-13T22:47:24.446Z",
    });

    // Missing stages get defaults
    const missingStages = ALL_STAGES.filter(
      (s) => s !== "setup" && s !== "script"
    );
    for (const stage of missingStages) {
      expect(body.stages[stage]).toEqual({
        status: "not_started",
        lastJobId: null,
        error: null,
        updatedAt: null,
      });
    }
  });

  it("returns all 10 stages even if only one row exists in DB", async () => {
    mockAll.mockReturnValue([
      {
        stage: "audit",
        status: "running",
        lastJobId: "job-a",
        error: null,
        updatedAt: "2026-03-13T23:50:47.344Z",
      },
    ]);

    const response = await GET();
    const { body } = await parseResponse(response);

    expect(Object.keys(body.stages)).toHaveLength(10);
    expect(body.stages["audit"].status).toBe("running");
    expect(body.stages["setup"].status).toBe("not_started");
  });
});

// ---------------------------------------------------------------------------
// 4. GET — DB query
// ---------------------------------------------------------------------------

describe("GET /api/pipeline/status — DB interaction", () => {
  it("calls getDb() to obtain the database", async () => {
    mockAll.mockReturnValue([]);

    await GET();

    expect(mockGetDb).toHaveBeenCalledTimes(1);
  });

  it("prepares a SELECT * FROM pipeline_status query", async () => {
    mockAll.mockReturnValue([]);

    await GET();

    expect(mockPrepare).toHaveBeenCalledWith("SELECT * FROM pipeline_status");
  });

  it("calls .all() on the prepared statement", async () => {
    mockAll.mockReturnValue([]);

    await GET();

    expect(mockAll).toHaveBeenCalledTimes(1);
  });
});

// ---------------------------------------------------------------------------
// 5. GET — error handling (HTTP 500)
// ---------------------------------------------------------------------------

describe("GET /api/pipeline/status — error handling", () => {
  it("returns 500 with error message when getDb throws", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("Database connection failed");
    });

    const response = await GET();
    const { status, body } = await parseResponse(response);

    expect(status).toBe(500);
    expect(body.error).toBeDefined();
    expect(typeof body.error).toBe("string");
  });

  it("returns 500 when prepare throws", async () => {
    mockPrepare.mockImplementation(() => {
      throw new Error("Table not found");
    });

    const response = await GET();
    const { status, body } = await parseResponse(response);

    expect(status).toBe(500);
    expect(body.error).toBeDefined();
  });

  it("returns 500 when .all() throws", async () => {
    mockAll.mockImplementation(() => {
      throw new Error("Disk I/O error");
    });

    const response = await GET();
    const { status, body } = await parseResponse(response);

    expect(status).toBe(500);
    expect(body.error).toBeDefined();
  });

  it("logs error to console.error on DB failure", async () => {
    const consoleSpy = jest
      .spyOn(console, "error")
      .mockImplementation(() => {});
    mockGetDb.mockImplementation(() => {
      throw new Error("DB crash");
    });

    await GET();

    expect(consoleSpy).toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 6. GET — response format
// ---------------------------------------------------------------------------

describe("GET /api/pipeline/status — response format", () => {
  it("returns JSON content type via NextResponse.json()", async () => {
    mockAll.mockReturnValue([]);

    const response = await GET();

    expect(response.headers.get("content-type")).toMatch(/application\/json/);
  });

  it("wraps stages in a { stages: ... } envelope", async () => {
    mockAll.mockReturnValue([]);

    const response = await GET();
    const { body } = await parseResponse(response);

    expect(body).toHaveProperty("stages");
    expect(typeof body.stages).toBe("object");
  });

  it("GET function takes no parameters (no auth needed)", async () => {
    // The GET export should be callable with no arguments
    mockAll.mockReturnValue([]);
    const response = await GET();
    expect(response.status).toBe(200);
  });
});

// ---------------------------------------------------------------------------
// 7. Edge cases
// ---------------------------------------------------------------------------

describe("GET /api/pipeline/status — edge cases", () => {
  it("handles undefined lastJobId by coercing to null", async () => {
    mockAll.mockReturnValue([
      { stage: "setup", status: "done", lastJobId: undefined, error: undefined },
    ]);

    const response = await GET();
    const { body } = await parseResponse(response);

    expect(body.stages["setup"].lastJobId).toBeNull();
    expect(body.stages["setup"].error).toBeNull();
  });

  it("handles all stages present with mixed statuses", async () => {
    const statuses = [
      "done",
      "running",
      "error",
      "not_started",
      "done",
      "running",
      "error",
      "not_started",
      "done",
      "running",
    ];
    mockAll.mockReturnValue(
      ALL_STAGES.map((stage, i) => ({
        stage,
        status: statuses[i],
        lastJobId: `job-${i}`,
        error: statuses[i] === "error" ? "Some error" : null,
      }))
    );

    const response = await GET();
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(Object.keys(body.stages)).toHaveLength(10);
    expect(body.stages["tts-script"].status).toBe("error");
    expect(body.stages["tts-script"].error).toBe("Some error");
  });
});

// ---------------------------------------------------------------------------
// 8. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/pipeline/status/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    const fs = jest.requireActual("fs");
    const path = require("path");
    sourceCode = fs.readFileSync(
      path.join(
        __dirname,
        "..",
        "app",
        "api",
        "pipeline",
        "status",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async function GET", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+GET/);
  });

  it("exports dynamic = 'force-dynamic'", () => {
    expect(sourceCode).toMatch(
      /export\s+const\s+dynamic\s*=\s*["']force-dynamic["']/
    );
  });

  it("imports getDb from @/lib/db", () => {
    expect(sourceCode).toMatch(/@\/lib\/db/);
    expect(sourceCode).toMatch(/getDb/);
  });

  it("imports PipelineStage and StageStatus from @/lib/types", () => {
    expect(sourceCode).toMatch(/@\/lib\/types/);
    expect(sourceCode).toMatch(/PipelineStage/);
    expect(sourceCode).toMatch(/StageStatus/);
  });

  it("defines PIPELINE_STAGES constant with all 10 stages", () => {
    expect(sourceCode).toMatch(/PIPELINE_STAGES/);
    for (const stage of ALL_STAGES) {
      expect(sourceCode).toContain(`"${stage}"`);
    }
  });

  it("uses db.prepare('SELECT * FROM pipeline_status').all()", () => {
    expect(sourceCode).toMatch(/db\.prepare\s*\(\s*["']SELECT \* FROM pipeline_status["']\s*\)\.all\(\)/);
  });

  it("uses NextResponse.json() for responses", () => {
    expect(sourceCode).toMatch(/NextResponse\.json\(/);
  });

  it("defines StageStatusEntry type with status, lastJobId, error", () => {
    expect(sourceCode).toMatch(/StageStatusEntry/);
    expect(sourceCode).toMatch(/status:\s*StageStatus/);
    expect(sourceCode).toMatch(/lastJobId:\s*string\s*\|\s*null/);
    expect(sourceCode).toMatch(/error:\s*string\s*\|\s*null/);
    expect(sourceCode).toMatch(/updatedAt:\s*string\s*\|\s*null/);
  });

  it("GET function has no request parameter", () => {
    // Should be GET() or GET(): ... not GET(request: ...)
    expect(sourceCode).toMatch(/export\s+async\s+function\s+GET\s*\(\s*\)/);
  });
});

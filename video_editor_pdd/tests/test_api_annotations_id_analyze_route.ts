/**
 * Tests for app/api/annotations/[id]/analyze/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_annotations_id_analyze_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. POST /api/annotations/[id]/analyze — triggers runClaudeAnalysis()
 *      - Loads annotation from DB by id; returns 404 if not found
 *      - Builds prompt with sectionId, text, and spec path
 *      - Writes compositeDataUrl to a temp PNG file
 *      - Calls runClaudeAnalysis(prompt, onLog)
 *      - Updates annotation.analysis in DB with returned AnnotationAnalysis JSON
 *      - Returns { annotation: Annotation } with updated record
 *   2. No authentication required
 *   3. Export dynamic = 'force-dynamic'
 *   4. Temp file cleanup in finally block
 *   5. Returns 500 on Claude analysis error
 */

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockGet = jest.fn();
const mockRun = jest.fn();
const mockPrepare = jest.fn(() => ({
  get: mockGet,
  run: mockRun,
}));
const mockDb = { prepare: mockPrepare };
const mockGetDb = jest.fn(() => mockDb);

jest.mock("@/lib/db", () => ({
  getDb: () => mockGetDb(),
}));

const mockRunClaudeAnalysis = jest.fn();
jest.mock("@/lib/claude", () => ({
  runClaudeAnalysis: (...args: any[]) => mockRunClaudeAnalysis(...args),
}));

const mockLoadProject = jest.fn();
jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
}));

// Mock fs for temp file operations
const mockWriteFileSync = jest.fn();
const mockExistsSync = jest.fn();
const mockUnlinkSync = jest.fn();
jest.mock("fs", () => ({
  writeFileSync: (...args: any[]) => mockWriteFileSync(...args),
  existsSync: (...args: any[]) => mockExistsSync(...args),
  unlinkSync: (...args: any[]) => mockUnlinkSync(...args),
  readFileSync: jest.requireActual("fs").readFileSync,
}));

// Import after mock setup
import { POST, dynamic } from "../app/api/annotations/[id]/analyze/route";
import fs from "fs";
import path from "path";
import os from "os";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Creates a mock Request object. */
function makeRequest(id: string): Request {
  return new Request(`http://localhost/api/annotations/${id}/analyze`, {
    method: "POST",
  });
}

/** Creates the params object matching Next.js App Router dynamic route. */
function makeParams(id: string): { params: { id: string } } {
  return { params: { id } };
}

/** Sample base64 composite data URL. */
const SAMPLE_COMPOSITE =
  "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==";

/** Returns a mock DB row as returned by better-sqlite3. */
function makeDbRow(overrides: Record<string, unknown> = {}) {
  return {
    id: "ann-123",
    sectionId: "section-1",
    timestamp: 5.0,
    text: "Fix the color grading here",
    videoFile: "output/video.mp4",
    drawingDataUrl: "data:image/png;base64,drawing",
    compositeDataUrl: SAMPLE_COMPOSITE,
    analysis: null,
    resolved: 0,
    resolveJobId: null,
    createdAt: "2025-01-15T10:00:00.000Z",
    ...overrides,
  };
}

/** Sample AnnotationAnalysis returned by Claude. */
const SAMPLE_ANALYSIS = {
  severity: "major" as const,
  fixType: "remotion" as const,
  technicalAssessment: "Color grading is off in this section",
  suggestedFixes: ["Adjust contrast levels", "Apply color correction filter"],
  confidence: 0.85,
};

// ---------------------------------------------------------------------------
// Setup / Teardown
// ---------------------------------------------------------------------------

beforeEach(() => {
  mockGetDb.mockReset();
  mockGetDb.mockReturnValue(mockDb);
  mockPrepare.mockReset();
  mockPrepare.mockReturnValue({ get: mockGet, run: mockRun });
  mockGet.mockReset();
  mockRun.mockReset();
  mockRunClaudeAnalysis.mockReset();
  mockLoadProject.mockReset();
  mockLoadProject.mockReturnValue({
    sections: [
      { id: "section-1", durationSeconds: 11, offsetSeconds: 0 },
      { id: "section-2", durationSeconds: 12, offsetSeconds: 11 },
    ],
  });
  mockWriteFileSync.mockReset();
  mockExistsSync.mockReset();
  mockUnlinkSync.mockReset();
  jest.spyOn(console, "error").mockImplementation(() => {});
  jest.spyOn(console, "log").mockImplementation(() => {});
  jest.spyOn(console, "warn").mockImplementation(() => {});
});

afterEach(() => {
  jest.restoreAllMocks();
});

// ---------------------------------------------------------------------------
// 1. POST /api/annotations/[id]/analyze — successful analysis
// ---------------------------------------------------------------------------

describe("POST /api/annotations/[id]/analyze — successful analysis", () => {
  beforeEach(() => {
    // First call: initial lookup. Second call: re-read after update.
    const initialRow = makeDbRow();
    const updatedRow = makeDbRow({
      analysis: JSON.stringify(SAMPLE_ANALYSIS),
    });
    mockGet.mockReturnValueOnce(initialRow).mockReturnValueOnce(updatedRow);
    mockRunClaudeAnalysis.mockResolvedValue(SAMPLE_ANALYSIS);
    mockExistsSync.mockReturnValue(true);
  });

  it("returns 200 on successful analysis", async () => {
    const response = await POST(makeRequest("ann-123"), makeParams("ann-123"));

    expect(response.status).toBe(200);
  });

  it("returns { annotation } with the updated record", async () => {
    const response = await POST(makeRequest("ann-123"), makeParams("ann-123"));
    const body = await response.json();

    expect(body).toHaveProperty("annotation");
    expect(body.annotation.id).toBe("ann-123");
  });

  it("returns the annotation with deserialized analysis", async () => {
    const response = await POST(makeRequest("ann-123"), makeParams("ann-123"));
    const body = await response.json();

    expect(body.annotation.analysis).toEqual(SAMPLE_ANALYSIS);
  });

  it("calls getDb() to obtain the database", async () => {
    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    expect(mockGetDb).toHaveBeenCalled();
  });

  it("queries the database with the ID from params", async () => {
    await POST(makeRequest("ann-789"), makeParams("ann-789"));

    expect(mockPrepare).toHaveBeenCalled();
    const sql = mockPrepare.mock.calls[0][0] as string;
    expect(sql).toContain("SELECT * FROM annotations WHERE id = ?");
    expect(mockGet).toHaveBeenCalledWith("ann-789");
  });
});

// ---------------------------------------------------------------------------
// 2. POST — builds correct prompt
// ---------------------------------------------------------------------------

describe("POST — prompt building", () => {
  beforeEach(() => {
    const row = makeDbRow({
      sectionId: "intro",
      text: "Color is wrong",
    });
    const updatedRow = makeDbRow({
      sectionId: "intro",
      text: "Color is wrong",
      analysis: JSON.stringify(SAMPLE_ANALYSIS),
    });
    mockGet.mockReturnValueOnce(row).mockReturnValueOnce(updatedRow);
    mockRunClaudeAnalysis.mockResolvedValue(SAMPLE_ANALYSIS);
    mockExistsSync.mockReturnValue(true);
  });

  it("passes a prompt containing the sectionId", async () => {
    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    const promptArg = mockRunClaudeAnalysis.mock.calls[0][0] as string;
    expect(promptArg).toContain("section intro");
  });

  it("passes a prompt containing the annotation text", async () => {
    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    const promptArg = mockRunClaudeAnalysis.mock.calls[0][0] as string;
    expect(promptArg).toContain("Color is wrong");
  });

  it("passes a prompt referencing spec files path", async () => {
    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    const promptArg = mockRunClaudeAnalysis.mock.calls[0][0] as string;
    expect(promptArg).toContain("specs/intro/");
  });

  it("matches the exact prompt format from the spec", async () => {
    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    const promptArg = mockRunClaudeAnalysis.mock.calls[0][0] as string;
    expect(promptArg).toBe(
      "Analyze this annotation for section intro. Annotation text: Color is wrong. Review the spec files in specs/intro/ and the composite frame image provided."
    );
  });

  it("normalizes stale full-video annotations to the effective later section before prompting Claude", async () => {
    const row = makeDbRow({
      sectionId: "section-1",
      timestamp: 16.8,
      videoFile: "/api/video/outputs/full_video.mp4?v=123",
      text: "Swap the beach and forest",
    });
    const updatedRow = makeDbRow({
      sectionId: "section-2",
      timestamp: 5.8,
      videoFile: "/api/video/outputs/full_video.mp4?v=123",
      text: "Swap the beach and forest",
      analysis: JSON.stringify(SAMPLE_ANALYSIS),
    });
    mockGet.mockReset();
    mockGet.mockReturnValueOnce(row).mockReturnValueOnce(updatedRow);

    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    const promptArg = mockRunClaudeAnalysis.mock.calls[0][0] as string;
    expect(promptArg).toContain("section section-2");
    expect(promptArg).toContain("specs/section-2/");
    expect(mockRun).toHaveBeenCalledWith("section-2", 5.800000000000001, "ann-123");
  });
});

// ---------------------------------------------------------------------------
// 3. POST — temp file handling
// ---------------------------------------------------------------------------

describe("POST — temp file handling", () => {
  beforeEach(() => {
    const row = makeDbRow();
    const updatedRow = makeDbRow({
      analysis: JSON.stringify(SAMPLE_ANALYSIS),
    });
    mockGet.mockReturnValueOnce(row).mockReturnValueOnce(updatedRow);
    mockRunClaudeAnalysis.mockResolvedValue(SAMPLE_ANALYSIS);
    mockExistsSync.mockReturnValue(true);
  });

  it("writes compositeDataUrl to a temp PNG file", async () => {
    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    expect(mockWriteFileSync).toHaveBeenCalledTimes(1);
    const [filePath] = mockWriteFileSync.mock.calls[0];
    expect(filePath).toContain("annotation_ann-123_composite.png");
    expect(filePath).toContain(os.tmpdir());
  });

  it("decodes base64 data from compositeDataUrl before writing", async () => {
    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    const [, bufferArg] = mockWriteFileSync.mock.calls[0];
    expect(Buffer.isBuffer(bufferArg)).toBe(true);
  });

  it("cleans up temp file after successful analysis", async () => {
    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    expect(mockExistsSync).toHaveBeenCalled();
    expect(mockUnlinkSync).toHaveBeenCalledTimes(1);
  });

  it("cleans up temp file even when analysis fails", async () => {
    mockRunClaudeAnalysis.mockRejectedValue(new Error("Claude crashed"));
    mockGet.mockReset();
    mockGet.mockReturnValueOnce(makeDbRow());

    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    expect(mockExistsSync).toHaveBeenCalled();
    expect(mockUnlinkSync).toHaveBeenCalledTimes(1);
  });

  it("does not attempt to delete if temp file does not exist", async () => {
    mockExistsSync.mockReturnValue(false);

    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    expect(mockUnlinkSync).not.toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 4. POST — DB update after analysis
// ---------------------------------------------------------------------------

describe("POST — DB update after analysis", () => {
  beforeEach(() => {
    const row = makeDbRow();
    const updatedRow = makeDbRow({
      analysis: JSON.stringify(SAMPLE_ANALYSIS),
    });
    mockGet.mockReturnValueOnce(row).mockReturnValueOnce(updatedRow);
    mockRunClaudeAnalysis.mockResolvedValue(SAMPLE_ANALYSIS);
    mockExistsSync.mockReturnValue(true);
  });

  it("stores analysis JSON in DB via UPDATE", async () => {
    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    // Find the UPDATE call
    const updateCall = mockPrepare.mock.calls.find((call: any[]) =>
      (call[0] as string).includes("UPDATE")
    );
    expect(updateCall).toBeDefined();
    expect(updateCall![0]).toContain(
      "UPDATE annotations SET analysis = ? WHERE id = ?"
    );
  });

  it("passes JSON.stringify(analysis) and id to the UPDATE", async () => {
    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    expect(mockRun).toHaveBeenCalledWith(
      JSON.stringify(SAMPLE_ANALYSIS),
      "ann-123"
    );
  });

  it("re-reads the annotation from DB after update", async () => {
    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    // mockGet should be called twice: initial load + re-read after update
    expect(mockGet).toHaveBeenCalledTimes(2);
  });
});

// ---------------------------------------------------------------------------
// 5. POST — runClaudeAnalysis invocation
// ---------------------------------------------------------------------------

describe("POST — runClaudeAnalysis invocation", () => {
  beforeEach(() => {
    const row = makeDbRow();
    const updatedRow = makeDbRow({
      analysis: JSON.stringify(SAMPLE_ANALYSIS),
    });
    mockGet.mockReturnValueOnce(row).mockReturnValueOnce(updatedRow);
    mockRunClaudeAnalysis.mockResolvedValue(SAMPLE_ANALYSIS);
    mockExistsSync.mockReturnValue(true);
  });

  it("calls runClaudeAnalysis with the prompt", async () => {
    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    expect(mockRunClaudeAnalysis).toHaveBeenCalledTimes(1);
    const [prompt] = mockRunClaudeAnalysis.mock.calls[0];
    expect(typeof prompt).toBe("string");
    expect(prompt).toContain("Analyze this annotation");
  });

  it("passes an onLog callback to runClaudeAnalysis", async () => {
    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    const [, onLog] = mockRunClaudeAnalysis.mock.calls[0];
    expect(typeof onLog).toBe("function");
  });

  it("onLog callback logs via console.log", async () => {
    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    const [, onLog] = mockRunClaudeAnalysis.mock.calls[0];
    onLog("test log line");
    expect(console.log).toHaveBeenCalledWith("[Claude] test log line");
  });
});

// ---------------------------------------------------------------------------
// 6. POST — 404 not found
// ---------------------------------------------------------------------------

describe("POST /api/annotations/[id]/analyze — not found", () => {
  it("returns 404 when annotation does not exist", async () => {
    mockGet.mockReturnValue(undefined);

    const response = await POST(
      makeRequest("nonexistent"),
      makeParams("nonexistent")
    );

    expect(response.status).toBe(404);
  });

  it("returns { error: 'Annotation not found' } body on miss", async () => {
    mockGet.mockReturnValue(undefined);

    const response = await POST(
      makeRequest("nonexistent"),
      makeParams("nonexistent")
    );
    const body = await response.json();

    expect(body).toEqual({ error: "Annotation not found" });
  });

  it("does not call runClaudeAnalysis when annotation not found", async () => {
    mockGet.mockReturnValue(undefined);

    await POST(makeRequest("nonexistent"), makeParams("nonexistent"));

    expect(mockRunClaudeAnalysis).not.toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 7. POST — error handling (500)
// ---------------------------------------------------------------------------

describe("POST — error handling (500)", () => {
  it("returns 500 when runClaudeAnalysis throws", async () => {
    mockGet.mockReturnValue(makeDbRow());
    mockRunClaudeAnalysis.mockRejectedValue(new Error("Claude CLI timeout"));
    mockExistsSync.mockReturnValue(true);

    const response = await POST(makeRequest("ann-123"), makeParams("ann-123"));

    expect(response.status).toBe(500);
  });

  it("returns { error: 'Internal Server Error' } on analysis failure", async () => {
    mockGet.mockReturnValue(makeDbRow());
    mockRunClaudeAnalysis.mockRejectedValue(new Error("Claude CLI timeout"));
    mockExistsSync.mockReturnValue(true);

    const response = await POST(makeRequest("ann-123"), makeParams("ann-123"));
    const body = await response.json();

    expect(body).toEqual({ error: "Internal Server Error" });
  });

  it("propagates error when getDb throws (outside try/catch)", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("DB connection failed");
    });

    await expect(
      POST(makeRequest("ann-123"), makeParams("ann-123"))
    ).rejects.toThrow("DB connection failed");
  });

  it("returns 500 when annotation has no compositeDataUrl", async () => {
    mockGet.mockReturnValue(makeDbRow({ compositeDataUrl: null }));

    const response = await POST(makeRequest("ann-123"), makeParams("ann-123"));

    expect(response.status).toBe(500);
  });

  it("logs error to console.error on failure", async () => {
    mockGet.mockReturnValue(makeDbRow());
    mockRunClaudeAnalysis.mockRejectedValue(new Error("Unexpected error"));
    mockExistsSync.mockReturnValue(true);

    await POST(makeRequest("ann-123"), makeParams("ann-123"));

    expect(console.error).toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 8. No authentication required
// ---------------------------------------------------------------------------

describe("no authentication required", () => {
  beforeEach(() => {
    const row = makeDbRow();
    const updatedRow = makeDbRow({
      analysis: JSON.stringify(SAMPLE_ANALYSIS),
    });
    mockGet.mockReturnValueOnce(row).mockReturnValueOnce(updatedRow);
    mockRunClaudeAnalysis.mockResolvedValue(SAMPLE_ANALYSIS);
    mockExistsSync.mockReturnValue(true);
  });

  it("POST succeeds without any authorization header", async () => {
    const response = await POST(makeRequest("ann-123"), makeParams("ann-123"));

    expect(response.status).toBe(200);
  });

  it("POST succeeds with an authorization header present", async () => {
    const request = new Request(
      "http://localhost/api/annotations/ann-123/analyze",
      {
        method: "POST",
        headers: { Authorization: "Bearer fake-token" },
      }
    );

    const response = await POST(request, makeParams("ann-123"));

    expect(response.status).toBe(200);
  });
});

// ---------------------------------------------------------------------------
// 9. Export: dynamic = 'force-dynamic'
// ---------------------------------------------------------------------------

describe("dynamic export", () => {
  it("exports dynamic as 'force-dynamic'", () => {
    expect(dynamic).toBe("force-dynamic");
  });
});

// ---------------------------------------------------------------------------
// 10. Annotation shape mapping in response
// ---------------------------------------------------------------------------

describe("POST — annotation shape mapping in response", () => {
  it("maps all DB row fields to Annotation properties", async () => {
    const updatedRow = makeDbRow({
      analysis: JSON.stringify(SAMPLE_ANALYSIS),
      resolved: 1,
    });
    mockGet.mockReturnValueOnce(makeDbRow()).mockReturnValueOnce(updatedRow);
    mockRunClaudeAnalysis.mockResolvedValue(SAMPLE_ANALYSIS);
    mockExistsSync.mockReturnValue(true);

    const response = await POST(makeRequest("ann-123"), makeParams("ann-123"));
    const body = await response.json();
    const annotation = body.annotation;

    expect(annotation.id).toBe("ann-123");
    expect(annotation.sectionId).toBe("section-1");
    expect(annotation.timestamp).toBe(5.0);
    expect(annotation.text).toBe("Fix the color grading here");
    expect(annotation.videoFile).toBe("output/video.mp4");
    expect(annotation.drawingDataUrl).toBe("data:image/png;base64,drawing");
    expect(annotation.compositeDataUrl).toBe(SAMPLE_COMPOSITE);
    expect(annotation.analysis).toEqual(SAMPLE_ANALYSIS);
    expect(annotation.resolved).toBe(true);
    expect(annotation.resolveJobId).toBeNull();
    expect(annotation.createdAt).toBe("2025-01-15T10:00:00.000Z");
  });

  it("converts resolved integer (0) to boolean false", async () => {
    const updatedRow = makeDbRow({
      analysis: JSON.stringify(SAMPLE_ANALYSIS),
      resolved: 0,
    });
    mockGet.mockReturnValueOnce(makeDbRow()).mockReturnValueOnce(updatedRow);
    mockRunClaudeAnalysis.mockResolvedValue(SAMPLE_ANALYSIS);
    mockExistsSync.mockReturnValue(true);

    const response = await POST(makeRequest("ann-123"), makeParams("ann-123"));
    const body = await response.json();

    expect(body.annotation.resolved).toBe(false);
  });

  it("returns null for optional fields when DB values are undefined", async () => {
    const updatedRow = makeDbRow({
      analysis: JSON.stringify(SAMPLE_ANALYSIS),
      videoFile: undefined,
      drawingDataUrl: undefined,
      resolveJobId: undefined,
    });
    mockGet.mockReturnValueOnce(makeDbRow()).mockReturnValueOnce(updatedRow);
    mockRunClaudeAnalysis.mockResolvedValue(SAMPLE_ANALYSIS);
    mockExistsSync.mockReturnValue(true);

    const response = await POST(makeRequest("ann-123"), makeParams("ann-123"));
    const body = await response.json();

    expect(body.annotation.videoFile).toBeNull();
    expect(body.annotation.drawingDataUrl).toBeNull();
    expect(body.annotation.resolveJobId).toBeNull();
  });
});

// ---------------------------------------------------------------------------
// 11. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/annotations/[id]/analyze/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    const actualFs = jest.requireActual("fs");
    sourceCode = actualFs.readFileSync(
      path.join(
        __dirname,
        "..",
        "app",
        "api",
        "annotations",
        "[id]",
        "analyze",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async POST function", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+POST/);
  });

  it("imports getDb from @/lib/db", () => {
    expect(sourceCode).toMatch(/@\/lib\/db/);
    expect(sourceCode).toMatch(/getDb/);
  });

  it("imports runClaudeAnalysis from @/lib/claude", () => {
    expect(sourceCode).toMatch(/@\/lib\/claude/);
    expect(sourceCode).toMatch(/runClaudeAnalysis/);
  });

  it("imports NextResponse from next/server", () => {
    expect(sourceCode).toMatch(/NextResponse/);
    expect(sourceCode).toMatch(/next\/server/);
  });

  it("imports fs, os, and path modules", () => {
    expect(sourceCode).toMatch(/import\s+fs\s+from\s+["']fs["']/);
    expect(sourceCode).toMatch(/import\s+os\s+from\s+["']os["']/);
    expect(sourceCode).toMatch(/import\s+path\s+from\s+["']path["']/);
  });

  it("exports dynamic = 'force-dynamic'", () => {
    expect(sourceCode).toMatch(
      /export\s+const\s+dynamic\s*=\s*["']force-dynamic["']/
    );
  });

  it("queries annotations table with parameterized ID", () => {
    expect(sourceCode).toMatch(/SELECT \* FROM annotations WHERE id = \?/);
  });

  it("uses UPDATE annotations SET analysis", () => {
    expect(sourceCode).toMatch(
      /UPDATE annotations SET analysis = \? WHERE id = \?/
    );
  });

  it("writes compositeDataUrl to temp file using os.tmpdir()", () => {
    expect(sourceCode).toMatch(/os\.tmpdir\(\)/);
    expect(sourceCode).toMatch(/annotation_.*_composite\.png/);
  });

  it("handles 404 not found case", () => {
    expect(sourceCode).toMatch(/404/);
    expect(sourceCode).toMatch(/Annotation not found/);
  });

  it("handles 500 internal server error case", () => {
    expect(sourceCode).toMatch(/500/);
    expect(sourceCode).toMatch(/Internal Server Error/);
  });

  it("uses try/finally for temp file cleanup", () => {
    expect(sourceCode).toMatch(/finally/);
    expect(sourceCode).toMatch(/unlinkSync/);
  });

  it("splits base64 data from data URL prefix", () => {
    expect(sourceCode).toMatch(/split\(.*,.*\)\[1\]/);
    expect(sourceCode).toMatch(/base64/);
  });
});

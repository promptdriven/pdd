/**
 * Tests for app/api/export/route.ts
 *
 * Spec requirements verified:
 *   1. GET /api/export — exports all annotations as JSON
 *   2. Returns Content-Disposition header for download
 *   3. Returns Content-Type application/json
 *   4. Returns exportedAt, count, and annotations array
 *   5. Returns 500 on internal error
 *   6. Export dynamic = 'force-dynamic'
 */

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockAll = jest.fn();
const mockPrepare = jest.fn(() => ({
  all: mockAll,
}));
const mockDb = { prepare: mockPrepare };
const mockGetDb = jest.fn(() => mockDb);

jest.mock("@/lib/db", () => ({
  getDb: () => mockGetDb(),
}));

// Import after mock setup
import { GET, dynamic } from "../app/api/export/route";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function makeDbRow(overrides: Record<string, unknown> = {}) {
  return {
    id: "ann-123",
    sectionId: "section-1",
    timestamp: 5.0,
    text: "Some annotation",
    videoFile: "output/video.mp4",
    drawingDataUrl: null,
    compositeDataUrl: null,
    analysis: null,
    resolved: 0,
    resolveJobId: null,
    createdAt: "2025-01-15T10:00:00.000Z",
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Setup / Teardown
// ---------------------------------------------------------------------------

beforeEach(() => {
  mockGetDb.mockReset();
  mockGetDb.mockReturnValue(mockDb);
  mockPrepare.mockReset();
  mockPrepare.mockReturnValue({ all: mockAll });
  mockAll.mockReset();
  jest.spyOn(console, "error").mockImplementation(() => {});
});

afterEach(() => {
  jest.restoreAllMocks();
});

// ---------------------------------------------------------------------------
// 1. dynamic export
// ---------------------------------------------------------------------------

describe("dynamic export", () => {
  it("exports dynamic as 'force-dynamic'", () => {
    expect(dynamic).toBe("force-dynamic");
  });
});

// ---------------------------------------------------------------------------
// 2. GET /api/export — successful export
// ---------------------------------------------------------------------------

describe("GET /api/export — successful export", () => {
  it("returns 200 status", async () => {
    mockAll.mockReturnValue([makeDbRow()]);
    const response = await GET();
    expect(response.status).toBe(200);
  });

  it("returns Content-Type application/json", async () => {
    mockAll.mockReturnValue([]);
    const response = await GET();
    const contentType = response.headers.get("Content-Type");
    expect(contentType).toContain("application/json");
  });

  it("returns Content-Disposition attachment header", async () => {
    mockAll.mockReturnValue([]);
    const response = await GET();
    const disposition = response.headers.get("Content-Disposition");
    expect(disposition).toContain("attachment");
    expect(disposition).toContain("annotations-export.json");
  });

  it("returns exportedAt timestamp", async () => {
    mockAll.mockReturnValue([]);
    const response = await GET();
    const body = JSON.parse(await response.text());
    expect(body).toHaveProperty("exportedAt");
    expect(typeof body.exportedAt).toBe("string");
  });

  it("returns count matching annotations length", async () => {
    mockAll.mockReturnValue([makeDbRow(), makeDbRow({ id: "ann-456" })]);
    const response = await GET();
    const body = JSON.parse(await response.text());
    expect(body.count).toBe(2);
    expect(body.annotations).toHaveLength(2);
  });

  it("returns empty annotations array when none exist", async () => {
    mockAll.mockReturnValue([]);
    const response = await GET();
    const body = JSON.parse(await response.text());
    expect(body.count).toBe(0);
    expect(body.annotations).toEqual([]);
  });

  it("maps DB rows to annotation objects correctly", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-abc",
        sectionId: "section-2",
        timestamp: 7.5,
        text: "Fix this",
        resolved: 1,
      }),
    ]);

    const response = await GET();
    const body = JSON.parse(await response.text());
    const ann = body.annotations[0];

    expect(ann.id).toBe("ann-abc");
    expect(ann.sectionId).toBe("section-2");
    expect(ann.timestamp).toBe(7.5);
    expect(ann.text).toBe("Fix this");
    expect(ann.resolved).toBe(true);
  });

  it("deserializes analysis JSON", async () => {
    const analysis = { severity: "major", fixType: "remotion", technicalAssessment: "text", suggestedFixes: [], confidence: 0.9 };
    mockAll.mockReturnValue([makeDbRow({ analysis: JSON.stringify(analysis) })]);

    const response = await GET();
    const body = JSON.parse(await response.text());
    expect(body.annotations[0].analysis).toEqual(analysis);
  });

  it("returns null for analysis when DB value is null", async () => {
    mockAll.mockReturnValue([makeDbRow({ analysis: null })]);

    const response = await GET();
    const body = JSON.parse(await response.text());
    expect(body.annotations[0].analysis).toBeNull();
  });

  it("queries annotations ordered by createdAt ASC", async () => {
    mockAll.mockReturnValue([]);
    await GET();

    const sql = mockPrepare.mock.calls[0][0] as string;
    expect(sql).toContain("SELECT * FROM annotations");
    expect(sql).toContain("ORDER BY createdAt ASC");
  });
});

// ---------------------------------------------------------------------------
// 3. GET /api/export — error handling
// ---------------------------------------------------------------------------

describe("GET /api/export — error handling", () => {
  it("returns 500 when getDb throws", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("DB connection failed");
    });

    const response = await GET();
    expect(response.status).toBe(500);
  });

  it("returns { error: 'Internal Server Error' } body on failure", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("DB connection failed");
    });

    const response = await GET();
    const body = await response.json();
    expect(body).toEqual({ error: "Internal Server Error" });
  });

  it("logs error to console.error on failure", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("Unexpected error");
    });

    await GET();
    expect(console.error).toHaveBeenCalled();
  });
});

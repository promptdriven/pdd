/**
 * Tests for app/api/annotations/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_annotations_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. POST /api/annotations — creates a new annotation
 *      - Accepts CreateAnnotationInput
 *      - Saves fields to DB
 *      - Returns the created Annotation object with all fields
 *   2. GET /api/annotations?section=X — returns annotations for a section
 *      - Optional section query param to filter by sectionId
 *      - Returns all annotations if no section filter
 *      - Returns { annotations: Annotation[] } ordered by timestamp ascending
 *   3. No authentication required
 *   4. Validates required fields (sectionId, text) and returns 400 if missing
 *   5. Generates UUID for annotation ID via crypto.randomUUID()
 *   6. analysis starts as NULL
 *   7. resolved defaults to false (0 in DB)
 *   8. Deserializes analysis_json → analysis when reading from DB
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

const MOCK_UUID = "aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee";
jest.mock("crypto", () => ({
  randomUUID: () => MOCK_UUID,
}));

const mockLoadProject = jest.fn();
jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
}));

// Import after mock setup
import { GET, POST } from "../app/api/annotations/route";
import { NextRequest } from "next/server";
import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Creates a NextRequest for GET with optional section query param. */
function makeGetRequest(section?: string): NextRequest {
  const url = section
    ? `http://localhost/api/annotations?section=${section}`
    : "http://localhost/api/annotations";
  return new NextRequest(url, { method: "GET" });
}

/** Creates a NextRequest for POST with a JSON body. */
function makePostRequest(body: Record<string, unknown>): NextRequest {
  return new NextRequest("http://localhost/api/annotations", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(body),
  });
}

/** Returns a valid POST body with all fields. */
function validPostBody() {
  return {
    sectionId: "section-1",
    timestamp: 5.5,
    text: "Fix the color grading here",
    drawingDataUrl: "data:image/png;base64,abc123",
    compositeDataUrl: "data:image/png;base64,xyz789",
    videoFile: "output/sections/intro.mp4",
  };
}

/** Returns a minimal valid POST body (only required fields). */
function minimalPostBody() {
  return {
    sectionId: "section-1",
    text: "Needs improvement",
  };
}

/** Returns a mock DB row as returned by better-sqlite3. */
function makeDbRow(overrides: Record<string, unknown> = {}) {
  return {
    id: "ann-123",
    sectionId: "section-1",
    timestamp: 5.0,
    text: "Some annotation",
    videoFile: "output/video.mp4",
    drawingDataUrl: "data:image/png;base64,drawing",
    compositeDataUrl: "data:image/png;base64,composite",
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
  mockPrepare.mockReturnValue({ all: mockAll, run: mockRun });
  mockAll.mockReset();
  mockRun.mockReset();
  mockLoadProject.mockReset();
  mockLoadProject.mockReturnValue({
    sections: [
      { id: "section-1", durationSeconds: 11, offsetSeconds: 0 },
      { id: "section-2", durationSeconds: 12, offsetSeconds: 11 },
    ],
  });
  jest.spyOn(console, "error").mockImplementation(() => {});
});

afterEach(() => {
  jest.restoreAllMocks();
});

// ---------------------------------------------------------------------------
// 1. GET /api/annotations — list all annotations
// ---------------------------------------------------------------------------

describe("GET /api/annotations — list all", () => {
  it("returns 200 with { annotations } array", async () => {
    mockAll.mockReturnValue([makeDbRow()]);

    const response = await GET(makeGetRequest());
    const body = await response.json();

    expect(response.status).toBe(200);
    expect(body).toHaveProperty("annotations");
    expect(Array.isArray(body.annotations)).toBe(true);
  });

  it("returns all annotations when no section filter is provided", async () => {
    mockAll.mockReturnValue([
      makeDbRow({ id: "ann-1", sectionId: "section-1" }),
      makeDbRow({ id: "ann-2", sectionId: "section-2" }),
    ]);

    const response = await GET(makeGetRequest());
    const body = await response.json();

    expect(body.annotations).toHaveLength(2);
    expect(body.annotations[0].id).toBe("ann-1");
    expect(body.annotations[1].id).toBe("ann-2");
  });

  it("returns empty array when no annotations exist", async () => {
    mockAll.mockReturnValue([]);

    const response = await GET(makeGetRequest());
    const body = await response.json();

    expect(response.status).toBe(200);
    expect(body.annotations).toEqual([]);
  });

  it("queries without WHERE clause when no section param", async () => {
    mockAll.mockReturnValue([]);

    await GET(makeGetRequest());

    const sql = mockPrepare.mock.calls[0][0] as string;
    expect(sql).toContain("ORDER BY timestamp ASC");
    expect(sql).not.toContain("WHERE");
  });

  it("calls getDb() to obtain the database", async () => {
    mockAll.mockReturnValue([]);

    await GET(makeGetRequest());

    expect(mockGetDb).toHaveBeenCalledTimes(1);
  });
});

// ---------------------------------------------------------------------------
// 2. GET /api/annotations?section=X — filter by section
// ---------------------------------------------------------------------------

describe("GET /api/annotations?section=X — filter by section", () => {
  it("filters annotations by sectionId when section param is provided", async () => {
    mockAll.mockReturnValue([
      makeDbRow({ id: "ann-1", sectionId: "section-1" }),
    ]);

    const response = await GET(makeGetRequest("section-1"));
    const body = await response.json();

    expect(response.status).toBe(200);
    expect(body.annotations).toHaveLength(1);
  });

  it("uses WHERE sectionId = ? when section param is provided", async () => {
    mockAll.mockReturnValue([]);

    await GET(makeGetRequest("section-1"));

    const sql = mockPrepare.mock.calls[0][0] as string;
    expect(sql).toContain("WHERE sectionId = ?");
    expect(mockAll).toHaveBeenCalledWith("section-1");
  });

  it("orders results by timestamp ascending", async () => {
    mockAll.mockReturnValue([]);

    await GET(makeGetRequest("section-1"));

    const sql = mockPrepare.mock.calls[0][0] as string;
    expect(sql).toContain("ORDER BY timestamp ASC");
  });
});

// ---------------------------------------------------------------------------
// 3. GET — response Annotation shape mapping
// ---------------------------------------------------------------------------

describe("GET — Annotation shape mapping", () => {
  it("maps all DB row fields to Annotation properties", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        id: "ann-abc",
        sectionId: "section-2",
        timestamp: 7.5,
        text: "Fix this",
        videoFile: "video.mp4",
        drawingDataUrl: "data:image/png;base64,draw",
        compositeDataUrl: "data:image/png;base64,comp",
        analysis: null,
        resolved: 0,
        resolveJobId: null,
        createdAt: "2025-06-01T12:00:00Z",
      }),
    ]);

    const response = await GET(makeGetRequest());
    const body = await response.json();
    const annotation = body.annotations[0];

    expect(annotation.id).toBe("ann-abc");
    expect(annotation.sectionId).toBe("section-2");
    expect(annotation.timestamp).toBe(7.5);
    expect(annotation.text).toBe("Fix this");
    expect(annotation.videoFile).toBe("video.mp4");
    expect(annotation.drawingDataUrl).toBe("data:image/png;base64,draw");
    expect(annotation.compositeDataUrl).toBe("data:image/png;base64,comp");
    expect(annotation.analysis).toBeNull();
    expect(annotation.resolved).toBe(false);
    expect(annotation.resolveJobId).toBeNull();
    expect(annotation.fixCommitSha).toBeNull();
    expect(annotation.createdAt).toBe("2025-06-01T12:00:00Z");
  });

  it("includes fixCommitSha when present in the DB row", async () => {
    mockAll.mockReturnValue([
      makeDbRow({ fixCommitSha: "abc123def456" }),
    ]);

    const response = await GET(makeGetRequest());
    const body = await response.json();

    expect(body.annotations[0].fixCommitSha).toBe("abc123def456");
  });

  it("converts resolved integer (0) to boolean false", async () => {
    mockAll.mockReturnValue([makeDbRow({ resolved: 0 })]);

    const response = await GET(makeGetRequest());
    const body = await response.json();

    expect(body.annotations[0].resolved).toBe(false);
  });

  it("converts resolved integer (1) to boolean true", async () => {
    mockAll.mockReturnValue([makeDbRow({ resolved: 1 })]);

    const response = await GET(makeGetRequest());
    const body = await response.json();

    expect(body.annotations[0].resolved).toBe(true);
  });

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

    const response = await GET(makeGetRequest());
    const body = await response.json();

    expect(body.annotations[0].analysis).toEqual(analysisData);
  });

  it("returns null for analysis when DB value is a non-AnnotationAnalysis JSON envelope", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        analysis: JSON.stringify({
          type: "result",
          result: "free-form prose",
        }),
      }),
    ]);

    const response = await GET(makeGetRequest());
    const body = await response.json();

    expect(body.annotations[0].analysis).toBeNull();
  });

  it("returns null for analysis when DB value is null", async () => {
    mockAll.mockReturnValue([makeDbRow({ analysis: null })]);

    const response = await GET(makeGetRequest());
    const body = await response.json();

    expect(body.annotations[0].analysis).toBeNull();
  });

  it("returns null for optional fields when DB values are undefined", async () => {
    mockAll.mockReturnValue([
      makeDbRow({
        videoFile: undefined,
        drawingDataUrl: undefined,
        compositeDataUrl: undefined,
        resolveJobId: undefined,
      }),
    ]);

    const response = await GET(makeGetRequest());
    const body = await response.json();
    const annotation = body.annotations[0];

    expect(annotation.videoFile).toBeNull();
    expect(annotation.drawingDataUrl).toBeNull();
    expect(annotation.compositeDataUrl).toBeNull();
    expect(annotation.resolveJobId).toBeNull();
  });
});

// ---------------------------------------------------------------------------
// 4. GET — error handling (500)
// ---------------------------------------------------------------------------

describe("GET — internal server error", () => {
  it("returns 500 when getDb throws", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("DB connection failed");
    });

    const response = await GET(makeGetRequest());

    expect(response.status).toBe(500);
  });

  it("returns { error: 'Internal Server Error' } body on failure", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("DB connection failed");
    });

    const response = await GET(makeGetRequest());
    const body = await response.json();

    expect(body).toEqual({ error: "Internal Server Error" });
  });

  it("logs error to console.error on failure", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("Unexpected error");
    });

    await GET(makeGetRequest());

    expect(console.error).toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 5. POST /api/annotations — create annotation with all fields
// ---------------------------------------------------------------------------

describe("POST /api/annotations — create annotation", () => {
  it("returns 201 status on successful creation", async () => {
    const response = await POST(makePostRequest(validPostBody()));

    expect(response.status).toBe(201);
  });

  it("returns the created Annotation object with all fields", async () => {
    const body = validPostBody();
    const response = await POST(makePostRequest(body));
    const result = await response.json();

    expect(result.id).toBe(MOCK_UUID);
    expect(result.sectionId).toBe(body.sectionId);
    expect(result.timestamp).toBe(body.timestamp);
    expect(result.text).toBe(body.text);
    expect(result.videoFile).toBe(body.videoFile);
    expect(result.drawingDataUrl).toBe(body.drawingDataUrl);
    expect(result.compositeDataUrl).toBe(body.compositeDataUrl);
    expect(result.analysis).toBeNull();
    expect(result.resolved).toBe(false);
    expect(result.resolveJobId).toBeNull();
    expect(result.createdAt).toBeDefined();
  });

  it("generates a UUID for the annotation ID", async () => {
    const response = await POST(makePostRequest(validPostBody()));
    const result = await response.json();

    expect(result.id).toBe(MOCK_UUID);
  });

  it("sets analysis to null for new annotations", async () => {
    const response = await POST(makePostRequest(validPostBody()));
    const result = await response.json();

    expect(result.analysis).toBeNull();
  });

  it("sets resolved to false for new annotations", async () => {
    const response = await POST(makePostRequest(validPostBody()));
    const result = await response.json();

    expect(result.resolved).toBe(false);
  });

  it("sets resolveJobId to null for new annotations", async () => {
    const response = await POST(makePostRequest(validPostBody()));
    const result = await response.json();

    expect(result.resolveJobId).toBeNull();
  });

  it("includes a createdAt ISO timestamp", async () => {
    const response = await POST(makePostRequest(validPostBody()));
    const result = await response.json();

    // createdAt should be a valid ISO string
    expect(new Date(result.createdAt).toISOString()).toBe(result.createdAt);
  });

  it("inserts the annotation into the database", async () => {
    const body = validPostBody();

    await POST(makePostRequest(body));

    expect(mockPrepare).toHaveBeenCalled();
    const sql = mockPrepare.mock.calls[0][0] as string;
    expect(sql).toContain("INSERT INTO annotations");
    expect(mockRun).toHaveBeenCalledTimes(1);
  });

  it("passes correct values to the INSERT statement", async () => {
    const body = validPostBody();

    await POST(makePostRequest(body));

    const runArgs = mockRun.mock.calls[0];
    expect(runArgs[0]).toBe(MOCK_UUID); // id
    expect(runArgs[1]).toBe(body.sectionId);
    expect(runArgs[2]).toBe(body.timestamp);
    expect(runArgs[3]).toBe(body.text);
    expect(runArgs[4]).toBe(body.videoFile);
    expect(runArgs[5]).toBe(body.drawingDataUrl);
    expect(runArgs[6]).toBe(body.compositeDataUrl);
    // runArgs[7] is createdAt
    expect(typeof runArgs[7]).toBe("string");
  });

  it("normalizes stitched full-video timestamps into the correct later section before insert", async () => {
    const body = {
      ...validPostBody(),
      sectionId: "section-1",
      timestamp: 16.8,
      videoFile: "/api/video/outputs/full_video.mp4?v=123",
    };

    const response = await POST(makePostRequest(body));
    const result = await response.json();

    expect(result.sectionId).toBe("section-2");
    expect(result.timestamp).toBeCloseTo(5.8, 5);

    const runArgs = mockRun.mock.calls[0];
    expect(runArgs[1]).toBe("section-2");
    expect(runArgs[2]).toBeCloseTo(5.8, 5);
  });

  it("uses explicit globalTimestamp and sectionTimestamp when provided", async () => {
    const body = {
      ...validPostBody(),
      sectionId: "section-1",
      timestamp: 5.5,
      globalTimestamp: 16.5,
      sectionTimestamp: 5.5,
      videoFile: "/api/video/outputs/full_video.mp4?v=999",
    };

    const response = await POST(makePostRequest(body));
    const result = await response.json();

    expect(result.sectionId).toBe("section-2");
    expect(result.timestamp).toBeCloseTo(5.5, 5);

    const runArgs = mockRun.mock.calls[0];
    expect(runArgs[1]).toBe("section-2");
    expect(runArgs[2]).toBeCloseTo(5.5, 5);
  });

  it("stores NULL for analysis in the INSERT", async () => {
    await POST(makePostRequest(validPostBody()));

    const sql = mockPrepare.mock.calls[0][0] as string;
    expect(sql).toContain("NULL");
  });

  it("stores 0 for resolved in the INSERT", async () => {
    await POST(makePostRequest(validPostBody()));

    const sql = mockPrepare.mock.calls[0][0] as string;
    // The SQL should have a literal 0 for the resolved column
    expect(sql).toMatch(/0/);
  });

  it("calls getDb() to obtain the database", async () => {
    await POST(makePostRequest(validPostBody()));

    expect(mockGetDb).toHaveBeenCalledTimes(1);
  });
});

// ---------------------------------------------------------------------------
// 6. POST — minimal body (only required fields)
// ---------------------------------------------------------------------------

describe("POST — minimal body (only required fields)", () => {
  it("returns 201 with only sectionId and text", async () => {
    const response = await POST(makePostRequest(minimalPostBody()));

    expect(response.status).toBe(201);
  });

  it("sets optional fields to null when not provided", async () => {
    const response = await POST(makePostRequest(minimalPostBody()));
    const result = await response.json();

    expect(result.timestamp).toBeNull();
    expect(result.videoFile).toBeNull();
    expect(result.drawingDataUrl).toBeNull();
    expect(result.compositeDataUrl).toBeNull();
  });

  it("passes null for optional fields in INSERT", async () => {
    await POST(makePostRequest(minimalPostBody()));

    const runArgs = mockRun.mock.calls[0];
    expect(runArgs[2]).toBeNull(); // timestamp
    expect(runArgs[4]).toBeNull(); // videoFile
    expect(runArgs[5]).toBeNull(); // drawingDataUrl
    expect(runArgs[6]).toBeNull(); // compositeDataUrl
  });
});

// ---------------------------------------------------------------------------
// 7. POST — validation (400)
// ---------------------------------------------------------------------------

describe("POST — validation errors (400)", () => {
  it("returns 400 when sectionId is missing", async () => {
    const response = await POST(
      makePostRequest({ text: "Some text" })
    );

    expect(response.status).toBe(400);
  });

  it("returns 400 when text is missing", async () => {
    const response = await POST(
      makePostRequest({ sectionId: "section-1" })
    );

    expect(response.status).toBe(400);
  });

  it("returns 400 when both sectionId and text are missing", async () => {
    const response = await POST(makePostRequest({}));

    expect(response.status).toBe(400);
  });

  it("returns error message about required fields", async () => {
    const response = await POST(makePostRequest({}));
    const body = await response.json();

    expect(body.error).toBeDefined();
    expect(body.error).toContain("sectionId");
    expect(body.error).toContain("text");
  });

  it("returns 400 when sectionId is empty string", async () => {
    const response = await POST(
      makePostRequest({ sectionId: "", text: "Some text" })
    );

    expect(response.status).toBe(400);
  });

  it("returns 400 when text is empty string", async () => {
    const response = await POST(
      makePostRequest({ sectionId: "section-1", text: "" })
    );

    expect(response.status).toBe(400);
  });

  it("does not insert into DB when validation fails", async () => {
    await POST(makePostRequest({}));

    expect(mockRun).not.toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 8. POST — error handling (500)
// ---------------------------------------------------------------------------

describe("POST — internal server error", () => {
  it("returns 500 when getDb throws", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("DB connection failed");
    });

    const response = await POST(makePostRequest(validPostBody()));

    expect(response.status).toBe(500);
  });

  it("returns { error: 'Internal Server Error' } body on failure", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("DB connection failed");
    });

    const response = await POST(makePostRequest(validPostBody()));
    const body = await response.json();

    expect(body).toEqual({ error: "Internal Server Error" });
  });

  it("returns 500 when db.prepare().run() throws", async () => {
    mockRun.mockImplementation(() => {
      throw new Error("SQLITE_CONSTRAINT: NOT NULL");
    });

    const response = await POST(makePostRequest(validPostBody()));

    expect(response.status).toBe(500);
  });

  it("logs error to console.error on failure", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("Unexpected error");
    });

    await POST(makePostRequest(validPostBody()));

    expect(console.error).toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 9. No authentication required
// ---------------------------------------------------------------------------

describe("no authentication required", () => {
  it("GET succeeds without any authorization header", async () => {
    mockAll.mockReturnValue([]);

    const response = await GET(makeGetRequest());

    expect(response.status).toBe(200);
  });

  it("POST succeeds without any authorization header", async () => {
    const response = await POST(makePostRequest(validPostBody()));

    expect(response.status).toBe(201);
  });

  it("GET succeeds with an authorization header present", async () => {
    mockAll.mockReturnValue([]);

    const request = new NextRequest("http://localhost/api/annotations", {
      method: "GET",
      headers: { Authorization: "Bearer fake-token" },
    });

    const response = await GET(request);

    expect(response.status).toBe(200);
  });

  it("POST succeeds with an authorization header present", async () => {
    const request = new NextRequest("http://localhost/api/annotations", {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        Authorization: "Bearer fake-token",
      },
      body: JSON.stringify(validPostBody()),
    });

    const response = await POST(request);

    expect(response.status).toBe(201);
  });
});

// ---------------------------------------------------------------------------
// 10. Data URL storage
// ---------------------------------------------------------------------------

describe("data URL storage", () => {
  it("stores drawingDataUrl as-is (base64 data URL string)", async () => {
    const body = {
      ...validPostBody(),
      drawingDataUrl: "data:image/png;base64,iVBORw0KGgo=",
    };

    const response = await POST(makePostRequest(body));
    const result = await response.json();

    expect(result.drawingDataUrl).toBe("data:image/png;base64,iVBORw0KGgo=");
  });

  it("stores compositeDataUrl as-is (base64 data URL string)", async () => {
    const body = {
      ...validPostBody(),
      compositeDataUrl: "data:image/png;base64,AAABBB=",
    };

    const response = await POST(makePostRequest(body));
    const result = await response.json();

    expect(result.compositeDataUrl).toBe("data:image/png;base64,AAABBB=");
  });
});

// ---------------------------------------------------------------------------
// 11. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/annotations/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    sourceCode = fs.readFileSync(
      path.join(__dirname, "..", "app", "api", "annotations", "route.ts"),
      "utf-8"
    );
  });

  it("exports async GET function", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+GET/);
  });

  it("exports async POST function", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+POST/);
  });

  it("imports getDb from @/lib/db", () => {
    expect(sourceCode).toMatch(/@\/lib\/db/);
    expect(sourceCode).toMatch(/getDb/);
  });

  it("imports Annotation and CreateAnnotationInput from @/lib/types", () => {
    expect(sourceCode).toMatch(/@\/lib\/types/);
    expect(sourceCode).toMatch(/Annotation/);
    expect(sourceCode).toMatch(/CreateAnnotationInput/);
  });

  it("imports randomUUID from crypto", () => {
    expect(sourceCode).toMatch(/randomUUID/);
    expect(sourceCode).toMatch(/crypto/);
  });

  it("imports NextRequest and NextResponse from next/server", () => {
    expect(sourceCode).toMatch(/NextRequest/);
    expect(sourceCode).toMatch(/NextResponse/);
    expect(sourceCode).toMatch(/next\/server/);
  });

  it("uses NextResponse.json() for responses", () => {
    expect(sourceCode).toMatch(/NextResponse\.json\(/);
  });

  it("validates sectionId and text as required", () => {
    expect(sourceCode).toMatch(/sectionId/);
    expect(sourceCode).toMatch(/text/);
    expect(sourceCode).toMatch(/400/);
  });

  it("reads section query parameter from URL", () => {
    expect(sourceCode).toMatch(/searchParams/);
    expect(sourceCode).toMatch(/section/);
  });

  it("queries annotations table", () => {
    expect(sourceCode).toMatch(/annotations/);
    expect(sourceCode).toMatch(/SELECT/);
    expect(sourceCode).toMatch(/INSERT/);
  });

  it("orders by timestamp ascending", () => {
    expect(sourceCode).toMatch(/ORDER BY timestamp ASC/);
  });
});

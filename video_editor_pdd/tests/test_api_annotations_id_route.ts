/**
 * Tests for app/api/annotations/[id]/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_annotations_id_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. GET /api/annotations/[id] — returns a single Annotation by ID
 *      - Returns the full Annotation shape including analysis (parsed from JSON text column)
 *      - Returns 404 with { error: 'Annotation not found' } if the ID does not exist
 *   2. No authentication required
 *   3. Export dynamic = 'force-dynamic'
 *   4. Uses getDb() from @/lib/db
 *   5. Deserializes analysis JSON text column into object
 *   6. Returns 500 with { error: 'Internal Server Error' } on unexpected errors
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

// Import after mock setup
import { GET, PUT, DELETE, dynamic } from "../app/api/annotations/[id]/route";
import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Creates a mock Request object. */
function makeRequest(id: string): Request {
  return new Request(`http://localhost/api/annotations/${id}`, {
    method: "GET",
  });
}

/** Creates the params object matching Next.js App Router dynamic route. */
function makeParams(id: string): { params: { id: string } } {
  return { params: { id } };
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
  mockPrepare.mockReturnValue({ get: mockGet, run: mockRun });
  mockGet.mockReset();
  mockRun.mockReset();
  jest.spyOn(console, "error").mockImplementation(() => {});
});

afterEach(() => {
  jest.restoreAllMocks();
});

// ---------------------------------------------------------------------------
// 1. GET /api/annotations/[id] — successful lookup
// ---------------------------------------------------------------------------

describe("GET /api/annotations/[id] — successful lookup", () => {
  it("returns 200 when annotation exists", async () => {
    mockGet.mockReturnValue(makeDbRow());

    const response = await GET(makeRequest("ann-123"), makeParams("ann-123"));

    expect(response.status).toBe(200);
  });

  it("returns the annotation object directly (not wrapped)", async () => {
    mockGet.mockReturnValue(makeDbRow({ id: "ann-456" }));

    const response = await GET(makeRequest("ann-456"), makeParams("ann-456"));
    const body = await response.json();

    expect(body.id).toBe("ann-456");
    expect(body).not.toHaveProperty("annotations");
  });

  it("queries the database with the ID from params", async () => {
    mockGet.mockReturnValue(makeDbRow());

    await GET(makeRequest("ann-789"), makeParams("ann-789"));

    const sql = mockPrepare.mock.calls[0][0] as string;
    expect(sql).toContain("SELECT * FROM annotations WHERE id = ?");
    expect(mockGet).toHaveBeenCalledWith("ann-789");
  });

  it("calls getDb() to obtain the database", async () => {
    mockGet.mockReturnValue(makeDbRow());

    await GET(makeRequest("ann-123"), makeParams("ann-123"));

    expect(mockGetDb).toHaveBeenCalledTimes(1);
  });
});

// ---------------------------------------------------------------------------
// 2. GET /api/annotations/[id] — 404 not found
// ---------------------------------------------------------------------------

describe("GET /api/annotations/[id] — not found", () => {
  it("returns 404 when annotation does not exist", async () => {
    mockGet.mockReturnValue(undefined);

    const response = await GET(
      makeRequest("nonexistent"),
      makeParams("nonexistent")
    );

    expect(response.status).toBe(404);
  });

  it("returns { error: 'Annotation not found' } body on miss", async () => {
    mockGet.mockReturnValue(undefined);

    const response = await GET(
      makeRequest("nonexistent"),
      makeParams("nonexistent")
    );
    const body = await response.json();

    expect(body).toEqual({ error: "Annotation not found" });
  });

  it("returns 404 when db.prepare().get() returns null", async () => {
    mockGet.mockReturnValue(null);

    const response = await GET(makeRequest("null-id"), makeParams("null-id"));

    expect(response.status).toBe(404);
  });
});

// ---------------------------------------------------------------------------
// 3. Annotation shape mapping
// ---------------------------------------------------------------------------

describe("GET — Annotation shape mapping", () => {
  it("maps all DB row fields to Annotation properties", async () => {
    mockGet.mockReturnValue(
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
      })
    );

    const response = await GET(makeRequest("ann-abc"), makeParams("ann-abc"));
    const annotation = await response.json();

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
    expect(annotation.createdAt).toBe("2025-06-01T12:00:00Z");
  });

  it("converts resolved integer (0) to boolean false", async () => {
    mockGet.mockReturnValue(makeDbRow({ resolved: 0 }));

    const response = await GET(makeRequest("ann-123"), makeParams("ann-123"));
    const body = await response.json();

    expect(body.resolved).toBe(false);
  });

  it("converts resolved integer (1) to boolean true", async () => {
    mockGet.mockReturnValue(makeDbRow({ resolved: 1 }));

    const response = await GET(makeRequest("ann-123"), makeParams("ann-123"));
    const body = await response.json();

    expect(body.resolved).toBe(true);
  });

  it("deserializes analysis JSON string into object", async () => {
    const analysisData = {
      severity: "major",
      fixType: "remotion",
      technicalAssessment: "Color issue",
      suggestedFixes: ["Adjust contrast"],
      confidence: 0.85,
    };
    mockGet.mockReturnValue(
      makeDbRow({ analysis: JSON.stringify(analysisData) })
    );

    const response = await GET(makeRequest("ann-123"), makeParams("ann-123"));
    const body = await response.json();

    expect(body.analysis).toEqual(analysisData);
  });

  it("returns null for analysis when DB value is null", async () => {
    mockGet.mockReturnValue(makeDbRow({ analysis: null }));

    const response = await GET(makeRequest("ann-123"), makeParams("ann-123"));
    const body = await response.json();

    expect(body.analysis).toBeNull();
  });

  it("returns null for analysis when DB value is empty string", async () => {
    mockGet.mockReturnValue(makeDbRow({ analysis: "" }));

    const response = await GET(makeRequest("ann-123"), makeParams("ann-123"));
    const body = await response.json();

    expect(body.analysis).toBeNull();
  });

  it("returns null for optional fields when DB values are undefined", async () => {
    mockGet.mockReturnValue(
      makeDbRow({
        videoFile: undefined,
        drawingDataUrl: undefined,
        compositeDataUrl: undefined,
        resolveJobId: undefined,
      })
    );

    const response = await GET(makeRequest("ann-123"), makeParams("ann-123"));
    const body = await response.json();

    expect(body.videoFile).toBeNull();
    expect(body.drawingDataUrl).toBeNull();
    expect(body.compositeDataUrl).toBeNull();
    expect(body.resolveJobId).toBeNull();
  });
});

// ---------------------------------------------------------------------------
// 4. Error handling (500)
// ---------------------------------------------------------------------------

describe("GET — internal server error", () => {
  it("returns 500 when getDb throws", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("DB connection failed");
    });

    const response = await GET(makeRequest("ann-123"), makeParams("ann-123"));

    expect(response.status).toBe(500);
  });

  it("returns { error: 'Internal Server Error' } body on failure", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("DB connection failed");
    });

    const response = await GET(makeRequest("ann-123"), makeParams("ann-123"));
    const body = await response.json();

    expect(body).toEqual({ error: "Internal Server Error" });
  });

  it("returns 500 when db.prepare().get() throws", async () => {
    mockGet.mockImplementation(() => {
      throw new Error("SQLITE_ERROR");
    });

    const response = await GET(makeRequest("ann-123"), makeParams("ann-123"));

    expect(response.status).toBe(500);
  });

  it("returns 500 when analysis JSON is malformed", async () => {
    mockGet.mockReturnValue(makeDbRow({ analysis: "not-valid-json{{{" }));

    const response = await GET(makeRequest("ann-123"), makeParams("ann-123"));

    expect(response.status).toBe(500);
  });

  it("logs error to console.error on failure", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("Unexpected error");
    });

    await GET(makeRequest("ann-123"), makeParams("ann-123"));

    expect(console.error).toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 5. No authentication required
// ---------------------------------------------------------------------------

describe("no authentication required", () => {
  it("GET succeeds without any authorization header", async () => {
    mockGet.mockReturnValue(makeDbRow());

    const response = await GET(makeRequest("ann-123"), makeParams("ann-123"));

    expect(response.status).toBe(200);
  });

  it("GET succeeds with an authorization header present", async () => {
    mockGet.mockReturnValue(makeDbRow());

    const request = new Request("http://localhost/api/annotations/ann-123", {
      method: "GET",
      headers: { Authorization: "Bearer fake-token" },
    });

    const response = await GET(request, makeParams("ann-123"));

    expect(response.status).toBe(200);
  });
});

// ---------------------------------------------------------------------------
// 6. Export: dynamic = 'force-dynamic'
// ---------------------------------------------------------------------------

describe("dynamic export", () => {
  it("exports dynamic as 'force-dynamic'", () => {
    expect(dynamic).toBe("force-dynamic");
  });
});

// ---------------------------------------------------------------------------
// 7. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/annotations/[id]/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    sourceCode = fs.readFileSync(
      path.join(
        __dirname,
        "..",
        "app",
        "api",
        "annotations",
        "[id]",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async GET function", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+GET/);
  });

  it("imports getDb from @/lib/db", () => {
    expect(sourceCode).toMatch(/@\/lib\/db/);
    expect(sourceCode).toMatch(/getDb/);
  });

  it("imports NextResponse from next/server", () => {
    expect(sourceCode).toMatch(/NextResponse/);
    expect(sourceCode).toMatch(/next\/server/);
  });

  it("uses NextResponse.json() for responses", () => {
    expect(sourceCode).toMatch(/NextResponse\.json\(/);
  });

  it("queries annotations table with parameterized ID", () => {
    expect(sourceCode).toMatch(/SELECT \* FROM annotations WHERE id = \?/);
  });

  it("exports dynamic = 'force-dynamic'", () => {
    expect(sourceCode).toMatch(/export\s+const\s+dynamic\s*=\s*["']force-dynamic["']/);
  });

  it("parses analysis JSON from the database row", () => {
    expect(sourceCode).toMatch(/JSON\.parse/);
    expect(sourceCode).toMatch(/analysis/);
  });

  it("converts resolved to boolean", () => {
    expect(sourceCode).toMatch(/Boolean\(row\.resolved\)/);
  });

  it("handles 404 not found case", () => {
    expect(sourceCode).toMatch(/404/);
    expect(sourceCode).toMatch(/Annotation not found/);
  });

  it("handles 500 internal server error case", () => {
    expect(sourceCode).toMatch(/500/);
    expect(sourceCode).toMatch(/Internal Server Error/);
  });

  it("exports async PUT function", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+PUT/);
  });

  it("exports async DELETE function", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+DELETE/);
  });
});

// ---------------------------------------------------------------------------
// 8. PUT /api/annotations/[id] — update annotation
// ---------------------------------------------------------------------------

describe("PUT /api/annotations/[id] — successful update", () => {
  it("returns 200 when annotation exists and fields are updated", async () => {
    // First call: SELECT id for existence check
    // Second call: UPDATE
    // Third call: SELECT * for re-fetch
    let callCount = 0;
    mockPrepare.mockImplementation(() => {
      callCount++;
      if (callCount === 1) return { get: () => ({ id: "ann-123" }) };
      if (callCount === 2) return { run: mockRun };
      return { get: () => makeDbRow({ text: "Updated text" }) };
    });

    const request = new Request("http://localhost/api/annotations/ann-123", {
      method: "PUT",
      body: JSON.stringify({ text: "Updated text" }),
      headers: { "Content-Type": "application/json" },
    });

    const response = await PUT(request, makeParams("ann-123"));
    expect(response.status).toBe(200);
  });

  it("returns updated annotation object", async () => {
    let callCount = 0;
    mockPrepare.mockImplementation(() => {
      callCount++;
      if (callCount === 1) return { get: () => ({ id: "ann-123" }) };
      if (callCount === 2) return { run: mockRun };
      return {
        get: () =>
          makeDbRow({
            id: "ann-123",
            text: "New text",
            sectionId: "section-1",
            timestamp: 5.0,
          }),
      };
    });

    const request = new Request("http://localhost/api/annotations/ann-123", {
      method: "PUT",
      body: JSON.stringify({ text: "New text" }),
      headers: { "Content-Type": "application/json" },
    });

    const response = await PUT(request, makeParams("ann-123"));
    const body = await response.json();
    expect(body.id).toBe("ann-123");
    expect(body.text).toBe("New text");
  });
});

describe("PUT /api/annotations/[id] — not found", () => {
  it("returns 404 when annotation does not exist", async () => {
    mockPrepare.mockReturnValue({ get: () => undefined });

    const request = new Request("http://localhost/api/annotations/missing", {
      method: "PUT",
      body: JSON.stringify({ text: "Updated" }),
      headers: { "Content-Type": "application/json" },
    });

    const response = await PUT(request, makeParams("missing"));
    expect(response.status).toBe(404);
  });

  it("returns { error: 'Annotation not found' } body", async () => {
    mockPrepare.mockReturnValue({ get: () => undefined });

    const request = new Request("http://localhost/api/annotations/missing", {
      method: "PUT",
      body: JSON.stringify({ text: "Updated" }),
      headers: { "Content-Type": "application/json" },
    });

    const response = await PUT(request, makeParams("missing"));
    const body = await response.json();
    expect(body).toEqual({ error: "Annotation not found" });
  });
});

describe("PUT /api/annotations/[id] — no fields to update", () => {
  it("returns 400 when no updatable fields are provided", async () => {
    mockPrepare.mockReturnValue({ get: () => ({ id: "ann-123" }) });

    const request = new Request("http://localhost/api/annotations/ann-123", {
      method: "PUT",
      body: JSON.stringify({}),
      headers: { "Content-Type": "application/json" },
    });

    const response = await PUT(request, makeParams("ann-123"));
    expect(response.status).toBe(400);
  });

  it("returns { error: 'No fields to update' } body", async () => {
    mockPrepare.mockReturnValue({ get: () => ({ id: "ann-123" }) });

    const request = new Request("http://localhost/api/annotations/ann-123", {
      method: "PUT",
      body: JSON.stringify({}),
      headers: { "Content-Type": "application/json" },
    });

    const response = await PUT(request, makeParams("ann-123"));
    const body = await response.json();
    expect(body).toEqual({ error: "No fields to update" });
  });
});

describe("PUT /api/annotations/[id] — error handling", () => {
  it("returns 500 when getDb throws", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("DB connection failed");
    });

    const request = new Request("http://localhost/api/annotations/ann-123", {
      method: "PUT",
      body: JSON.stringify({ text: "Updated" }),
      headers: { "Content-Type": "application/json" },
    });

    const response = await PUT(request, makeParams("ann-123"));
    expect(response.status).toBe(500);
  });
});

// ---------------------------------------------------------------------------
// 9. DELETE /api/annotations/[id] — delete annotation
// ---------------------------------------------------------------------------

describe("DELETE /api/annotations/[id] — successful deletion", () => {
  it("returns 200 with { success: true } when annotation exists", async () => {
    let callCount = 0;
    mockPrepare.mockImplementation(() => {
      callCount++;
      if (callCount === 1) return { get: () => ({ id: "ann-123" }) };
      return { run: mockRun };
    });

    const request = new Request("http://localhost/api/annotations/ann-123", {
      method: "DELETE",
    });

    const response = await DELETE(request, makeParams("ann-123"));
    expect(response.status).toBe(200);

    const body = await response.json();
    expect(body).toEqual({ success: true });
  });

  it("calls DELETE FROM annotations WHERE id = ?", async () => {
    let callCount = 0;
    let deleteSQL = "";
    mockPrepare.mockImplementation((sql: string) => {
      callCount++;
      if (callCount === 1) return { get: () => ({ id: "ann-123" }) };
      deleteSQL = sql;
      return { run: mockRun };
    });

    const request = new Request("http://localhost/api/annotations/ann-123", {
      method: "DELETE",
    });

    await DELETE(request, makeParams("ann-123"));
    expect(deleteSQL).toContain("DELETE FROM annotations WHERE id = ?");
  });
});

describe("DELETE /api/annotations/[id] — not found", () => {
  it("returns 404 when annotation does not exist", async () => {
    mockPrepare.mockReturnValue({ get: () => undefined });

    const request = new Request("http://localhost/api/annotations/missing", {
      method: "DELETE",
    });

    const response = await DELETE(request, makeParams("missing"));
    expect(response.status).toBe(404);
  });

  it("returns { error: 'Annotation not found' } body", async () => {
    mockPrepare.mockReturnValue({ get: () => undefined });

    const request = new Request("http://localhost/api/annotations/missing", {
      method: "DELETE",
    });

    const response = await DELETE(request, makeParams("missing"));
    const body = await response.json();
    expect(body).toEqual({ error: "Annotation not found" });
  });
});

describe("DELETE /api/annotations/[id] — error handling", () => {
  it("returns 500 when getDb throws", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("DB connection failed");
    });

    const request = new Request("http://localhost/api/annotations/ann-123", {
      method: "DELETE",
    });

    const response = await DELETE(request, makeParams("ann-123"));
    expect(response.status).toBe(500);
  });
});

/**
 * Integration tests for Project, Script, and Annotation API routes.
 *
 * Unlike the unit tests in tests/, these tests exercise route handlers with
 * REAL file I/O and a REAL SQLite database.  Only external CLIs and heavy
 * AI/render services are mocked.  A temporary directory is created per suite
 * run to isolate state from the real project.
 *
 * Routes under test:
 *   - GET  /api/project
 *   - PUT  /api/project
 *   - GET  /api/project/script
 *   - PUT  /api/project/script
 *   - GET  /api/annotations
 *   - POST /api/annotations
 *   - GET  /api/annotations/[id]
 *   - PUT  /api/annotations/[id]
 */

// ---------------------------------------------------------------------------
// External-service mocks (declared before any imports)
// ---------------------------------------------------------------------------
jest.mock("@/lib/claude", () => ({ runClaude: jest.fn() }));
jest.mock("@/lib/veo", () => ({ generateVeoClip: jest.fn() }));
jest.mock("@/lib/render", () => ({
  renderSection: jest.fn(),
  getSectionDuration: jest.fn(),
  stitchFullVideo: jest.fn(),
}));

// ---------------------------------------------------------------------------
// Imports
// ---------------------------------------------------------------------------
import os from "os";
import path from "path";
import fs from "fs";

// ---------------------------------------------------------------------------
// Temp directory + fixture setup (runs once before the whole file)
// ---------------------------------------------------------------------------
const tmpDir = path.join(os.tmpdir(), `video-editor-integration-${Date.now()}`);

/** Minimal valid project.json fixture matching the Zod schema. */
function makeProjectFixture() {
  return {
    name: "Test Project",
    outputResolution: { width: 1920, height: 1080 },
    tts: {
      engine: "qwen3-tts",
      modelPath: "",
      tokenizerPath: "",
      speaker: "Aiden",
      speakingRate: 0.95,
      sampleRate: 24000,
    },
    sections: [
      {
        id: "intro",
        label: "Introduction",
        videoFile: "",
        specDir: "",
        remotionDir: "",
        compositionId: "",
        durationSeconds: 0,
        offsetSeconds: 0,
      },
    ],
    audioSync: { sectionGroups: {}, silenceGapDefault: 0.3 },
    veo: {
      model: "veo-3.1-generate-preview",
      defaultAspectRatio: "16:9",
      maxConcurrentGenerations: 4,
      references: [],
      frameChains: [],
    },
    render: { maxParallelRenders: 3, useLambda: false, lambdaRegion: "us-east-1" },
  };
}

beforeAll(() => {
  // Build temp project tree
  fs.mkdirSync(tmpDir, { recursive: true });
  fs.writeFileSync(
    path.join(tmpDir, "project.json"),
    JSON.stringify(makeProjectFixture(), null, 2)
  );
  fs.mkdirSync(path.join(tmpDir, "narrative"), { recursive: true });
  fs.writeFileSync(
    path.join(tmpDir, "narrative", "main_script.md"),
    "# Test Script\nNARRATOR: Hello world"
  );

  // Point DB to a file inside the temp dir
  process.env.DB_PATH = path.join(tmpDir, "test-pipeline.db");

  // Override process.cwd() so every route handler resolves paths inside tmpDir
  jest.spyOn(process, "cwd").mockReturnValue(tmpDir);
});

afterAll(() => {
  jest.restoreAllMocks();
  fs.rmSync(tmpDir, { recursive: true, force: true });
  delete process.env.DB_PATH;
});

// Suppress console.error noise from intentional error-path tests
beforeEach(() => {
  jest.spyOn(console, "error").mockImplementation(() => {});
});

afterEach(() => {
  (console.error as jest.Mock).mockRestore?.();
});

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function makeRequest(url: string, options?: RequestInit): Request {
  return new Request(`http://localhost${url}`, options);
}

async function parseResponse(
  response: Response
): Promise<{ status: number; body: any }> {
  const body = await response.json();
  return { status: response.status, body };
}

// ============================================================================
// GET /api/project
// ============================================================================

describe("Integration: GET /api/project", () => {
  let GET: typeof import("@/app/api/project/route").GET;
  let PUT: typeof import("@/app/api/project/route").PUT;

  beforeAll(async () => {
    const mod = await import("@/app/api/project/route");
    GET = mod.GET;
    PUT = mod.PUT;
  });

  it("returns 200 with valid ProjectConfig from project.json", async () => {
    const response = await GET(makeRequest("/api/project"));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body.name).toBe("Test Project");
  });

  it("response includes all required top-level fields", async () => {
    const response = await GET(makeRequest("/api/project"));
    const { body } = await parseResponse(response);

    expect(body).toHaveProperty("name");
    expect(body).toHaveProperty("outputResolution");
    expect(body).toHaveProperty("tts");
    expect(body).toHaveProperty("sections");
    expect(body).toHaveProperty("audioSync");
    expect(body).toHaveProperty("veo");
    expect(body).toHaveProperty("render");
  });

  it("returns sections array with at least the fixture section", async () => {
    const response = await GET(makeRequest("/api/project"));
    const { body } = await parseResponse(response);

    expect(Array.isArray(body.sections)).toBe(true);
    expect(body.sections.length).toBeGreaterThanOrEqual(1);
    expect(body.sections[0].id).toBe("intro");
  });

  it("returns 500 when project.json is missing", async () => {
    const orig = path.join(tmpDir, "project.json");
    const bak = orig + ".bak";
    fs.renameSync(orig, bak);

    try {
      const response = await GET(makeRequest("/api/project"));
      expect(response.status).toBe(500);
    } finally {
      fs.renameSync(bak, orig);
    }
  });

  it("returns 400 when project.json has invalid schema (valid JSON, wrong shape)", async () => {
    const filePath = path.join(tmpDir, "project.json");
    const original = fs.readFileSync(filePath, "utf-8");
    fs.writeFileSync(filePath, JSON.stringify({ bad: "data" }));

    try {
      const response = await GET(makeRequest("/api/project"));
      expect(response.status).toBe(400);
    } finally {
      fs.writeFileSync(filePath, original);
    }
  });

  it("returns 500 when project.json contains invalid JSON (not parseable)", async () => {
    const filePath = path.join(tmpDir, "project.json");
    const original = fs.readFileSync(filePath, "utf-8");
    fs.writeFileSync(filePath, "NOT VALID JSON {{{");

    try {
      const response = await GET(makeRequest("/api/project"));
      // JSON.parse throws SyntaxError (not ZodError), so the route
      // falls through to the generic error handler → 500
      expect(response.status).toBe(500);
    } finally {
      fs.writeFileSync(filePath, original);
    }
  });

  it("response has JSON content type", async () => {
    const response = await GET(makeRequest("/api/project"));
    expect(response.headers.get("content-type")).toMatch(/application\/json/);
  });
});

// ============================================================================
// PUT /api/project
// ============================================================================

describe("Integration: PUT /api/project", () => {
  let GET: typeof import("@/app/api/project/route").GET;
  let PUT: typeof import("@/app/api/project/route").PUT;

  beforeAll(async () => {
    const mod = await import("@/app/api/project/route");
    GET = mod.GET;
    PUT = mod.PUT;
  });

  // Reset project.json to fixture between tests to avoid cross-contamination
  afterEach(() => {
    fs.writeFileSync(
      path.join(tmpDir, "project.json"),
      JSON.stringify(makeProjectFixture(), null, 2)
    );
  });

  it("returns 200 and updates project.json when given valid partial config", async () => {
    const response = await PUT(
      makeRequest("/api/project", {
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ name: "Updated Project" }),
      })
    );
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body.name).toBe("Updated Project");
  });

  it("merged config preserves existing fields not in the partial update", async () => {
    const response = await PUT(
      makeRequest("/api/project", {
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ name: "Partial Update" }),
      })
    );
    const { body } = await parseResponse(response);

    // tts, sections, render, veo, audioSync should be preserved
    expect(body.tts.engine).toBe("qwen3-tts");
    expect(body.sections).toHaveLength(1);
    expect(body.render.maxParallelRenders).toBe(3);
  });

  it("returns 400 when body has invalid field types (name: 123)", async () => {
    const response = await PUT(
      makeRequest("/api/project", {
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ name: 123 }),
      })
    );
    expect(response.status).toBe(400);
  });

  it("returns 400 when body is not valid JSON", async () => {
    const response = await PUT(
      makeRequest("/api/project", {
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: "not valid json {{{",
      })
    );
    expect(response.status).toBe(400);
  });

  it("returns 200 and actually writes to disk", async () => {
    await PUT(
      makeRequest("/api/project", {
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ name: "Disk Check" }),
      })
    );

    const onDisk = JSON.parse(
      fs.readFileSync(path.join(tmpDir, "project.json"), "utf-8")
    );
    expect(onDisk.name).toBe("Disk Check");
  });

  it("handles empty body {} without crashing (merges nothing)", async () => {
    const response = await PUT(
      makeRequest("/api/project", {
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({}),
      })
    );
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body.name).toBe("Test Project");
  });

  it("returns 400 with ZodError issues array for invalid outputResolution", async () => {
    const response = await PUT(
      makeRequest("/api/project", {
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ outputResolution: "not-an-object" }),
      })
    );
    const { status, body } = await parseResponse(response);

    expect(status).toBe(400);
    expect(body.error).toBe("Validation failed");
    expect(Array.isArray(body.issues)).toBe(true);
  });

  it("preserves sections array when updating non-section fields", async () => {
    const response = await PUT(
      makeRequest("/api/project", {
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ name: "Sections Preserved" }),
      })
    );
    const { body } = await parseResponse(response);

    expect(body.sections).toHaveLength(1);
    expect(body.sections[0].id).toBe("intro");
    expect(body.sections[0].label).toBe("Introduction");
  });
});

// ============================================================================
// GET /api/project/script
// ============================================================================

describe("Integration: GET /api/project/script", () => {
  let GET_script: typeof import("@/app/api/project/script/route").GET;
  let PUT_script: typeof import("@/app/api/project/script/route").PUT;

  beforeAll(async () => {
    const mod = await import("@/app/api/project/script/route");
    GET_script = mod.GET;
    PUT_script = mod.PUT;
  });

  it("returns 200 with script content from narrative/main_script.md", async () => {
    const response = await GET_script(
      makeRequest("/api/project/script")
    );
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body.content).toContain("# Test Script");
    expect(body.content).toContain("NARRATOR: Hello world");
  });

  it("returns the file content as { content: string } response shape", async () => {
    const response = await GET_script(
      makeRequest("/api/project/script")
    );
    const { body } = await parseResponse(response);

    expect(typeof body.content).toBe("string");
    expect(Object.keys(body)).toEqual(["content"]);
  });

  it("returns 404 when narrative/main_script.md is missing", async () => {
    const scriptPath = path.join(tmpDir, "narrative", "main_script.md");
    const bak = scriptPath + ".bak";
    fs.renameSync(scriptPath, bak);

    try {
      const response = await GET_script(
        makeRequest("/api/project/script")
      );
      expect(response.status).toBe(404);
    } finally {
      fs.renameSync(bak, scriptPath);
    }
  });

  it("returns 200 with empty content when file is empty", async () => {
    const scriptPath = path.join(tmpDir, "narrative", "main_script.md");
    const original = fs.readFileSync(scriptPath, "utf-8");
    fs.writeFileSync(scriptPath, "");

    try {
      const response = await GET_script(
        makeRequest("/api/project/script")
      );
      const { status, body } = await parseResponse(response);

      expect(status).toBe(200);
      expect(body.content).toBe("");
    } finally {
      fs.writeFileSync(scriptPath, original);
    }
  });
});

// ============================================================================
// PUT /api/project/script
// ============================================================================

describe("Integration: PUT /api/project/script", () => {
  let PUT_script: typeof import("@/app/api/project/script/route").PUT;

  beforeAll(async () => {
    const mod = await import("@/app/api/project/script/route");
    PUT_script = mod.PUT;
  });

  // Restore script after each test
  afterEach(() => {
    fs.writeFileSync(
      path.join(tmpDir, "narrative", "main_script.md"),
      "# Test Script\nNARRATOR: Hello world"
    );
  });

  it("returns 200 and writes new content to narrative/main_script.md", async () => {
    const response = await PUT_script(
      makeRequest("/api/project/script", {
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ content: "# Updated Script\nNew narrator line" }),
      })
    );
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body.ok).toBe(true);
  });

  it("verify file on disk has the new content after PUT", async () => {
    const newContent = "# Disk Verification\nLine two";
    await PUT_script(
      makeRequest("/api/project/script", {
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ content: newContent }),
      })
    );

    const onDisk = fs.readFileSync(
      path.join(tmpDir, "narrative", "main_script.md"),
      "utf-8"
    );
    expect(onDisk).toBe(newContent);
  });

  it("returns 400 when body is missing content field", async () => {
    const response = await PUT_script(
      makeRequest("/api/project/script", {
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({}),
      })
    );
    expect(response.status).toBe(400);
  });

  it("handles unicode content correctly", async () => {
    const unicodeContent = "# Unicode Test\nNARRATOR: \u3053\u3093\u306b\u3061\u306f\u4e16\u754c \u{1F30D} \u00e9\u00e0\u00fc\u00f1";
    await PUT_script(
      makeRequest("/api/project/script", {
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ content: unicodeContent }),
      })
    );

    const onDisk = fs.readFileSync(
      path.join(tmpDir, "narrative", "main_script.md"),
      "utf-8"
    );
    expect(onDisk).toBe(unicodeContent);
  });
});

// ============================================================================
// POST /api/annotations  +  GET /api/annotations
// ============================================================================

describe("Integration: POST & GET /api/annotations", () => {
  let GET_annotations: typeof import("@/app/api/annotations/route").GET;
  let POST_annotations: typeof import("@/app/api/annotations/route").POST;

  beforeAll(async () => {
    const mod = await import("@/app/api/annotations/route");
    GET_annotations = mod.GET;
    POST_annotations = mod.POST;
  });

  it("POST creates annotation and returns 201 with id", async () => {
    const { NextRequest } = await import("next/server");
    const response = await POST_annotations(
      new NextRequest("http://localhost/api/annotations", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          sectionId: "intro",
          text: "Integration test annotation",
          timestamp: 1.5,
        }),
      })
    );
    const { status, body } = await parseResponse(response);

    expect(status).toBe(201);
    expect(body.id).toBeDefined();
    expect(typeof body.id).toBe("string");
    expect(body.id.length).toBeGreaterThan(0);
  });

  it("GET returns array of annotations including the one just created", async () => {
    const { NextRequest } = await import("next/server");

    // Create one
    await POST_annotations(
      new NextRequest("http://localhost/api/annotations", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          sectionId: "intro",
          text: "Second annotation for GET test",
        }),
      })
    );

    // Fetch all
    const response = await GET_annotations(
      new NextRequest("http://localhost/api/annotations")
    );
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(Array.isArray(body.annotations)).toBe(true);
    expect(body.annotations.length).toBeGreaterThanOrEqual(1);

    const texts = body.annotations.map((a: any) => a.text);
    expect(texts).toContain("Second annotation for GET test");
  });

  it("POST with missing required fields returns 400", async () => {
    const { NextRequest } = await import("next/server");
    const response = await POST_annotations(
      new NextRequest("http://localhost/api/annotations", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ timestamp: 5.0 }),
      })
    );
    expect(response.status).toBe(400);
  });

  it("POST with empty text but drawingDataUrl creates annotation (drawing-only)", async () => {
    const { NextRequest } = await import("next/server");
    const response = await POST_annotations(
      new NextRequest("http://localhost/api/annotations", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          sectionId: "intro",
          timestamp: 71.0,
          text: "",
          drawingDataUrl: "data:image/png;base64,iVBORw0KGgoAAAANSUhEUg==",
          compositeDataUrl: null,
        }),
      })
    );
    expect(response.status).toBe(201);
    const { body } = await parseResponse(response);
    expect(body.sectionId).toBe("intro");
    expect(body.text).toBe("");
    expect(body.drawingDataUrl).toBe("data:image/png;base64,iVBORw0KGgoAAAANSUhEUg==");
  });

  it("POST with valid sectionId, timestamp, text creates and returns annotation", async () => {
    const { NextRequest } = await import("next/server");
    const response = await POST_annotations(
      new NextRequest("http://localhost/api/annotations", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          sectionId: "intro",
          timestamp: 42.0,
          text: "Annotation with all three fields",
        }),
      })
    );
    const { status, body } = await parseResponse(response);

    expect(status).toBe(201);
    expect(body.sectionId).toBe("intro");
    expect(body.timestamp).toBe(42.0);
    expect(body.text).toBe("Annotation with all three fields");
    expect(body.analysis).toBeNull();
    expect(body.resolved).toBe(false);
    expect(body.createdAt).toBeDefined();
  });
});

// ============================================================================
// GET /api/annotations/[id]  +  PUT /api/annotations/[id]
// ============================================================================

describe("Integration: GET & PUT /api/annotations/[id]", () => {
  let GET_annotation: typeof import("@/app/api/annotations/[id]/route").GET;
  let PUT_annotation: typeof import("@/app/api/annotations/[id]/route").PUT;
  let POST_annotations: typeof import("@/app/api/annotations/route").POST;

  /** ID of an annotation created during beforeAll. */
  let createdId: string;

  beforeAll(async () => {
    const idMod = await import("@/app/api/annotations/[id]/route");
    GET_annotation = idMod.GET;
    PUT_annotation = idMod.PUT;

    const listMod = await import("@/app/api/annotations/route");
    POST_annotations = listMod.POST;

    // Seed an annotation for the [id] tests
    const { NextRequest } = await import("next/server");
    const response = await POST_annotations(
      new NextRequest("http://localhost/api/annotations", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          sectionId: "intro",
          text: "Seed annotation for [id] tests",
          timestamp: 10.0,
        }),
      })
    );
    const data = await response.json();
    createdId = data.id;
  });

  it("GET returns 200 with annotation details for valid id", async () => {
    const response = await GET_annotation(
      makeRequest(`/api/annotations/${createdId}`),
      { params: { id: createdId } }
    );
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body.id).toBe(createdId);
    expect(body.sectionId).toBe("intro");
    expect(body.text).toBe("Seed annotation for [id] tests");
    expect(body.timestamp).toBe(10.0);
  });

  it("GET returns 404 for non-existent annotation id", async () => {
    const response = await GET_annotation(
      makeRequest("/api/annotations/does-not-exist-00000"),
      { params: { id: "does-not-exist-00000" } }
    );
    expect(response.status).toBe(404);
  });

  it("PUT updates annotation fields and returns updated annotation", async () => {
    const response = await PUT_annotation(
      makeRequest(`/api/annotations/${createdId}`, {
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ text: "Updated via integration test" }),
      }),
      { params: { id: createdId } }
    );
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body.id).toBe(createdId);
    expect(body.text).toBe("Updated via integration test");
    // Other fields should remain unchanged
    expect(body.sectionId).toBe("intro");
  });

  it("PUT returns 404 for non-existent id", async () => {
    const response = await PUT_annotation(
      makeRequest("/api/annotations/nope-not-here", {
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ text: "Should not update" }),
      }),
      { params: { id: "nope-not-here" } }
    );
    expect(response.status).toBe(404);
  });
});

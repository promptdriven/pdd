/**
 * Tests for app/api/project/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_project_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. GET /api/project — returns full ProjectConfig as JSON with status 200
 *   2. PUT /api/project — merges Partial<ProjectConfig>, validates, saves, returns 200
 *   3. HTTP 400 with { error, issues } on Zod validation failure
 *   4. HTTP 500 with { error } on file system errors
 *   5. HTTP 405 with { error: 'Method not allowed' } for unsupported methods
 *   6. No authentication required
 *   7. Uses NextResponse.json() for all responses
 *   8. export const dynamic = 'force-dynamic'
 */

import { ZodError, ZodIssue } from "zod";

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockLoadProject = jest.fn();
const mockSaveProject = jest.fn();
const mockValidateProjectConfig = jest.fn();

jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
  saveProject: (...args: unknown[]) => mockSaveProject(...args),
  validateProjectConfig: (...args: unknown[]) =>
    mockValidateProjectConfig(...args),
}));

// Import after mocking
import {
  GET,
  PUT,
  POST,
  PATCH,
  DELETE,
  OPTIONS,
  HEAD,
  dynamic,
} from "../app/api/project/route";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Returns a valid ProjectConfig fixture for testing. */
function validConfig() {
  return {
    name: "Test Project",
    outputResolution: "1920x1080",
    tts: {
      voice: "en-US-Neural2-F",
      rate: 1.0,
      model: "google-tts-v2",
    },
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
    ],
    audioSync: {
      sectionGroups: { narration: ["intro"] },
    },
    veo: {
      model: "veo-2.0-generate-001",
      aspectRatio: "16:9",
      referenceImages: { logo: "assets/logo.png" },
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

/** Creates a minimal Request object for GET. */
function makeGetRequest(): Request {
  return new Request("http://localhost/api/project", { method: "GET" });
}

/** Creates a Request object for PUT with a JSON body. */
function makePutRequest(body: unknown): Request {
  return new Request("http://localhost/api/project", {
    method: "PUT",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(body),
  });
}

/** Creates a Request with invalid (non-JSON) body. */
function makePutRequestWithBadBody(): Request {
  return new Request("http://localhost/api/project", {
    method: "PUT",
    headers: { "Content-Type": "application/json" },
    body: "not valid json {{{",
  });
}

/** Extracts JSON body and status from a NextResponse. */
async function parseResponse(
  response: Response
): Promise<{ status: number; body: any }> {
  const body = await response.json();
  return { status: response.status, body };
}

/** Creates a ZodError with the given issues. */
function makeZodError(issues: Partial<ZodIssue>[]): ZodError {
  return new ZodError(
    issues.map((i) => ({
      code: "invalid_type" as const,
      expected: "string",
      received: "number",
      path: i.path ?? ["name"],
      message: i.message ?? "Expected string, received number",
      ...i,
    }))
  );
}

// ---------------------------------------------------------------------------
// Setup
// ---------------------------------------------------------------------------

beforeEach(() => {
  jest.resetAllMocks();
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
// 2. GET /api/project
// ---------------------------------------------------------------------------

describe("GET /api/project", () => {
  it("returns the full ProjectConfig as JSON with status 200", async () => {
    const config = validConfig();
    mockLoadProject.mockReturnValue(config);

    const response = await GET(makeGetRequest());
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body).toEqual(config);
  });

  it("calls loadProject() to read project.json", async () => {
    mockLoadProject.mockReturnValue(validConfig());

    await GET(makeGetRequest());

    expect(mockLoadProject).toHaveBeenCalledTimes(1);
  });

  it("returns 400 with validation error details when loadProject throws ZodError", async () => {
    const zodError = makeZodError([
      { path: ["name"], message: "Expected string, received number" },
    ]);
    mockLoadProject.mockImplementation(() => {
      throw zodError;
    });

    const response = await GET(makeGetRequest());
    const { status, body } = await parseResponse(response);

    expect(status).toBe(400);
    expect(body.error).toBe("Validation failed");
    expect(body.issues).toBeDefined();
    expect(Array.isArray(body.issues)).toBe(true);
    expect(body.issues.length).toBeGreaterThan(0);
  });

  it("includes ZodIssue[] in the 400 response", async () => {
    const zodError = makeZodError([
      { path: ["tts", "rate"], message: "Expected number" },
      { path: ["name"], message: "Required" },
    ]);
    mockLoadProject.mockImplementation(() => {
      throw zodError;
    });

    const response = await GET(makeGetRequest());
    const { body } = await parseResponse(response);

    expect(body.issues).toHaveLength(2);
    expect(body.issues[0].path).toEqual(["tts", "rate"]);
    expect(body.issues[1].path).toEqual(["name"]);
  });

  it("returns 500 with error message on file system errors", async () => {
    mockLoadProject.mockImplementation(() => {
      throw new Error("ENOENT: no such file or directory");
    });

    const response = await GET(makeGetRequest());
    const { status, body } = await parseResponse(response);

    expect(status).toBe(500);
    expect(body.error).toBeDefined();
    expect(typeof body.error).toBe("string");
  });

  it("returns JSON content type via NextResponse.json()", async () => {
    mockLoadProject.mockReturnValue(validConfig());

    const response = await GET(makeGetRequest());

    expect(response.headers.get("content-type")).toMatch(/application\/json/);
  });
});

// ---------------------------------------------------------------------------
// 3. PUT /api/project
// ---------------------------------------------------------------------------

describe("PUT /api/project", () => {
  it("merges partial body with existing config, validates, saves, and returns 200", async () => {
    const existing = validConfig();
    const updated = { ...existing, name: "Updated Project" };

    mockLoadProject.mockReturnValue(existing);
    mockValidateProjectConfig.mockReturnValue(updated);

    const response = await PUT(makePutRequest({ name: "Updated Project" }));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body.name).toBe("Updated Project");
  });

  it("calls loadProject to get existing config", async () => {
    const existing = validConfig();
    mockLoadProject.mockReturnValue(existing);
    mockValidateProjectConfig.mockReturnValue(existing);

    await PUT(makePutRequest({}));

    expect(mockLoadProject).toHaveBeenCalledTimes(1);
  });

  it("calls validateProjectConfig with merged config", async () => {
    const existing = validConfig();
    mockLoadProject.mockReturnValue(existing);
    mockValidateProjectConfig.mockReturnValue({
      ...existing,
      name: "New Name",
    });

    await PUT(makePutRequest({ name: "New Name" }));

    expect(mockValidateProjectConfig).toHaveBeenCalledTimes(1);
    const mergedArg = mockValidateProjectConfig.mock.calls[0][0];
    expect(mergedArg.name).toBe("New Name");
    // Other fields should come from existing config
    expect(mergedArg.outputResolution).toBe("1920x1080");
  });

  it("calls saveProject with the validated config", async () => {
    const existing = validConfig();
    const validated = { ...existing, name: "Validated" };
    mockLoadProject.mockReturnValue(existing);
    mockValidateProjectConfig.mockReturnValue(validated);

    await PUT(makePutRequest({ name: "Validated" }));

    expect(mockSaveProject).toHaveBeenCalledTimes(1);
    expect(mockSaveProject).toHaveBeenCalledWith(validated);
  });

  it("returns the validated config in the response body", async () => {
    const existing = validConfig();
    const validated = { ...existing, name: "Final" };
    mockLoadProject.mockReturnValue(existing);
    mockValidateProjectConfig.mockReturnValue(validated);

    const response = await PUT(makePutRequest({ name: "Final" }));
    const { body } = await parseResponse(response);

    expect(body).toEqual(validated);
  });

  it("returns 400 for malformed JSON body", async () => {
    const response = await PUT(makePutRequestWithBadBody());
    const { status, body } = await parseResponse(response);

    expect(status).toBe(400);
    expect(body.error).toBeDefined();
  });

  it("returns 400 with validation error when validateProjectConfig throws ZodError", async () => {
    const existing = validConfig();
    mockLoadProject.mockReturnValue(existing);

    const zodError = makeZodError([
      { path: ["outputResolution"], message: "Invalid enum value" },
    ]);
    mockValidateProjectConfig.mockImplementation(() => {
      throw zodError;
    });

    const response = await PUT(
      makePutRequest({ outputResolution: "invalid" })
    );
    const { status, body } = await parseResponse(response);

    expect(status).toBe(400);
    expect(body.error).toBe("Validation failed");
    expect(body.issues).toBeDefined();
    expect(Array.isArray(body.issues)).toBe(true);
  });

  it("returns 500 when loadProject throws a generic error", async () => {
    mockLoadProject.mockImplementation(() => {
      throw new Error("Disk read failure");
    });

    const response = await PUT(makePutRequest({ name: "Test" }));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(500);
    expect(body.error).toBeDefined();
    expect(typeof body.error).toBe("string");
  });

  it("returns 500 when saveProject throws a generic error", async () => {
    const existing = validConfig();
    mockLoadProject.mockReturnValue(existing);
    mockValidateProjectConfig.mockReturnValue(existing);
    mockSaveProject.mockImplementation(() => {
      throw new Error("Disk write failure");
    });

    const response = await PUT(makePutRequest({ name: "Test" }));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(500);
    expect(body.error).toBeDefined();
  });

  it("does not call saveProject when validation fails", async () => {
    const existing = validConfig();
    mockLoadProject.mockReturnValue(existing);
    mockValidateProjectConfig.mockImplementation(() => {
      throw makeZodError([{ path: ["name"] }]);
    });

    await PUT(makePutRequest({ name: 123 }));

    expect(mockSaveProject).not.toHaveBeenCalled();
  });

  it("shallow-merges body over existing config (body fields override)", async () => {
    const existing = validConfig();
    const newTts = { voice: "en-US-Neural2-D", rate: 1.5, model: "v3" };
    mockLoadProject.mockReturnValue(existing);
    mockValidateProjectConfig.mockImplementation((data: any) => data);

    await PUT(makePutRequest({ tts: newTts }));

    const mergedArg = mockValidateProjectConfig.mock.calls[0][0];
    // Shallow merge: tts entirely replaced
    expect(mergedArg.tts).toEqual(newTts);
    // Other fields preserved from existing
    expect(mergedArg.name).toBe("Test Project");
  });

  it("handles empty body (no changes)", async () => {
    const existing = validConfig();
    mockLoadProject.mockReturnValue(existing);
    mockValidateProjectConfig.mockReturnValue(existing);

    const response = await PUT(makePutRequest({}));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body).toEqual(existing);
  });
});

// ---------------------------------------------------------------------------
// 4. Unsupported HTTP methods — 405
// ---------------------------------------------------------------------------

describe("unsupported HTTP methods return 405", () => {
  const methods = [
    { name: "POST", handler: POST },
    { name: "PATCH", handler: PATCH },
    { name: "DELETE", handler: DELETE },
    { name: "OPTIONS", handler: OPTIONS },
    { name: "HEAD", handler: HEAD },
  ];

  for (const { name, handler } of methods) {
    it(`${name} returns 405 with { error: 'Method not allowed' }`, async () => {
      const response = await handler();
      const { status, body } = await parseResponse(response);

      expect(status).toBe(405);
      expect(body.error).toBe("Method not allowed");
    });
  }
});

// ---------------------------------------------------------------------------
// 5. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/project/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    const fs = require("fs");
    const path = require("path");
    sourceCode = fs.readFileSync(
      path.join(__dirname, "..", "app", "api", "project", "route.ts"),
      "utf-8"
    );
  });

  it("exports named GET function", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+GET/);
  });

  it("exports named PUT function", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+PUT/);
  });

  it("exports dynamic = 'force-dynamic'", () => {
    expect(sourceCode).toMatch(
      /export\s+const\s+dynamic\s*=\s*["']force-dynamic["']/
    );
  });

  it("imports from @/lib/project", () => {
    expect(sourceCode).toMatch(/@\/lib\/project/);
  });

  it("imports loadProject, saveProject, validateProjectConfig", () => {
    expect(sourceCode).toMatch(/loadProject/);
    expect(sourceCode).toMatch(/saveProject/);
    expect(sourceCode).toMatch(/validateProjectConfig/);
  });

  it("imports ZodError from zod", () => {
    expect(sourceCode).toMatch(
      /import\s+\{.*ZodError.*\}\s+from\s+["']zod["']/
    );
  });

  it("uses NextResponse.json() for responses", () => {
    expect(sourceCode).toMatch(/NextResponse\.json\(/);
  });

  it("uses instanceof ZodError for error differentiation", () => {
    expect(sourceCode).toMatch(/instanceof\s+ZodError/);
  });

  it("uses request.json() to parse PUT body", () => {
    expect(sourceCode).toMatch(/request\.json\(\)/);
  });
});

/**
 * Tests for app/api/project/script/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_project_script_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. GET /api/project/script — reads narrative/main_script.md, returns { content } with 200
 *   2. GET returns 404 with { error: 'Script file not found' } if file does not exist
 *   3. PUT /api/project/script — accepts { content: string }, writes atomically, returns { ok: true } with 200
 *   4. PUT returns 400 if content is missing or not a string
 *   5. No authentication required
 *   6. Ensures narrative/ directory is created if it does not exist before writing
 *   7. Atomic write: write to .tmp then rename
 *   8. export const dynamic = 'force-dynamic'
 *   9. Uses path.join(process.cwd(), 'narrative', 'main_script.md') for file path
 */

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockExistsSync = jest.fn();
const mockReadFileSync = jest.fn();
const mockWriteFileSync = jest.fn();
const mockMkdirSync = jest.fn();
const mockRenameSync = jest.fn();

jest.mock("fs", () => ({
  __esModule: true,
  default: {
    existsSync: (...args: unknown[]) => mockExistsSync(...args),
    readFileSync: (...args: unknown[]) => mockReadFileSync(...args),
    writeFileSync: (...args: unknown[]) => mockWriteFileSync(...args),
    mkdirSync: (...args: unknown[]) => mockMkdirSync(...args),
    renameSync: (...args: unknown[]) => mockRenameSync(...args),
  },
}));

// Import after mocking
import { GET, PUT, dynamic } from "../app/api/project/script/route";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Creates a minimal Request object for GET. */
function makeGetRequest(): Request {
  return new Request("http://localhost/api/project/script", { method: "GET" });
}

function makeGetSectionRequest(section: string): Request {
  return new Request(
    `http://localhost/api/project/script?section=${encodeURIComponent(section)}`,
    { method: "GET" }
  );
}

/** Creates a Request object for PUT with a JSON body. */
function makePutRequest(body: unknown): Request {
  return new Request("http://localhost/api/project/script", {
    method: "PUT",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(body),
  });
}

/** Creates a Request with invalid (non-JSON) body. */
function makePutRequestWithBadBody(): Request {
  return new Request("http://localhost/api/project/script", {
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

// ---------------------------------------------------------------------------
// Setup
// ---------------------------------------------------------------------------

beforeEach(() => {
  jest.resetAllMocks();
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
// 2. GET /api/project/script
// ---------------------------------------------------------------------------

describe("GET /api/project/script", () => {
  it("returns { content } with status 200 when file exists", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue("# My Script\n\nHello world");

    const response = await GET(makeGetRequest());
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body).toEqual({
      content: "# My Script\n\nHello world",
      sectionContent: null,
      sectionHeading: null,
    });
  });

  it("returns 404 with { error: 'Script file not found' } when file does not exist", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await GET(makeGetRequest());
    const { status, body } = await parseResponse(response);

    expect(status).toBe(404);
    expect(body).toEqual({ error: "Script file not found" });
  });

  it("uses correct file path: process.cwd() + narrative/main_script.md", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue("content");

    await GET(makeGetRequest());

    const path = require("path");
    const expectedPath = path.join(
      process.cwd(),
      "narrative",
      "main_script.md"
    );
    expect(mockExistsSync).toHaveBeenCalledWith(expectedPath);
    expect(mockReadFileSync).toHaveBeenCalledWith(expectedPath, "utf-8");
  });

  it("does not call readFileSync when file does not exist", async () => {
    mockExistsSync.mockReturnValue(false);

    await GET(makeGetRequest());

    expect(mockReadFileSync).not.toHaveBeenCalled();
  });

  it("returns 500 with error on internal file system error", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockImplementation(() => {
      throw new Error("EACCES: permission denied");
    });

    const response = await GET(makeGetRequest());
    const { status, body } = await parseResponse(response);

    expect(status).toBe(500);
    expect(body.error).toBeDefined();
    expect(typeof body.error).toBe("string");
  });

  it("returns empty string content when file exists but is empty", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue("");

    const response = await GET(makeGetRequest());
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body).toEqual({
      content: "",
      sectionContent: null,
      sectionHeading: null,
    });
  });

  it("returns JSON content type via NextResponse.json()", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue("test");

    const response = await GET(makeGetRequest());

    expect(response.headers.get("content-type")).toMatch(/application\/json/);
  });

  it("returns sectionContent for a matching section request", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue(
      [
        "# Main Script",
        "",
        "## Cold Open (00:00 - 00:17)",
        "",
        "**NARRATOR:**",
        "Open beat.",
        "",
        "## Part 1: The Economics of Darning (00:17 - 07:58)",
        "",
        "**NARRATOR:**",
        "Watch my grandmother darn this sock.",
      ].join("\n")
    );

    const response = await GET(makeGetSectionRequest("cold_open"));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body.sectionHeading).toBe("Cold Open (00:00 - 00:17)");
    expect(body.sectionContent).toContain("## Cold Open (00:00 - 00:17)");
    expect(body.sectionContent).toContain("Open beat.");
    expect(body.sectionContent).not.toContain("The Economics of Darning");
  });

  it("matches section IDs that are compact abbreviations of verbose headings", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue(
      [
        "# Main Script",
        "",
        "## COLD OPEN: THE SOCK HOOK (0:00 - 2:00)",
        "",
        "**NARRATOR:**",
        "Hook the audience.",
        "",
        "## PART 1: THE ECONOMICS OF DARNING (2:30 - 8:30)",
        "",
        "**NARRATOR:**",
        "Watch my grandmother darn this sock.",
        "",
        "## PART 2: THE PARADIGM SHIFT (8:30 - 13:00)",
        "",
        "**NARRATOR:**",
        "Everything changed.",
      ].join("\n")
    );

    const response = await GET(makeGetSectionRequest("part1_economics"));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body.sectionHeading).toBe("PART 1: THE ECONOMICS OF DARNING (2:30 - 8:30)");
    expect(body.sectionContent).toContain("Watch my grandmother darn this sock.");
    expect(body.sectionContent).not.toContain("Hook the audience.");
    expect(body.sectionContent).not.toContain("Everything changed.");
  });

  it("returns folded timed demo headings with the owning section instead of the next top-level section", async () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockImplementation((filePath: string) => {
      if (String(filePath).endsWith("project.json")) {
        return JSON.stringify({
          name: "demo",
          outputResolution: { width: 1920, height: 1080 },
          tts: {
            engine: "qwen3-tts",
            modelPath: "models/Qwen3-TTS",
            tokenizerPath: "models/Qwen3-TTS",
            speaker: "Aiden",
            speakingRate: 1,
            sampleRate: 24000,
          },
          sections: [
            {
              id: "cold_open",
              label: "Cold Open",
              videoFile: "cold_open.mp4",
              specDir: "cold_open",
              remotionDir: "S00-ColdOpen",
              compositionId: "ColdOpenSection",
              durationSeconds: 0,
              offsetSeconds: 0,
            },
            {
              id: "part1_economics",
              label: "Part 1: Economics of Darning",
              videoFile: "part1_economics.mp4",
              specDir: "part1_economics",
              remotionDir: "S01-Part1Economics",
              compositionId: "Part1EconomicsSection",
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
          render: {
            maxParallelRenders: 3,
            useLambda: false,
            lambdaRegion: "us-east-1",
          },
        });
      }

      return [
        "# Main Script",
        "",
        "## COLD OPEN: THE SOCK HOOK (0:00 - 2:00)",
        "",
        "**NARRATOR:**",
        "If you use Cursor...",
        "",
        "## THE THIRTY-SECOND DEMO (2:00 - 2:30)",
        "",
        "**NARRATOR:**",
        "Watch this.",
        "",
        "## PART 1: THE ECONOMICS OF DARNING (2:30 - 8:30)",
        "",
        "**NARRATOR:**",
        "This isn't nostalgia.",
      ].join("\n");
    });

    const response = await GET(makeGetSectionRequest("cold_open"));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body.sectionHeading).toBe("COLD OPEN: THE SOCK HOOK (0:00 - 2:00)");
    expect(body.sectionContent).toContain("## COLD OPEN: THE SOCK HOOK (0:00 - 2:00)");
    expect(body.sectionContent).toContain("## THE THIRTY-SECOND DEMO (2:00 - 2:30)");
    expect(body.sectionContent).toContain("Watch this.");
    expect(body.sectionContent).not.toContain("This isn't nostalgia.");
  });

  it("falls back to full content when section match is not found", async () => {
    const content = [
      "# Main Script",
      "",
      "## Cold Open (00:00 - 00:17)",
      "",
      "**NARRATOR:**",
      "Open beat.",
    ].join("\n");
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue(content);

    const response = await GET(makeGetSectionRequest("unknown_section"));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body.content).toBe(content);
    expect(body.sectionContent).toBeNull();
    expect(body.sectionHeading).toBeNull();
  });
});

// ---------------------------------------------------------------------------
// 3. PUT /api/project/script
// ---------------------------------------------------------------------------

describe("PUT /api/project/script", () => {
  it("writes content and returns { ok: true } with status 200", async () => {
    const response = await PUT(
      makePutRequest({ content: "# New Script Content" })
    );
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body).toEqual({ ok: true });
  });

  it("creates narrative/ directory before writing", async () => {
    await PUT(makePutRequest({ content: "test" }));

    const path = require("path");
    const expectedDir = path.join(process.cwd(), "narrative");
    expect(mockMkdirSync).toHaveBeenCalledWith(expectedDir, {
      recursive: true,
    });
  });

  it("performs atomic write: writes to .tmp then renames", async () => {
    await PUT(makePutRequest({ content: "atomic content" }));

    const path = require("path");
    const filePath = path.join(process.cwd(), "narrative", "main_script.md");
    const tmpPath = filePath + ".tmp";

    expect(mockWriteFileSync).toHaveBeenCalledWith(
      tmpPath,
      "atomic content",
      "utf-8"
    );
    expect(mockRenameSync).toHaveBeenCalledWith(tmpPath, filePath);
  });

  it("calls mkdirSync before writeFileSync", async () => {
    const callOrder: string[] = [];
    mockMkdirSync.mockImplementation(() => callOrder.push("mkdir"));
    mockWriteFileSync.mockImplementation(() => callOrder.push("write"));
    mockRenameSync.mockImplementation(() => callOrder.push("rename"));

    await PUT(makePutRequest({ content: "order test" }));

    expect(callOrder).toEqual(["mkdir", "write", "rename"]);
  });

  it("returns 400 when content is missing from body", async () => {
    const response = await PUT(makePutRequest({}));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(400);
    expect(body.error).toBeDefined();
  });

  it("returns 400 when content is null", async () => {
    const response = await PUT(makePutRequest({ content: null }));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(400);
    expect(body.error).toBeDefined();
  });

  it("returns 400 when content is a number", async () => {
    const response = await PUT(makePutRequest({ content: 42 }));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(400);
    expect(body.error).toBeDefined();
  });

  it("returns 400 when content is a boolean", async () => {
    const response = await PUT(makePutRequest({ content: true }));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(400);
    expect(body.error).toBeDefined();
  });

  it("returns 400 when content is an object", async () => {
    const response = await PUT(makePutRequest({ content: { text: "hi" } }));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(400);
    expect(body.error).toBeDefined();
  });

  it("returns 400 when content is an array", async () => {
    const response = await PUT(makePutRequest({ content: ["line1"] }));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(400);
    expect(body.error).toBeDefined();
  });

  it("accepts empty string as valid content", async () => {
    const response = await PUT(makePutRequest({ content: "" }));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(200);
    expect(body).toEqual({ ok: true });
  });

  it("returns 500 on malformed JSON body", async () => {
    const response = await PUT(makePutRequestWithBadBody());
    const { status, body } = await parseResponse(response);

    expect(status).toBe(500);
    expect(body.error).toBeDefined();
  });

  it("returns 500 when writeFileSync throws", async () => {
    mockWriteFileSync.mockImplementation(() => {
      throw new Error("ENOSPC: no space left on device");
    });

    const response = await PUT(makePutRequest({ content: "test" }));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(500);
    expect(body.error).toBeDefined();
    expect(typeof body.error).toBe("string");
  });

  it("returns 500 when renameSync throws", async () => {
    mockRenameSync.mockImplementation(() => {
      throw new Error("EPERM: operation not permitted");
    });

    const response = await PUT(makePutRequest({ content: "test" }));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(500);
    expect(body.error).toBeDefined();
  });

  it("returns 500 when mkdirSync throws", async () => {
    mockMkdirSync.mockImplementation(() => {
      throw new Error("EACCES: permission denied");
    });

    const response = await PUT(makePutRequest({ content: "test" }));
    const { status, body } = await parseResponse(response);

    expect(status).toBe(500);
    expect(body.error).toBeDefined();
  });

  it("does not write file when content validation fails", async () => {
    await PUT(makePutRequest({ content: 123 }));

    expect(mockWriteFileSync).not.toHaveBeenCalled();
    expect(mockRenameSync).not.toHaveBeenCalled();
  });

  it("returns JSON content type via NextResponse.json()", async () => {
    const response = await PUT(makePutRequest({ content: "test" }));

    expect(response.headers.get("content-type")).toMatch(/application\/json/);
  });
});

// ---------------------------------------------------------------------------
// 4. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/project/script/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    const realFs = jest.requireActual<typeof import("fs")>("fs");
    const path = require("path");
    sourceCode = realFs.readFileSync(
      path.join(__dirname, "..", "app", "api", "project", "script", "route.ts"),
      "utf-8"
    );
  });

  it("exports named async GET function", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+GET/);
  });

  it("exports named async PUT function", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+PUT/);
  });

  it("exports dynamic = 'force-dynamic'", () => {
    expect(sourceCode).toMatch(
      /export\s+const\s+dynamic\s*=\s*["']force-dynamic["']/
    );
  });

  it("imports fs from Node.js", () => {
    expect(sourceCode).toMatch(/import\s+fs\s+from\s+["']fs["']/);
  });

  it("imports path from Node.js", () => {
    expect(sourceCode).toMatch(/import\s+path\s+from\s+["']path["']/);
  });

  it("imports NextResponse from next/server", () => {
    expect(sourceCode).toMatch(
      /import\s+\{.*NextResponse.*\}\s+from\s+["']next\/server["']/
    );
  });

  it("uses NextResponse.json() for responses", () => {
    expect(sourceCode).toMatch(/NextResponse\.json\(/);
  });

  it("uses fs.existsSync for file existence check", () => {
    expect(sourceCode).toMatch(/fs\.existsSync\(/);
  });

  it("uses fs.readFileSync for reading", () => {
    expect(sourceCode).toMatch(/fs\.readFileSync\(/);
  });

  it("uses fs.writeFileSync for writing", () => {
    expect(sourceCode).toMatch(/fs\.writeFileSync\(/);
  });

  it("uses fs.mkdirSync for directory creation", () => {
    expect(sourceCode).toMatch(/fs\.mkdirSync\(/);
  });

  it("uses fs.renameSync for atomic rename", () => {
    expect(sourceCode).toMatch(/fs\.renameSync\(/);
  });

  it("uses project-aware file path resolution", () => {
    expect(sourceCode).toMatch(/getProjectDir\(\)/);
  });

  it("references narrative/main_script.md path", () => {
    expect(sourceCode).toMatch(/main_script\.md/);
    expect(sourceCode).toMatch(/narrative/);
  });

  it("uses .tmp extension for atomic write", () => {
    expect(sourceCode).toMatch(/\.tmp/);
  });
});

/**
 * Tests for app/api/video/[...path]/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_video_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. GET /api/video/[...path] — serves video files from outputs/sections/ and remotion/public/
 *   2. Reads Range header; returns 206 Partial Content with Content-Range and Accept-Ranges headers
 *   3. Returns 200 for requests without a Range header (full file)
 *   4. Returns 404 if file not found
 *   5. Returns 403 if path traversal detected (path contains ".." or escapes allowed dirs)
 *   6. Sets Content-Type: video/mp4 for all responses
 *   7. Allowed root directories: outputs/ and remotion/public/
 */

import { Readable } from "stream";

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockExistsSync = jest.fn();
const mockStatSync = jest.fn();
const mockCreateReadStream = jest.fn();

jest.mock("fs", () => ({
  existsSync: (...args: unknown[]) => mockExistsSync(...args),
  statSync: (...args: unknown[]) => mockStatSync(...args),
  createReadStream: (...args: unknown[]) => mockCreateReadStream(...args),
}));

// Import after mocking
import { GET } from "../app/api/video/[...path]/route";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Creates a Request for GET /api/video/[...path] with optional Range header. */
function makeRequest(rangeHeader?: string): Request {
  const headers: Record<string, string> = {};
  if (rangeHeader) {
    headers["range"] = rangeHeader;
  }
  return new Request("http://localhost/api/video/outputs/sections/intro.mp4", {
    method: "GET",
    headers,
  });
}

/** Creates params object for the catch-all route. */
function makeParams(segments: string[]): { params: { path: string[] } } {
  return { params: { path: segments } };
}

/** Creates a fake Node.js readable stream that emits the given data. */
function makeFakeNodeStream(data: Buffer): Readable {
  const readable = new Readable({
    read() {
      this.push(data);
      this.push(null);
    },
  });
  return readable;
}

/** Extracts JSON body and status from a Response. */
async function parseJsonResponse(
  response: Response
): Promise<{ status: number; body: any }> {
  const body = await response.json();
  return { status: response.status, body };
}

/** Reads the full body from a streaming Response as a Buffer. */
async function readStreamBody(response: Response): Promise<Buffer> {
  const arrayBuffer = await response.arrayBuffer();
  return Buffer.from(arrayBuffer);
}

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

const FAKE_FILE_SIZE = 10000;
const FAKE_FILE_DATA = Buffer.alloc(FAKE_FILE_SIZE, 0x42); // 10000 bytes of 0x42

// ---------------------------------------------------------------------------
// Setup
// ---------------------------------------------------------------------------

beforeEach(() => {
  jest.resetAllMocks();
  jest.spyOn(console, "error").mockImplementation(() => {});

  // Default: file exists with known size
  mockExistsSync.mockReturnValue(true);
  mockStatSync.mockReturnValue({ size: FAKE_FILE_SIZE });
  mockCreateReadStream.mockImplementation((_path: string, opts?: { start?: number; end?: number }) => {
    if (opts && opts.start !== undefined && opts.end !== undefined) {
      return makeFakeNodeStream(FAKE_FILE_DATA.subarray(opts.start, opts.end + 1));
    }
    return makeFakeNodeStream(FAKE_FILE_DATA);
  });
});

afterEach(() => {
  jest.restoreAllMocks();
});

// ---------------------------------------------------------------------------
// 1. Full file serving (no Range header) — 200
// ---------------------------------------------------------------------------

describe("GET /api/video/[...path] — full file (no Range)", () => {
  it("returns 200 for a valid file without Range header", async () => {
    const response = await GET(
      makeRequest(),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.status).toBe(200);
  });

  it("sets Content-Type: video/mp4", async () => {
    const response = await GET(
      makeRequest(),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.headers.get("content-type")).toBe("video/mp4");
  });

  it("sets Accept-Ranges: bytes", async () => {
    const response = await GET(
      makeRequest(),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.headers.get("accept-ranges")).toBe("bytes");
  });

  it("sets Content-Length to full file size", async () => {
    const response = await GET(
      makeRequest(),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.headers.get("content-length")).toBe(String(FAKE_FILE_SIZE));
  });

  it("streams the full file data in the response body", async () => {
    const response = await GET(
      makeRequest(),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    const body = await readStreamBody(response);
    expect(body.length).toBe(FAKE_FILE_SIZE);
    expect(body[0]).toBe(0x42);
  });

  it("calls fs.createReadStream with the resolved file path", async () => {
    await GET(
      makeRequest(),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(mockCreateReadStream).toHaveBeenCalledTimes(1);
    const callPath = mockCreateReadStream.mock.calls[0][0];
    expect(callPath).toMatch(/outputs[/\\]sections[/\\]intro\.mp4$/);
  });
});

// ---------------------------------------------------------------------------
// 2. Range request — 206 Partial Content
// ---------------------------------------------------------------------------

describe("GET /api/video/[...path] — Range request (206)", () => {
  it("returns 206 for a valid Range header", async () => {
    const response = await GET(
      makeRequest("bytes=0-499"),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.status).toBe(206);
  });

  it("returns Content-Range: bytes start-end/total", async () => {
    const response = await GET(
      makeRequest("bytes=0-499"),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.headers.get("content-range")).toBe(
      `bytes 0-499/${FAKE_FILE_SIZE}`
    );
  });

  it("returns correct Content-Length for the byte range", async () => {
    const response = await GET(
      makeRequest("bytes=0-499"),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.headers.get("content-length")).toBe("500");
  });

  it("sets Content-Type: video/mp4 on 206 responses", async () => {
    const response = await GET(
      makeRequest("bytes=0-499"),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.headers.get("content-type")).toBe("video/mp4");
  });

  it("sets Accept-Ranges: bytes on 206 responses", async () => {
    const response = await GET(
      makeRequest("bytes=0-499"),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.headers.get("accept-ranges")).toBe("bytes");
  });

  it("passes correct start and end to fs.createReadStream", async () => {
    await GET(
      makeRequest("bytes=100-599"),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(mockCreateReadStream).toHaveBeenCalledTimes(1);
    const opts = mockCreateReadStream.mock.calls[0][1];
    expect(opts.start).toBe(100);
    expect(opts.end).toBe(599);
  });

  it("handles open-ended range (bytes=500-)", async () => {
    const response = await GET(
      makeRequest("bytes=500-"),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.status).toBe(206);
    expect(response.headers.get("content-range")).toBe(
      `bytes 500-${FAKE_FILE_SIZE - 1}/${FAKE_FILE_SIZE}`
    );
    expect(response.headers.get("content-length")).toBe(
      String(FAKE_FILE_SIZE - 500)
    );
  });

  it("handles suffix range (bytes=-500)", async () => {
    const response = await GET(
      makeRequest("bytes=-500"),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.status).toBe(206);
    const expectedStart = FAKE_FILE_SIZE - 500;
    expect(response.headers.get("content-range")).toBe(
      `bytes ${expectedStart}-${FAKE_FILE_SIZE - 1}/${FAKE_FILE_SIZE}`
    );
    expect(response.headers.get("content-length")).toBe("500");
  });

  it("clamps end to file size when range exceeds total", async () => {
    const response = await GET(
      makeRequest("bytes=9000-99999"),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.status).toBe(206);
    expect(response.headers.get("content-range")).toBe(
      `bytes 9000-${FAKE_FILE_SIZE - 1}/${FAKE_FILE_SIZE}`
    );
  });

  it("returns 416 for unsatisfiable range (start >= total)", async () => {
    const response = await GET(
      makeRequest("bytes=50000-60000"),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.status).toBe(416);
    expect(response.headers.get("content-range")).toBe(
      `bytes */${FAKE_FILE_SIZE}`
    );
  });

  it("returns 400 for invalid Range header format", async () => {
    const response = await GET(
      makeRequest("invalid-range"),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    const { status, body } = await parseJsonResponse(response);
    expect(status).toBe(400);
    expect(body.error).toBeDefined();
  });
});

// ---------------------------------------------------------------------------
// 3. File not found — 404
// ---------------------------------------------------------------------------

describe("GET /api/video/[...path] — 404 Not Found", () => {
  it("returns 404 when file does not exist", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await GET(
      makeRequest(),
      makeParams(["outputs", "sections", "missing.mp4"])
    );
    const { status, body } = await parseJsonResponse(response);

    expect(status).toBe(404);
    expect(body.error).toBeDefined();
  });
});

// ---------------------------------------------------------------------------
// 4. Path traversal — 403
// ---------------------------------------------------------------------------

describe("GET /api/video/[...path] — 403 path traversal", () => {
  it("returns 403 when path contains '..'", async () => {
    const response = await GET(
      makeRequest(),
      makeParams(["outputs", "..", "etc", "passwd"])
    );
    const { status, body } = await parseJsonResponse(response);

    expect(status).toBe(403);
    expect(body.error).toMatch(/[Ff]orbidden/);
  });

  it("returns 403 when a segment is exactly '..'", async () => {
    const response = await GET(
      makeRequest(),
      makeParams(["..", "outputs", "sections", "intro.mp4"])
    );
    const { status } = await parseJsonResponse(response);

    expect(status).toBe(403);
  });

  it("returns 403 for path outside allowed directories", async () => {
    const response = await GET(
      makeRequest(),
      makeParams(["etc", "passwd"])
    );
    const { status, body } = await parseJsonResponse(response);

    expect(status).toBe(403);
    expect(body.error).toMatch(/[Ff]orbidden/);
  });

  it("returns 403 for path that partially matches allowed dir name", async () => {
    // e.g., "outputs_evil/" should not match "outputs/"
    const response = await GET(
      makeRequest(),
      makeParams(["outputs_evil", "hack.mp4"])
    );
    const { status } = await parseJsonResponse(response);

    expect(status).toBe(403);
  });
});

// ---------------------------------------------------------------------------
// 5. Allowed directories
// ---------------------------------------------------------------------------

describe("GET /api/video/[...path] — allowed directories", () => {
  it("allows files under outputs/", async () => {
    const response = await GET(
      makeRequest(),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.status).toBe(200);
  });

  it("allows files under remotion/public/", async () => {
    const response = await GET(
      makeRequest(),
      makeParams(["remotion", "public", "video.mp4"])
    );

    expect(response.status).toBe(200);
  });

  it("rejects files outside allowed directories", async () => {
    const response = await GET(
      makeRequest(),
      makeParams(["src", "secret.mp4"])
    );
    const { status } = await parseJsonResponse(response);

    expect(status).toBe(403);
  });
});

// ---------------------------------------------------------------------------
// 6. Content-Type always video/mp4
// ---------------------------------------------------------------------------

describe("GET /api/video/[...path] — Content-Type", () => {
  it("always returns Content-Type: video/mp4 for 200", async () => {
    const response = await GET(
      makeRequest(),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.headers.get("content-type")).toBe("video/mp4");
  });

  it("always returns Content-Type: video/mp4 for 206", async () => {
    const response = await GET(
      makeRequest("bytes=0-499"),
      makeParams(["outputs", "sections", "intro.mp4"])
    );

    expect(response.headers.get("content-type")).toBe("video/mp4");
  });
});

// ---------------------------------------------------------------------------
// 7. Internal server error — 500
// ---------------------------------------------------------------------------

describe("GET /api/video/[...path] — 500 Internal Server Error", () => {
  it("returns 500 when fs.statSync throws", async () => {
    mockStatSync.mockImplementation(() => {
      throw new Error("Disk read failure");
    });

    const response = await GET(
      makeRequest(),
      makeParams(["outputs", "sections", "intro.mp4"])
    );
    const { status, body } = await parseJsonResponse(response);

    expect(status).toBe(500);
    expect(body.error).toBe("Internal Server Error");
  });

  it("returns 500 when createReadStream throws", async () => {
    mockCreateReadStream.mockImplementation(() => {
      throw new Error("Stream creation failed");
    });

    const response = await GET(
      makeRequest(),
      makeParams(["outputs", "sections", "intro.mp4"])
    );
    const { status, body } = await parseJsonResponse(response);

    expect(status).toBe(500);
    expect(body.error).toBe("Internal Server Error");
  });
});

// ---------------------------------------------------------------------------
// 8. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/video/[...path]/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    const realFs = jest.requireActual("fs");
    const realPath = jest.requireActual("path");
    sourceCode = realFs.readFileSync(
      realPath.join(
        __dirname,
        "..",
        "app",
        "api",
        "video",
        "[...path]",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports an async GET function", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+GET/);
  });

  it("imports fs module", () => {
    expect(sourceCode).toMatch(/import\s+.*fs.*from\s+["']fs["']/);
  });

  it("imports path module", () => {
    expect(sourceCode).toMatch(/import\s+.*path.*from\s+["']path["']/);
  });

  it("imports Readable from stream", () => {
    expect(sourceCode).toMatch(
      /import\s+\{.*Readable.*\}\s+from\s+["']stream["']/
    );
  });

  it("uses Readable.toWeb() for stream conversion", () => {
    expect(sourceCode).toMatch(/Readable\.toWeb\(/);
  });

  it("uses fs.createReadStream for file reading", () => {
    expect(sourceCode).toMatch(/fs\.createReadStream\(/);
  });

  it("uses fs.statSync for file size", () => {
    expect(sourceCode).toMatch(/fs\.statSync\(/);
  });

  it("checks for path traversal with '..'", () => {
    expect(sourceCode).toMatch(/\.\./);
  });

  it("defines allowed directories including outputs and remotion/public", () => {
    expect(sourceCode).toMatch(/outputs/);
    expect(sourceCode).toMatch(/remotion\/public/);
  });

  it("uses Accept-Ranges: bytes header", () => {
    expect(sourceCode).toMatch(/Accept-Ranges/);
    expect(sourceCode).toMatch(/bytes/);
  });

  it("uses Content-Range header for range responses", () => {
    expect(sourceCode).toMatch(/Content-Range/);
  });

  it("sets Content-Type to video/mp4", () => {
    expect(sourceCode).toMatch(/video\/mp4/);
  });
});

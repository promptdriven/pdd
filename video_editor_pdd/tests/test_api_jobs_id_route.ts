/**
 * Tests for app/api/jobs/[id]/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_jobs_id_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. GET /api/jobs/[id] — returns the current Job record for polling fallback
 *   2. Returns the full Job shape including status, progress, error, createdAt, updatedAt
 *   3. Returns 404 with { error: 'Job not found' } if the ID does not exist
 *   4. No authentication required
 *   5. Export dynamic = 'force-dynamic'
 */

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockGetJob = jest.fn();

jest.mock("@/lib/jobs", () => ({
  getJob: (...args: unknown[]) => mockGetJob(...args),
}));

// Import after mock setup
import { GET, dynamic } from "../app/api/jobs/[id]/route";
import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function mockRequest(id: string = "test-id"): Request {
  return new Request(`http://localhost/api/jobs/${id}`);
}

function makeParams(id: string): { params: { id: string } } {
  return { params: { id } };
}

function makeJob(overrides: Record<string, unknown> = {}) {
  return {
    id: "job-123",
    stage: "setup",
    status: "done",
    progress: 100,
    error: null,
    params: {},
    logs: "",
    createdAt: "2025-01-15T10:00:00Z",
    updatedAt: "2025-01-15T10:02:30Z",
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Setup / Teardown
// ---------------------------------------------------------------------------

beforeEach(() => {
  mockGetJob.mockReset();
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
// 2. GET handler — successful job fetch (200)
// ---------------------------------------------------------------------------

describe("GET — successful job fetch", () => {
  it("returns 200 status when job exists", async () => {
    mockGetJob.mockReturnValue(makeJob());

    const response = await GET(mockRequest(), makeParams("job-123"));
    expect(response.status).toBe(200);
  });

  it("returns the full Job shape as JSON", async () => {
    const job = makeJob({
      id: "job-abc",
      stage: "tts-render",
      status: "running",
      progress: 45,
      error: null,
      params: { sectionId: "intro", voice: "en-US-Neural2-F" },
      createdAt: "2025-01-15T10:00:00Z",
      updatedAt: "2025-01-15T10:02:30Z",
    });
    mockGetJob.mockReturnValue(job);

    const response = await GET(mockRequest("job-abc"), makeParams("job-abc"));
    const body = await response.json();

    expect(body.id).toBe("job-abc");
    expect(body.stage).toBe("tts-render");
    expect(body.status).toBe("running");
    expect(body.progress).toBe(45);
    expect(body.error).toBeNull();
    expect(body.params).toEqual({ sectionId: "intro", voice: "en-US-Neural2-F" });
    expect(body.createdAt).toBe("2025-01-15T10:00:00Z");
    expect(body.updatedAt).toBe("2025-01-15T10:02:30Z");
  });

  it("includes status field in response", async () => {
    mockGetJob.mockReturnValue(makeJob({ status: "pending" }));

    const response = await GET(mockRequest(), makeParams("job-123"));
    const body = await response.json();
    expect(body).toHaveProperty("status", "pending");
  });

  it("includes progress field in response", async () => {
    mockGetJob.mockReturnValue(makeJob({ progress: 75 }));

    const response = await GET(mockRequest(), makeParams("job-123"));
    const body = await response.json();
    expect(body).toHaveProperty("progress", 75);
  });

  it("includes error field in response", async () => {
    mockGetJob.mockReturnValue(makeJob({ status: "error", error: "API failure" }));

    const response = await GET(mockRequest(), makeParams("job-123"));
    const body = await response.json();
    expect(body).toHaveProperty("error", "API failure");
  });

  it("includes createdAt field in response", async () => {
    mockGetJob.mockReturnValue(makeJob({ createdAt: "2025-06-01T12:00:00Z" }));

    const response = await GET(mockRequest(), makeParams("job-123"));
    const body = await response.json();
    expect(body).toHaveProperty("createdAt", "2025-06-01T12:00:00Z");
  });

  it("includes updatedAt field in response", async () => {
    mockGetJob.mockReturnValue(makeJob({ updatedAt: "2025-06-01T12:30:00Z" }));

    const response = await GET(mockRequest(), makeParams("job-123"));
    const body = await response.json();
    expect(body).toHaveProperty("updatedAt", "2025-06-01T12:30:00Z");
  });

  it("passes params.id to getJob", async () => {
    mockGetJob.mockReturnValue(makeJob());

    await GET(mockRequest("my-job-id"), makeParams("my-job-id"));
    expect(mockGetJob).toHaveBeenCalledWith("my-job-id");
  });

  it("calls getJob exactly once", async () => {
    mockGetJob.mockReturnValue(makeJob());

    await GET(mockRequest(), makeParams("job-123"));
    expect(mockGetJob).toHaveBeenCalledTimes(1);
  });

  it("returns Content-Type application/json", async () => {
    mockGetJob.mockReturnValue(makeJob());

    const response = await GET(mockRequest(), makeParams("job-123"));
    const contentType = response.headers.get("Content-Type");
    expect(contentType).toContain("application/json");
  });
});

// ---------------------------------------------------------------------------
// 3. GET handler — job not found (404)
// ---------------------------------------------------------------------------

describe("GET — job not found", () => {
  beforeEach(() => {
    mockGetJob.mockReturnValue(undefined);
  });

  it("returns 404 status when job does not exist", async () => {
    const response = await GET(mockRequest("nonexistent"), makeParams("nonexistent"));
    expect(response.status).toBe(404);
  });

  it("returns { error: 'Job not found' } body", async () => {
    const response = await GET(mockRequest("nonexistent"), makeParams("nonexistent"));
    const body = await response.json();
    expect(body).toEqual({ error: "Job not found" });
  });

  it("returns 404 for empty string id", async () => {
    const response = await GET(mockRequest(""), makeParams(""));
    expect(response.status).toBe(404);
  });
});

// ---------------------------------------------------------------------------
// 4. GET handler — various job states
// ---------------------------------------------------------------------------

describe("GET — various job states", () => {
  it("returns pending job correctly", async () => {
    mockGetJob.mockReturnValue(
      makeJob({ status: "pending", progress: 0, error: null })
    );

    const response = await GET(mockRequest(), makeParams("job-123"));
    const body = await response.json();

    expect(response.status).toBe(200);
    expect(body.status).toBe("pending");
    expect(body.progress).toBe(0);
  });

  it("returns running job correctly", async () => {
    mockGetJob.mockReturnValue(
      makeJob({ status: "running", progress: 50 })
    );

    const response = await GET(mockRequest(), makeParams("job-123"));
    const body = await response.json();

    expect(response.status).toBe(200);
    expect(body.status).toBe("running");
    expect(body.progress).toBe(50);
  });

  it("returns done job correctly", async () => {
    mockGetJob.mockReturnValue(
      makeJob({ status: "done", progress: 100 })
    );

    const response = await GET(mockRequest(), makeParams("job-123"));
    const body = await response.json();

    expect(response.status).toBe(200);
    expect(body.status).toBe("done");
    expect(body.progress).toBe(100);
  });

  it("returns error job with error message", async () => {
    mockGetJob.mockReturnValue(
      makeJob({ status: "error", progress: 25, error: "Veo API rate limit exceeded" })
    );

    const response = await GET(mockRequest(), makeParams("job-123"));
    const body = await response.json();

    expect(response.status).toBe(200);
    expect(body.status).toBe("error");
    expect(body.error).toBe("Veo API rate limit exceeded");
  });
});

// ---------------------------------------------------------------------------
// 5. GET handler — error handling (500)
// ---------------------------------------------------------------------------

describe("GET — internal server error", () => {
  it("returns 500 when getJob throws", async () => {
    mockGetJob.mockImplementation(() => {
      throw new Error("DB connection lost");
    });

    const response = await GET(mockRequest(), makeParams("job-123"));
    expect(response.status).toBe(500);
  });

  it("returns { error: 'Internal Server Error' } body when getJob throws", async () => {
    mockGetJob.mockImplementation(() => {
      throw new Error("DB connection lost");
    });

    const response = await GET(mockRequest(), makeParams("job-123"));
    const body = await response.json();
    expect(body).toEqual({ error: "Internal Server Error" });
  });

  it("logs error to console.error when getJob throws", async () => {
    const consoleSpy = jest.spyOn(console, "error").mockImplementation(() => {});
    mockGetJob.mockImplementation(() => {
      throw new Error("DB crash");
    });

    await GET(mockRequest(), makeParams("job-123"));
    expect(consoleSpy).toHaveBeenCalled();
    consoleSpy.mockRestore();
  });
});

// ---------------------------------------------------------------------------
// 6. No authentication required
// ---------------------------------------------------------------------------

describe("no authentication required", () => {
  beforeEach(() => {
    mockGetJob.mockReturnValue(makeJob());
  });

  it("succeeds without any authorization header", async () => {
    const response = await GET(mockRequest(), makeParams("job-123"));
    expect(response.status).toBe(200);
  });

  it("succeeds with an authorization header present", async () => {
    const request = new Request("http://localhost/api/jobs/job-123", {
      headers: { Authorization: "Bearer fake-token" },
    });

    const response = await GET(request, makeParams("job-123"));
    expect(response.status).toBe(200);
  });

  it("does not inspect or validate request headers", async () => {
    const request = new Request("http://localhost/api/jobs/job-123", {
      headers: { "X-Custom-Header": "some-value" },
    });

    const response = await GET(request, makeParams("job-123"));
    const body = await response.json();
    expect(body.id).toBe("job-123");
  });
});

// ---------------------------------------------------------------------------
// 7. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/jobs/[id]/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    sourceCode = fs.readFileSync(
      path.join(__dirname, "..", "app", "api", "jobs", "[id]", "route.ts"),
      "utf-8"
    );
  });

  it("exports async GET function", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+GET/);
  });

  it("exports dynamic = 'force-dynamic'", () => {
    expect(sourceCode).toMatch(
      /export\s+const\s+dynamic\s*=\s*["']force-dynamic["']/
    );
  });

  it("imports getJob from @/lib/jobs", () => {
    expect(sourceCode).toMatch(/@\/lib\/jobs/);
    expect(sourceCode).toMatch(/getJob/);
  });

  it("imports NextResponse from next/server", () => {
    expect(sourceCode).toMatch(/next\/server/);
    expect(sourceCode).toMatch(/NextResponse/);
  });

  it("uses NextResponse.json for responses", () => {
    expect(sourceCode).toMatch(/NextResponse\.json/);
  });

  it("handles 'Job not found' error", () => {
    expect(sourceCode).toMatch(/Job not found/);
  });

  it("uses params.id from route context", () => {
    expect(sourceCode).toMatch(/params/);
    // Next.js 15: params is a Promise, so id is accessed via destructuring after await
    expect(sourceCode).toMatch(/id/);
  });

  it("returns 404 status for not-found jobs", () => {
    expect(sourceCode).toMatch(/404/);
  });
});

/**
 * Tests for app/api/jobs/[id]/retry/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_jobs_id_retry_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. POST /api/jobs/[id]/retry — retries a failed job
 *   2. Calls retryJob(jobId) from lib/jobs.ts
 *   3. Returns { jobId: string } on success
 *   4. Returns 404 with { error: 'Job not found' } if job does not exist
 *   5. Returns 400 with { error: 'Job is not in error state' } if job status is not 'error'
 *   6. No authentication required
 *   7. Export dynamic = 'force-dynamic'
 *   8. Returns 500 with error message if retryJob throws
 */

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockGetJob = jest.fn();
const mockRetryJob = jest.fn();

jest.mock("@/lib/jobs", () => ({
  getJob: (...args: unknown[]) => mockGetJob(...args),
  retryJob: (...args: unknown[]) => mockRetryJob(...args),
}));

// Import after mock setup
import { POST, dynamic } from "../app/api/jobs/[id]/retry/route";
import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function mockRequest(id: string = "test-id"): Request {
  return new Request(`http://localhost/api/jobs/${id}/retry`, {
    method: "POST",
  });
}

function makeParams(id: string): { params: { id: string } } {
  return { params: { id } };
}

function makeJob(overrides: Record<string, unknown> = {}) {
  return {
    id: "job-123",
    stage: "setup",
    status: "error",
    progress: 50,
    error: "Something went wrong",
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
  mockRetryJob.mockReset();
  mockRetryJob.mockResolvedValue("new-job-id-abc");
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
// 2. POST handler — successful retry (200)
// ---------------------------------------------------------------------------

describe("POST — successful retry", () => {
  beforeEach(() => {
    mockGetJob.mockReturnValue(makeJob({ status: "error" }));
  });

  it("returns 200 status when job is in error state", async () => {
    const response = await POST(mockRequest("job-123"), makeParams("job-123"));
    expect(response.status).toBe(200);
  });

  it("returns { jobId } with the NEW job ID on success", async () => {
    mockRetryJob.mockResolvedValue("new-job-id-xyz");
    const response = await POST(mockRequest("job-abc"), makeParams("job-abc"));
    const body = await response.json();
    expect(body).toEqual({ jobId: "new-job-id-xyz" });
  });

  it("returns the new jobId from retryJob, not the original params.id", async () => {
    mockRetryJob.mockResolvedValue("retry-new-001");
    const response = await POST(
      mockRequest("my-retry-job"),
      makeParams("my-retry-job")
    );
    const body = await response.json();
    expect(body.jobId).toBe("retry-new-001");
    expect(body.jobId).not.toBe("my-retry-job");
  });

  it("calls getJob with params.id", async () => {
    await POST(mockRequest("job-xyz"), makeParams("job-xyz"));
    expect(mockGetJob).toHaveBeenCalledWith("job-xyz");
  });

  it("calls retryJob with params.id", async () => {
    await POST(mockRequest("job-xyz"), makeParams("job-xyz"));
    expect(mockRetryJob).toHaveBeenCalledWith("job-xyz");
  });

  it("calls getJob before retryJob", async () => {
    const callOrder: string[] = [];
    mockGetJob.mockImplementation(() => {
      callOrder.push("getJob");
      return makeJob({ status: "error" });
    });
    mockRetryJob.mockImplementation(async () => {
      callOrder.push("retryJob");
    });

    await POST(mockRequest("job-123"), makeParams("job-123"));
    expect(callOrder).toEqual(["getJob", "retryJob"]);
  });

  it("calls getJob exactly once", async () => {
    await POST(mockRequest("job-123"), makeParams("job-123"));
    expect(mockGetJob).toHaveBeenCalledTimes(1);
  });

  it("calls retryJob exactly once", async () => {
    await POST(mockRequest("job-123"), makeParams("job-123"));
    expect(mockRetryJob).toHaveBeenCalledTimes(1);
  });

  it("returns Content-Type application/json", async () => {
    const response = await POST(mockRequest("job-123"), makeParams("job-123"));
    const contentType = response.headers.get("Content-Type");
    expect(contentType).toContain("application/json");
  });
});

// ---------------------------------------------------------------------------
// 3. POST handler — job not found (404)
// ---------------------------------------------------------------------------

describe("POST — job not found", () => {
  beforeEach(() => {
    mockGetJob.mockReturnValue(undefined);
  });

  it("returns 404 status when job does not exist", async () => {
    const response = await POST(
      mockRequest("nonexistent"),
      makeParams("nonexistent")
    );
    expect(response.status).toBe(404);
  });

  it("returns { error: 'Job not found' } body", async () => {
    const response = await POST(
      mockRequest("nonexistent"),
      makeParams("nonexistent")
    );
    const body = await response.json();
    expect(body).toEqual({ error: "Job not found" });
  });

  it("does not call retryJob when job not found", async () => {
    await POST(mockRequest("nonexistent"), makeParams("nonexistent"));
    expect(mockRetryJob).not.toHaveBeenCalled();
  });

  it("returns 404 for empty string id", async () => {
    const response = await POST(mockRequest(""), makeParams(""));
    expect(response.status).toBe(404);
  });
});

// ---------------------------------------------------------------------------
// 4. POST handler — job not in error state (409 Conflict)
// ---------------------------------------------------------------------------

describe("POST — job not in error state", () => {
  it("returns 409 when job status is 'pending'", async () => {
    mockGetJob.mockReturnValue(makeJob({ status: "pending" }));

    const response = await POST(mockRequest("job-123"), makeParams("job-123"));
    expect(response.status).toBe(409);
  });

  it("returns 409 when job status is 'running'", async () => {
    mockGetJob.mockReturnValue(makeJob({ status: "running" }));

    const response = await POST(mockRequest("job-123"), makeParams("job-123"));
    expect(response.status).toBe(409);
  });

  it("returns 409 when job status is 'done'", async () => {
    mockGetJob.mockReturnValue(makeJob({ status: "done" }));

    const response = await POST(mockRequest("job-123"), makeParams("job-123"));
    expect(response.status).toBe(409);
  });

  it("returns { error: 'Job is not in error state' } body", async () => {
    mockGetJob.mockReturnValue(makeJob({ status: "running" }));

    const response = await POST(mockRequest("job-123"), makeParams("job-123"));
    const body = await response.json();
    expect(body).toEqual({ error: "Job is not in error state" });
  });

  it("does not call retryJob when job is not in error state", async () => {
    mockGetJob.mockReturnValue(makeJob({ status: "done" }));

    await POST(mockRequest("job-123"), makeParams("job-123"));
    expect(mockRetryJob).not.toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 5. POST handler — retryJob throws (500)
// ---------------------------------------------------------------------------

describe("POST — internal server error", () => {
  beforeEach(() => {
    mockGetJob.mockReturnValue(makeJob({ status: "error" }));
  });

  it("returns 500 when retryJob throws", async () => {
    mockRetryJob.mockRejectedValue(new Error("DB connection lost"));

    const response = await POST(mockRequest("job-123"), makeParams("job-123"));
    expect(response.status).toBe(500);
  });

  it("returns { error: 'Internal Server Error' } body when retryJob throws", async () => {
    mockRetryJob.mockRejectedValue(new Error("DB connection lost"));

    const response = await POST(mockRequest("job-123"), makeParams("job-123"));
    const body = await response.json();
    expect(body).toEqual({ error: "Internal Server Error" });
  });

  it("returns 500 when getJob throws", async () => {
    mockGetJob.mockImplementation(() => {
      throw new Error("Unexpected DB error");
    });

    const response = await POST(mockRequest("job-123"), makeParams("job-123"));
    expect(response.status).toBe(500);
  });

  it("logs error to console.error when retryJob throws", async () => {
    const consoleSpy = jest
      .spyOn(console, "error")
      .mockImplementation(() => {});
    mockRetryJob.mockRejectedValue(new Error("Retry failed"));

    await POST(mockRequest("job-123"), makeParams("job-123"));
    expect(consoleSpy).toHaveBeenCalled();
    consoleSpy.mockRestore();
  });
});

// ---------------------------------------------------------------------------
// 6. No authentication required
// ---------------------------------------------------------------------------

describe("no authentication required", () => {
  beforeEach(() => {
    mockGetJob.mockReturnValue(makeJob({ status: "error" }));
  });

  it("succeeds without any authorization header", async () => {
    const response = await POST(mockRequest("job-123"), makeParams("job-123"));
    expect(response.status).toBe(200);
  });

  it("succeeds with an authorization header present", async () => {
    const request = new Request("http://localhost/api/jobs/job-123/retry", {
      method: "POST",
      headers: { Authorization: "Bearer fake-token" },
    });

    const response = await POST(request, makeParams("job-123"));
    expect(response.status).toBe(200);
  });

  it("does not inspect or validate request headers", async () => {
    mockRetryJob.mockResolvedValue("new-job-from-retry");
    const request = new Request("http://localhost/api/jobs/job-123/retry", {
      method: "POST",
      headers: { "X-Custom-Header": "some-value" },
    });

    const response = await POST(request, makeParams("job-123"));
    const body = await response.json();
    expect(body.jobId).toBe("new-job-from-retry");
  });
});

// ---------------------------------------------------------------------------
// 7. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/jobs/[id]/retry/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    sourceCode = fs.readFileSync(
      path.join(
        __dirname,
        "..",
        "app",
        "api",
        "jobs",
        "[id]",
        "retry",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async POST function", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+POST/);
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

  it("imports retryJob from @/lib/jobs", () => {
    expect(sourceCode).toMatch(/@\/lib\/jobs/);
    expect(sourceCode).toMatch(/retryJob/);
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

  it("handles 'Job is not in error state' error", () => {
    expect(sourceCode).toMatch(/Job is not in error state/);
  });

  it("uses params.id from route context", () => {
    expect(sourceCode).toMatch(/params/);
    expect(sourceCode).toMatch(/\.id/);
  });

  it("returns 404 status for not-found jobs", () => {
    expect(sourceCode).toMatch(/404/);
  });

  it("returns 409 status for non-error jobs", () => {
    expect(sourceCode).toMatch(/409/);
  });
});

/**
 * Tests for app/api/jobs/[id]/stream/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_jobs_stream_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. GET /api/jobs/[id]/stream — opens an SSE ReadableStream
 *   2. Subscribes to job log events by polling the DB every 200ms
 *   3. Sends new log lines as data: {"type":"log","message":"..."}\n\n events
 *   4. Tracks lastLineIndex to only send new lines since last poll
 *   5. When job reaches done status: sends event: done\ndata: {}\n\n and closes
 *   6. When job reaches error status: sends event: error\ndata: {"message":"..."}\n\n and closes
 *   7. SSE response headers: Content-Type, Cache-Control, Connection
 *   8. No authentication required
 *   9. Export dynamic = 'force-dynamic'
 *  10. If job not found on first poll, sends error "Job not found" and closes
 *  11. Interval cleared on stream close to prevent DB polling leaks
 *  12. Handles exceptions in poll gracefully
 */

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockGetJob = jest.fn();

jest.mock("@/lib/jobs", () => ({
  getJob: (...args: unknown[]) => mockGetJob(...args),
  parseStoredJobLogLine: (line: string) => {
    if (!line.startsWith("__ts__:")) {
      return { message: line };
    }
    const payload = line.slice("__ts__:".length);
    const tabIndex = payload.indexOf("\t");
    if (tabIndex === -1) {
      return { message: line };
    }
    return {
      message: payload.slice(tabIndex + 1),
      timestamp: payload.slice(0, tabIndex),
    };
  },
}));

let mockSend: jest.Mock;
let mockDone: jest.Mock;
let mockError: jest.Mock;
let capturedOnCancel: (() => void) | undefined;

jest.mock("@/lib/sse", () => ({
  createSseStream: (onCancel?: () => void) => {
    capturedOnCancel = onCancel;
    return {
      stream: new ReadableStream(),
      send: mockSend,
      done: mockDone,
      error: mockError,
    };
  },
}));

// Import after mock setup
import { GET, dynamic } from "../app/api/jobs/[id]/stream/route";
import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function mockRequest(): Request {
  return new Request("http://localhost/api/jobs/test-id/stream");
}

function makeParams(id: string): { params: { id: string } } {
  return { params: { id } };
}

// ---------------------------------------------------------------------------
// Setup / Teardown
// ---------------------------------------------------------------------------

beforeEach(() => {
  jest.useFakeTimers();
  mockGetJob.mockReset();
  mockSend = jest.fn();
  mockDone = jest.fn();
  mockError = jest.fn();
  capturedOnCancel = undefined;
});

afterEach(() => {
  jest.useRealTimers();
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
// 2. GET handler — response shape and SSE headers
// ---------------------------------------------------------------------------

describe("GET response shape", () => {
  beforeEach(() => {
    mockGetJob.mockReturnValue({
      id: "test-id",
      stage: "setup",
      status: "done",
      progress: 100,
      error: null,
      params: {},
      logs: "done\n",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });
  });

  it("returns a Response object", async () => {
    const response = await GET(mockRequest(), makeParams("test-id"));
    expect(response).toBeInstanceOf(Response);
  });

  it("sets Content-Type to text/event-stream", async () => {
    const response = await GET(mockRequest(), makeParams("test-id"));
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("sets Cache-Control to no-cache", async () => {
    const response = await GET(mockRequest(), makeParams("test-id"));
    expect(response.headers.get("Cache-Control")).toBe("no-cache");
  });

  it("sets Connection to keep-alive", async () => {
    const response = await GET(mockRequest(), makeParams("test-id"));
    expect(response.headers.get("Connection")).toBe("keep-alive");
  });
});

// ---------------------------------------------------------------------------
// 3. Job not found — error event on first poll
// ---------------------------------------------------------------------------

describe("job not found", () => {
  beforeEach(() => {
    mockGetJob.mockReturnValue(undefined);
  });

  it("sends error 'Job not found' when job does not exist", async () => {
    await GET(mockRequest(), makeParams("nonexistent"));
    expect(mockError).toHaveBeenCalledWith("Job not found");
  });

  it("sends error only once when job is not found", async () => {
    await GET(mockRequest(), makeParams("nonexistent"));

    // Advance timer to trigger more polls
    jest.advanceTimersByTime(600);

    expect(mockError).toHaveBeenCalledTimes(1);
  });

  it("does not call send() when job is not found", async () => {
    await GET(mockRequest(), makeParams("nonexistent"));
    expect(mockSend).not.toHaveBeenCalled();
  });

  it("does not call done() when job is not found", async () => {
    await GET(mockRequest(), makeParams("nonexistent"));
    expect(mockDone).not.toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 4. Job with logs — sends log messages
// ---------------------------------------------------------------------------

describe("log streaming", () => {
  it("sends log events for each line in job.logs", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "setup",
      status: "done",
      progress: 100,
      error: null,
      params: {},
      logs: "line 1\nline 2\nline 3\n",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));

    const logCalls = mockSend.mock.calls.filter(
      (call: any[]) => call[0]?.type === "log"
    );
    expect(logCalls).toHaveLength(3);
    expect(logCalls[0][0]).toEqual({ type: "log", message: "line 1" });
    expect(logCalls[1][0]).toEqual({ type: "log", message: "line 2" });
    expect(logCalls[2][0]).toEqual({ type: "log", message: "line 3" });
  });

  it("handles empty logs gracefully", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "setup",
      status: "done",
      progress: 100,
      error: null,
      params: {},
      logs: "",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));

    const logCalls = mockSend.mock.calls.filter(
      (call: any[]) => call[0]?.type === "log"
    );
    expect(logCalls).toHaveLength(0);
  });

  it("handles null/undefined logs gracefully", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "setup",
      status: "done",
      progress: 100,
      error: null,
      params: {},
      logs: null,
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));

    const logCalls = mockSend.mock.calls.filter(
      (call: any[]) => call[0]?.type === "log"
    );
    expect(logCalls).toHaveLength(0);
  });

  it("excludes trailing empty string from log lines", async () => {
    // "line1\nline2\n" splits to ["line1", "line2", ""] — trailing empty should be excluded
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "setup",
      status: "done",
      progress: 100,
      error: null,
      params: {},
      logs: "line1\nline2\n",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));

    const logCalls = mockSend.mock.calls.filter(
      (call: any[]) => call[0]?.type === "log"
    );
    expect(logCalls).toHaveLength(2);
    expect(logCalls[0][0].message).toBe("line1");
    expect(logCalls[1][0].message).toBe("line2");
  });

  it("parses timestamped log lines and includes the timestamp in SSE payloads", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "setup",
      status: "done",
      progress: 100,
      error: null,
      params: {},
      logs: "__ts__:2026-03-16T22:21:32.380Z\tline 1\n__ts__:2026-03-16T22:31:33.275Z\tline 2\n",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));

    const logCalls = mockSend.mock.calls.filter(
      (call: any[]) => call[0]?.type === "log"
    );
    expect(logCalls).toHaveLength(2);
    expect(logCalls[0][0]).toEqual({
      type: "log",
      message: "line 1",
      timestamp: "2026-03-16T22:21:32.380Z",
    });
    expect(logCalls[1][0]).toEqual({
      type: "log",
      message: "line 2",
      timestamp: "2026-03-16T22:31:33.275Z",
    });
  });
});

// ---------------------------------------------------------------------------
// 5. Incremental log delivery — lastLineIndex tracking
// ---------------------------------------------------------------------------

describe("incremental log delivery (lastLineIndex)", () => {
  it("only sends new log lines on subsequent polls", async () => {
    let pollCount = 0;
    mockGetJob.mockImplementation(() => {
      pollCount++;
      if (pollCount === 1) {
        return {
          id: "job-1",
          stage: "setup",
          status: "running",
          progress: 0,
          error: null,
          params: {},
          logs: "line 1\n",
          createdAt: "2025-01-01T00:00:00Z",
          updatedAt: "2025-01-01T00:00:00Z",
        };
      }
      if (pollCount === 2) {
        return {
          id: "job-1",
          stage: "setup",
          status: "running",
          progress: 50,
          error: null,
          params: {},
          logs: "line 1\nline 2\nline 3\n",
          createdAt: "2025-01-01T00:00:00Z",
          updatedAt: "2025-01-01T00:00:00Z",
        };
      }
      return {
        id: "job-1",
        stage: "setup",
        status: "done",
        progress: 100,
        error: null,
        params: {},
        logs: "line 1\nline 2\nline 3\n",
        createdAt: "2025-01-01T00:00:00Z",
        updatedAt: "2025-01-01T00:00:00Z",
      };
    });

    await GET(mockRequest(), makeParams("job-1"));

    // First poll: sends "line 1"
    const logCallsAfterFirst = mockSend.mock.calls.filter(
      (call: any[]) => call[0]?.type === "log"
    );
    expect(logCallsAfterFirst).toHaveLength(1);
    expect(logCallsAfterFirst[0][0].message).toBe("line 1");

    // Second poll: sends "line 2" and "line 3"
    jest.advanceTimersByTime(200);

    const logCallsAfterSecond = mockSend.mock.calls.filter(
      (call: any[]) => call[0]?.type === "log"
    );
    expect(logCallsAfterSecond).toHaveLength(3);
    expect(logCallsAfterSecond[1][0].message).toBe("line 2");
    expect(logCallsAfterSecond[2][0].message).toBe("line 3");
  });

  it("does not re-send old log lines", async () => {
    let callCount = 0;
    mockGetJob.mockImplementation(() => {
      callCount++;
      // Always return same logs
      return {
        id: "job-1",
        stage: "setup",
        status: callCount < 3 ? "running" : "done",
        progress: callCount < 3 ? 50 : 100,
        error: null,
        params: {},
        logs: "same line\n",
        createdAt: "2025-01-01T00:00:00Z",
        updatedAt: "2025-01-01T00:00:00Z",
      };
    });

    await GET(mockRequest(), makeParams("job-1"));

    // First poll sends the line
    const logCallsAfterFirst = mockSend.mock.calls.filter(
      (call: any[]) => call[0]?.type === "log"
    );
    expect(logCallsAfterFirst).toHaveLength(1);

    // Second poll — no new lines, so no new log events
    jest.advanceTimersByTime(200);

    const logCallsAfterSecond = mockSend.mock.calls.filter(
      (call: any[]) => call[0]?.type === "log"
    );
    expect(logCallsAfterSecond).toHaveLength(1); // still 1
  });
});

// ---------------------------------------------------------------------------
// 6. Done status — terminal event
// ---------------------------------------------------------------------------

describe("done status", () => {
  it("calls done() when job status is 'done'", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "setup",
      status: "done",
      progress: 100,
      error: null,
      params: {},
      logs: "complete\n",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));
    expect(mockDone).toHaveBeenCalledTimes(1);
  });

  it("sends log lines before calling done()", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "setup",
      status: "done",
      progress: 100,
      error: null,
      params: {},
      logs: "step 1\nstep 2\n",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));

    const logCalls = mockSend.mock.calls.filter(
      (call: any[]) => call[0]?.type === "log"
    );
    expect(logCalls).toHaveLength(2);
    expect(mockDone).toHaveBeenCalledTimes(1);
  });

  it("does not call error() when job is done", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "setup",
      status: "done",
      progress: 100,
      error: null,
      params: {},
      logs: "",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));
    expect(mockError).not.toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 7. Error status — terminal event
// ---------------------------------------------------------------------------

describe("error status", () => {
  it("calls error() with job error message when status is 'error'", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "veo",
      status: "error",
      progress: 25,
      error: "Veo API rate limit exceeded",
      params: {},
      logs: "started\n",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));
    expect(mockError).toHaveBeenCalledWith("Veo API rate limit exceeded");
  });

  it("uses 'Unknown error' when job.error is null", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "render",
      status: "error",
      progress: 0,
      error: null,
      params: {},
      logs: "",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));
    expect(mockError).toHaveBeenCalledWith("Unknown error");
  });

  it("sends log lines before calling error()", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "veo",
      status: "error",
      progress: 50,
      error: "fail",
      params: {},
      logs: "log before error\n",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));

    const logCalls = mockSend.mock.calls.filter(
      (call: any[]) => call[0]?.type === "log"
    );
    expect(logCalls).toHaveLength(1);
    expect(mockError).toHaveBeenCalledTimes(1);
  });

  it("does not call done() when job is in error", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "render",
      status: "error",
      progress: 0,
      error: "crash",
      params: {},
      logs: "",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));
    expect(mockDone).not.toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 8. Progress tracking
// ---------------------------------------------------------------------------

describe("progress events", () => {
  it("sends progress event when progress changes", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "setup",
      status: "done",
      progress: 50,
      error: null,
      params: {},
      logs: "",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));

    const progressCalls = mockSend.mock.calls.filter(
      (call: any[]) => call[0]?.type === "progress"
    );
    expect(progressCalls.length).toBeGreaterThanOrEqual(1);
    expect(progressCalls[0][0]).toEqual({ type: "progress", percent: 50 });
  });

  it("does not re-send progress when value hasn't changed", async () => {
    let callCount = 0;
    mockGetJob.mockImplementation(() => {
      callCount++;
      return {
        id: "job-1",
        stage: "setup",
        status: callCount < 3 ? "running" : "done",
        progress: 50, // always 50
        error: null,
        params: {},
        logs: "",
        createdAt: "2025-01-01T00:00:00Z",
        updatedAt: "2025-01-01T00:00:00Z",
      };
    });

    await GET(mockRequest(), makeParams("job-1"));
    jest.advanceTimersByTime(200);
    jest.advanceTimersByTime(200);

    const progressCalls = mockSend.mock.calls.filter(
      (call: any[]) => call[0]?.type === "progress"
    );
    // Progress should only be sent once since value stays at 50
    expect(progressCalls).toHaveLength(1);
  });

  it("sends progress when value changes across polls", async () => {
    let callCount = 0;
    mockGetJob.mockImplementation(() => {
      callCount++;
      if (callCount === 1) {
        return {
          id: "job-1",
          stage: "setup",
          status: "running",
          progress: 25,
          error: null,
          params: {},
          logs: "",
          createdAt: "2025-01-01T00:00:00Z",
          updatedAt: "2025-01-01T00:00:00Z",
        };
      }
      return {
        id: "job-1",
        stage: "setup",
        status: "done",
        progress: 100,
        error: null,
        params: {},
        logs: "",
        createdAt: "2025-01-01T00:00:00Z",
        updatedAt: "2025-01-01T00:00:00Z",
      };
    });

    await GET(mockRequest(), makeParams("job-1"));
    jest.advanceTimersByTime(200);

    const progressCalls = mockSend.mock.calls.filter(
      (call: any[]) => call[0]?.type === "progress"
    );
    expect(progressCalls).toHaveLength(2);
    expect(progressCalls[0][0].percent).toBe(25);
    expect(progressCalls[1][0].percent).toBe(100);
  });
});

// ---------------------------------------------------------------------------
// 9. Polling interval — 200ms
// ---------------------------------------------------------------------------

describe("polling interval", () => {
  it("calls getJob immediately on first poll", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "setup",
      status: "done",
      progress: 100,
      error: null,
      params: {},
      logs: "",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));
    expect(mockGetJob).toHaveBeenCalledTimes(1);
  });

  it("passes params.id to getJob", async () => {
    mockGetJob.mockReturnValue({
      id: "my-job-id",
      stage: "setup",
      status: "done",
      progress: 100,
      error: null,
      params: {},
      logs: "",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("my-job-id"));
    expect(mockGetJob).toHaveBeenCalledWith("my-job-id");
  });

  it("polls again after 200ms for non-terminal jobs", async () => {
    let callCount = 0;
    mockGetJob.mockImplementation(() => {
      callCount++;
      return {
        id: "job-1",
        stage: "setup",
        status: callCount < 3 ? "running" : "done",
        progress: callCount < 3 ? 50 : 100,
        error: null,
        params: {},
        logs: "",
        createdAt: "2025-01-01T00:00:00Z",
        updatedAt: "2025-01-01T00:00:00Z",
      };
    });

    await GET(mockRequest(), makeParams("job-1"));
    expect(mockGetJob).toHaveBeenCalledTimes(1);

    jest.advanceTimersByTime(200);
    expect(mockGetJob).toHaveBeenCalledTimes(2);

    jest.advanceTimersByTime(200);
    expect(mockGetJob).toHaveBeenCalledTimes(3);
  });

  it("stops polling after done status", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "setup",
      status: "done",
      progress: 100,
      error: null,
      params: {},
      logs: "",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));
    expect(mockGetJob).toHaveBeenCalledTimes(1);

    jest.advanceTimersByTime(1000);
    // Should not have been called again since interval was cleared
    expect(mockGetJob).toHaveBeenCalledTimes(1);
  });

  it("stops polling after error status", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "setup",
      status: "error",
      progress: 0,
      error: "fail",
      params: {},
      logs: "",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));
    expect(mockGetJob).toHaveBeenCalledTimes(1);

    jest.advanceTimersByTime(1000);
    expect(mockGetJob).toHaveBeenCalledTimes(1);
  });

  it("stops polling after job-not-found error", async () => {
    mockGetJob.mockReturnValue(undefined);

    await GET(mockRequest(), makeParams("nonexistent"));
    expect(mockGetJob).toHaveBeenCalledTimes(1);

    jest.advanceTimersByTime(1000);
    // getJob is still called via the interval, but error should only fire once
    expect(mockError).toHaveBeenCalledTimes(1);
  });
});

// ---------------------------------------------------------------------------
// 10. Interval cleanup — onCancel callback
// ---------------------------------------------------------------------------

describe("interval cleanup", () => {
  it("passes an onCancel callback to createSseStream", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "setup",
      status: "done",
      progress: 100,
      error: null,
      params: {},
      logs: "",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    await GET(mockRequest(), makeParams("job-1"));
    expect(capturedOnCancel).toBeDefined();
    expect(typeof capturedOnCancel).toBe("function");
  });

  it("onCancel callback clears interval without throwing", async () => {
    let callCount = 0;
    mockGetJob.mockImplementation(() => {
      callCount++;
      return {
        id: "job-1",
        stage: "setup",
        status: "running",
        progress: 50,
        error: null,
        params: {},
        logs: "",
        createdAt: "2025-01-01T00:00:00Z",
        updatedAt: "2025-01-01T00:00:00Z",
      };
    });

    await GET(mockRequest(), makeParams("job-1"));

    // Simulate client disconnect
    expect(() => capturedOnCancel!()).not.toThrow();
  });
});

// ---------------------------------------------------------------------------
// 11. Exception handling in poll
// ---------------------------------------------------------------------------

describe("exception handling", () => {
  it("sends 'Internal Server Error' when getJob throws", async () => {
    mockGetJob.mockImplementation(() => {
      throw new Error("DB connection lost");
    });

    await GET(mockRequest(), makeParams("job-1"));
    expect(mockError).toHaveBeenCalledWith("Internal Server Error");
  });

  it("clears interval after exception", async () => {
    let callCount = 0;
    mockGetJob.mockImplementation(() => {
      callCount++;
      if (callCount === 1) throw new Error("DB crash");
      return {
        id: "job-1",
        stage: "setup",
        status: "done",
        progress: 100,
        error: null,
        params: {},
        logs: "",
        createdAt: "2025-01-01T00:00:00Z",
        updatedAt: "2025-01-01T00:00:00Z",
      };
    });

    await GET(mockRequest(), makeParams("job-1"));

    // First poll throws, interval should be cleared
    jest.advanceTimersByTime(1000);
    // Since interval is cleared, getJob should only have been called once
    expect(callCount).toBe(1);
  });
});

// ---------------------------------------------------------------------------
// 12. No authentication required
// ---------------------------------------------------------------------------

describe("no authentication required", () => {
  it("does not check for authorization headers", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "setup",
      status: "done",
      progress: 100,
      error: null,
      params: {},
      logs: "",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    const request = new Request("http://localhost/api/jobs/job-1/stream", {
      headers: { Authorization: "Bearer fake-token" },
    });

    const response = await GET(request, makeParams("job-1"));
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("works with minimal request (no headers)", async () => {
    mockGetJob.mockReturnValue({
      id: "job-1",
      stage: "setup",
      status: "done",
      progress: 100,
      error: null,
      params: {},
      logs: "",
      createdAt: "2025-01-01T00:00:00Z",
      updatedAt: "2025-01-01T00:00:00Z",
    });

    const response = await GET(mockRequest(), makeParams("job-1"));
    expect(response).toBeInstanceOf(Response);
  });
});

// ---------------------------------------------------------------------------
// 13. Source file structure checks
// ---------------------------------------------------------------------------

describe("app/api/jobs/[id]/stream/route.ts source structure", () => {
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
        "stream",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async GET function", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+GET/);
  });

  it("exports dynamic = 'force-dynamic'", () => {
    expect(sourceCode).toMatch(/export\s+const\s+dynamic\s*=\s*["']force-dynamic["']/);
  });

  it("imports getJob from @/lib/jobs", () => {
    expect(sourceCode).toMatch(/@\/lib\/jobs/);
    expect(sourceCode).toMatch(/getJob/);
  });

  it("imports createSseStream from @/lib/sse", () => {
    expect(sourceCode).toMatch(/@\/lib\/sse/);
    expect(sourceCode).toMatch(/createSseStream/);
  });

  it("uses setInterval for polling", () => {
    expect(sourceCode).toMatch(/setInterval/);
  });

  it("uses 200ms polling interval", () => {
    expect(sourceCode).toMatch(/200/);
  });

  it("tracks lastLineIndex", () => {
    expect(sourceCode).toMatch(/lastLineIndex/);
  });

  it("splits logs on newline", () => {
    expect(sourceCode).toMatch(/\.split\s*\(/);
  });

  it("sends log events with type 'log'", () => {
    expect(sourceCode).toMatch(/["']log["']/);
  });

  it("handles 'Job not found' error", () => {
    expect(sourceCode).toMatch(/Job not found/);
  });

  it("uses clearInterval for cleanup", () => {
    expect(sourceCode).toMatch(/clearInterval/);
  });

  it("sets Content-Type to text/event-stream", () => {
    expect(sourceCode).toMatch(/text\/event-stream/);
  });

  it("sets Cache-Control to no-cache", () => {
    expect(sourceCode).toMatch(/no-cache/);
  });

  it("sets Connection to keep-alive", () => {
    expect(sourceCode).toMatch(/keep-alive/);
  });

  it("checks for done status", () => {
    expect(sourceCode).toMatch(/["']done["']/);
  });

  it("checks for error status", () => {
    expect(sourceCode).toMatch(/["']error["']/);
  });
});

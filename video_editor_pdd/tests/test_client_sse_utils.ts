import {
  extractJobIdFromSse,
  readSseStartResult,
  waitForJobCompletion,
} from "../lib/client/sse-utils";

describe("lib/client/sse-utils", () => {
  it("extracts a jobId from an SSE stream", async () => {
    const stream = new ReadableStream<Uint8Array>({
      start(controller) {
        controller.enqueue(
          new TextEncoder().encode('data: {"jobId":"sse-job-123"}\n\n'),
        );
        controller.close();
      },
    });

    const response = new Response(stream, {
      headers: { "Content-Type": "text/event-stream" },
    });

    await expect(extractJobIdFromSse(response)).resolves.toBe("sse-job-123");
  });

  it("extracts a jobId from a JSON response", async () => {
    const response = new Response(JSON.stringify({ jobId: "json-job-456" }), {
      headers: { "Content-Type": "application/json" },
    });

    await expect(extractJobIdFromSse(response)).resolves.toBe("json-job-456");
  });

  it("returns null for SSE error events", async () => {
    const stream = new ReadableStream<Uint8Array>({
      start(controller) {
        controller.enqueue(
          new TextEncoder().encode(
            'event: error\ndata: {"message":"Render failed"}\n\n',
          ),
        );
        controller.close();
      },
    });

    const response = new Response(stream, {
      headers: { "Content-Type": "text/event-stream" },
    });

    await expect(extractJobIdFromSse(response)).resolves.toBeNull();
  });

  it("returns the SSE error message for callers that need UI state", async () => {
    const stream = new ReadableStream<Uint8Array>({
      start(controller) {
        controller.enqueue(
          new TextEncoder().encode(
            'event: error\ndata: {"message":"Spec generation failed"}\n\n',
          ),
        );
        controller.close();
      },
    });

    const response = new Response(stream, {
      headers: { "Content-Type": "text/event-stream" },
    });

    await expect(readSseStartResult(response)).resolves.toEqual({
      jobId: null,
      errorMessage: "Spec generation failed",
    });
  });

  it("waits until a job reaches done status", async () => {
    const fetchImpl = jest
      .fn<Promise<Response>, [string]>()
      .mockResolvedValueOnce(
        new Response(JSON.stringify({ status: "running", error: null }), {
          headers: { "Content-Type": "application/json" },
        }),
      )
      .mockResolvedValueOnce(
        new Response(JSON.stringify({ status: "done", error: null }), {
          headers: { "Content-Type": "application/json" },
        }),
      );
    const sleepImpl = jest.fn<Promise<void>, [number]>().mockResolvedValue();

    await expect(
      waitForJobCompletion("job-123", {
        fetchImpl,
        sleepImpl,
        pollIntervalMs: 1,
        timeoutMs: 100,
      }),
    ).resolves.toBeUndefined();

    expect(fetchImpl).toHaveBeenNthCalledWith(1, "/api/jobs/job-123");
    expect(fetchImpl).toHaveBeenNthCalledWith(2, "/api/jobs/job-123");
    expect(sleepImpl).toHaveBeenCalledWith(1);
  });

  it("throws with the job error when a job reaches error status", async () => {
    const fetchImpl = jest.fn<Promise<Response>, [string]>().mockResolvedValue(
      new Response(JSON.stringify({ status: "error", error: "render failed" }), {
        headers: { "Content-Type": "application/json" },
      }),
    );

    await expect(
      waitForJobCompletion("job-999", {
        fetchImpl,
        sleepImpl: jest.fn(),
        pollIntervalMs: 1,
        timeoutMs: 100,
      }),
    ).rejects.toThrow("render failed");
  });
});

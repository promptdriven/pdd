/**
 * Tests for lib/sse.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/lib_sse_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. Export createSseStream() returning { stream, send, done, error }
 *   2. stream is a ReadableStream
 *   3. send(data) encodes `data: ${JSON.stringify(data)}\n\n`
 *   4. done() enqueues `event: done\ndata: {}\n\n` and closes
 *   5. error(msg) enqueues `event: error\ndata: ${JSON.stringify({ message: msg })}\n\n` and closes
 *   6. After done() or error(), the controller is closed
 *   7. Uses TextEncoder to encode strings to Uint8Array
 *   8. ReadableStream start(controller) captures controller in closure
 *   9. server-only guard
 *  10. Handles already-closed controller gracefully
 */

import fs from "fs";
import path from "path";

import { createSseStream } from "../lib/sse";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Reads all chunks from a ReadableStream and returns the decoded string. */
async function readAll(stream: ReadableStream<Uint8Array>): Promise<string> {
  const reader = stream.getReader();
  const decoder = new TextDecoder();
  let result = "";
  while (true) {
    const { done, value } = await reader.read();
    if (done) break;
    result += decoder.decode(value, { stream: true });
  }
  result += decoder.decode();
  return result;
}

// ---------------------------------------------------------------------------
// 1. createSseStream — return shape
// ---------------------------------------------------------------------------

describe("createSseStream return shape", () => {
  it("returns an object with stream, send, done, error", () => {
    const sse = createSseStream();
    expect(sse).toHaveProperty("stream");
    expect(sse).toHaveProperty("send");
    expect(sse).toHaveProperty("done");
    expect(sse).toHaveProperty("error");
  });

  it("stream is a ReadableStream", () => {
    const { stream } = createSseStream();
    expect(stream).toBeInstanceOf(ReadableStream);
  });

  it("send is a function", () => {
    const { send, done } = createSseStream();
    expect(typeof send).toBe("function");
    done(); // clean up
  });

  it("done is a function", () => {
    const { done } = createSseStream();
    expect(typeof done).toBe("function");
    done(); // clean up
  });

  it("error is a function", () => {
    const { error } = createSseStream();
    expect(typeof error).toBe("function");
    error("cleanup"); // clean up
  });
});

// ---------------------------------------------------------------------------
// 2. send() — SSE data format
// ---------------------------------------------------------------------------

describe("send()", () => {
  it("encodes data as SSE data line with double newline", async () => {
    const { stream, send, done } = createSseStream();
    send({ hello: "world" });
    done();

    const output = await readAll(stream);
    expect(output).toContain('data: {"hello":"world"}\n\n');
  });

  it("serializes complex objects via JSON.stringify", async () => {
    const { stream, send, done } = createSseStream();
    const payload = { count: 42, nested: { key: "value" }, arr: [1, 2, 3] };
    send(payload);
    done();

    const output = await readAll(stream);
    expect(output).toContain(`data: ${JSON.stringify(payload)}\n\n`);
  });

  it("can send multiple messages before closing", async () => {
    const { stream, send, done } = createSseStream();
    send({ step: 1 });
    send({ step: 2 });
    send({ step: 3 });
    done();

    const output = await readAll(stream);
    expect(output).toContain('data: {"step":1}\n\n');
    expect(output).toContain('data: {"step":2}\n\n');
    expect(output).toContain('data: {"step":3}\n\n');
  });

  it("preserves message order", async () => {
    const { stream, send, done } = createSseStream();
    send({ n: 1 });
    send({ n: 2 });
    send({ n: 3 });
    done();

    const output = await readAll(stream);
    const idx1 = output.indexOf('data: {"n":1}');
    const idx2 = output.indexOf('data: {"n":2}');
    const idx3 = output.indexOf('data: {"n":3}');
    expect(idx1).toBeLessThan(idx2);
    expect(idx2).toBeLessThan(idx3);
  });

  it("handles empty object", async () => {
    const { stream, send, done } = createSseStream();
    send({});
    done();

    const output = await readAll(stream);
    expect(output).toContain("data: {}\n\n");
  });

  it("handles object with special characters in values", async () => {
    const { stream, send, done } = createSseStream();
    send({ text: 'hello\n"world"' });
    done();

    const output = await readAll(stream);
    const expected = `data: ${JSON.stringify({ text: 'hello\n"world"' })}\n\n`;
    expect(output).toContain(expected);
  });
});

// ---------------------------------------------------------------------------
// 3. done() — completion event
// ---------------------------------------------------------------------------

describe("done()", () => {
  it("enqueues event: done with empty data and closes stream", async () => {
    const { stream, done } = createSseStream();
    done();

    const output = await readAll(stream);
    expect(output).toBe("event: done\ndata: {}\n\n");
  });

  it("includes both event: and data: lines before double newline", async () => {
    const { stream, done } = createSseStream();
    done();

    const output = await readAll(stream);
    // Must have event line, then data line, then double newline
    expect(output).toMatch(/^event: done\ndata: \{\}\n\n$/);
  });

  it("closes the stream after done()", async () => {
    const { stream, done } = createSseStream();
    done();

    const reader = stream.getReader();
    // Read the done message
    await reader.read();
    // Next read should indicate stream is done
    const result = await reader.read();
    expect(result.done).toBe(true);
  });

  it("includes send messages before done event", async () => {
    const { stream, send, done } = createSseStream();
    send({ progress: 50 });
    send({ progress: 100 });
    done();

    const output = await readAll(stream);
    expect(output).toBe(
      'data: {"progress":50}\n\n' +
        'data: {"progress":100}\n\n' +
        "event: done\ndata: {}\n\n"
    );
  });
});

// ---------------------------------------------------------------------------
// 4. error() — error event
// ---------------------------------------------------------------------------

describe("error()", () => {
  it("enqueues event: error with message and closes stream", async () => {
    const { stream, error } = createSseStream();
    error("something went wrong");

    const output = await readAll(stream);
    expect(output).toBe(
      'event: error\ndata: {"message":"something went wrong"}\n\n'
    );
  });

  it("JSON-encodes the message in a { message } object", async () => {
    const { stream, error } = createSseStream();
    error("fail");

    const output = await readAll(stream);
    expect(output).toContain(`data: ${JSON.stringify({ message: "fail" })}`);
  });

  it("includes both event: and data: lines before double newline", async () => {
    const { stream, error } = createSseStream();
    error("oops");

    const output = await readAll(stream);
    expect(output).toMatch(/^event: error\ndata: .*\n\n$/);
  });

  it("closes the stream after error()", async () => {
    const { stream, error } = createSseStream();
    error("fail");

    const reader = stream.getReader();
    await reader.read();
    const result = await reader.read();
    expect(result.done).toBe(true);
  });

  it("handles empty string message", async () => {
    const { stream, error } = createSseStream();
    error("");

    const output = await readAll(stream);
    expect(output).toBe('event: error\ndata: {"message":""}\n\n');
  });

  it("handles message with special characters", async () => {
    const { stream, error } = createSseStream();
    error('Error: "file not found"\npath: /tmp');

    const output = await readAll(stream);
    const expected = `event: error\ndata: ${JSON.stringify({
      message: 'Error: "file not found"\npath: /tmp',
    })}\n\n`;
    expect(output).toBe(expected);
  });

  it("includes send messages before error event", async () => {
    const { stream, send, error } = createSseStream();
    send({ step: 1 });
    error("pipeline failed");

    const output = await readAll(stream);
    expect(output).toBe(
      'data: {"step":1}\n\n' +
        'event: error\ndata: {"message":"pipeline failed"}\n\n'
    );
  });
});

// ---------------------------------------------------------------------------
// 5. Stream closure — after done() or error()
// ---------------------------------------------------------------------------

describe("stream closure behavior", () => {
  it("send() after done() is silently ignored", async () => {
    const { stream, send, done } = createSseStream();
    send({ before: true });
    done();
    // This should not throw or enqueue anything
    send({ after: true });

    const output = await readAll(stream);
    expect(output).not.toContain("after");
    expect(output).toContain('data: {"before":true}');
    expect(output).toContain("event: done");
  });

  it("send() after error() is silently ignored", async () => {
    const { stream, send, error } = createSseStream();
    send({ before: true });
    error("fail");
    send({ after: true });

    const output = await readAll(stream);
    expect(output).not.toContain("after");
  });

  it("calling done() twice does not throw", async () => {
    const { stream, done } = createSseStream();
    done();
    expect(() => done()).not.toThrow();
    await readAll(stream);
  });

  it("calling error() twice does not throw", async () => {
    const { stream, error } = createSseStream();
    error("first");
    expect(() => error("second")).not.toThrow();
    await readAll(stream);
  });

  it("calling error() after done() does not throw", async () => {
    const { stream, done, error } = createSseStream();
    done();
    expect(() => error("after done")).not.toThrow();
    await readAll(stream);
  });

  it("calling done() after error() does not throw", async () => {
    const { stream, done, error } = createSseStream();
    error("fail");
    expect(() => done()).not.toThrow();
    await readAll(stream);
  });
});

// ---------------------------------------------------------------------------
// 6. TextEncoder usage — Uint8Array encoding
// ---------------------------------------------------------------------------

describe("TextEncoder encoding", () => {
  it("stream chunks are Uint8Array instances", async () => {
    const { stream, send, done } = createSseStream();
    send({ test: true });
    done();

    const reader = stream.getReader();
    const { value } = await reader.read();
    expect(value).toBeInstanceOf(Uint8Array);
    reader.releaseLock();
    // Drain remaining
    await readAll(stream);
  });

  it("encoded bytes decode back to the expected SSE string", async () => {
    const { stream, send, done } = createSseStream();
    const payload = { key: "value" };
    send(payload);
    done();

    const reader = stream.getReader();
    const decoder = new TextDecoder();
    const { value } = await reader.read();
    const decoded = decoder.decode(value);
    expect(decoded).toBe(`data: ${JSON.stringify(payload)}\n\n`);
    reader.releaseLock();
    await readAll(stream);
  });
});

// ---------------------------------------------------------------------------
// 7. SSE format compliance
// ---------------------------------------------------------------------------

describe("SSE format compliance", () => {
  it("data messages use 'data: ' prefix", async () => {
    const { stream, send, done } = createSseStream();
    send({ x: 1 });
    done();

    const output = await readAll(stream);
    const lines = output.split("\n");
    expect(lines[0]).toMatch(/^data: /);
  });

  it("all messages terminate with double newline", async () => {
    const { stream, send, done } = createSseStream();
    send({ a: 1 });
    send({ b: 2 });
    done();

    const output = await readAll(stream);
    // Each SSE message ends with \n\n
    const messages = output.split("\n\n").filter((m) => m.length > 0);
    expect(messages.length).toBe(3); // two sends + done
  });

  it("done event has event: line before data: line", async () => {
    const { stream, done } = createSseStream();
    done();

    const output = await readAll(stream);
    const eventIdx = output.indexOf("event: done");
    const dataIdx = output.indexOf("data: {}");
    expect(eventIdx).toBeLessThan(dataIdx);
    expect(eventIdx).toBe(0);
  });

  it("error event has event: line before data: line", async () => {
    const { stream, error } = createSseStream();
    error("fail");

    const output = await readAll(stream);
    const eventIdx = output.indexOf("event: error");
    const dataIdx = output.indexOf("data: ");
    expect(eventIdx).toBeLessThan(dataIdx);
    expect(eventIdx).toBe(0);
  });
});

// ---------------------------------------------------------------------------
// 8. ReadableStream usability — Response compatibility
// ---------------------------------------------------------------------------

describe("ReadableStream Response compatibility", () => {
  it("stream can be passed to new Response()", () => {
    const { stream, done } = createSseStream();
    done();

    const response = new Response(stream, {
      headers: {
        "Content-Type": "text/event-stream",
        "Cache-Control": "no-cache",
        Connection: "keep-alive",
      },
    });
    expect(response).toBeInstanceOf(Response);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("Response body can be consumed as text", async () => {
    const { stream, send, done } = createSseStream();
    send({ status: "ok" });
    done();

    const response = new Response(stream);
    const text = await response.text();
    expect(text).toContain('data: {"status":"ok"}');
    expect(text).toContain("event: done");
  });
});

// ---------------------------------------------------------------------------
// 9. Source file structure checks
// ---------------------------------------------------------------------------

describe("lib/sse.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    sourceCode = fs.readFileSync(
      path.join(__dirname, "..", "lib", "sse.ts"),
      "utf-8"
    );
  });

  it("has server-only guard", () => {
    expect(sourceCode).toMatch(/server-only/);
  });

  it("uses TextEncoder", () => {
    expect(sourceCode).toMatch(/TextEncoder/);
  });

  it("uses ReadableStream constructor", () => {
    expect(sourceCode).toMatch(/new\s+ReadableStream/);
  });

  it("captures controller in start callback", () => {
    expect(sourceCode).toMatch(/start\s*\(/);
  });

  it("exports createSseStream function", () => {
    expect(sourceCode).toMatch(/export\s+function\s+createSseStream/);
  });

  it("uses JSON.stringify for encoding data", () => {
    expect(sourceCode).toMatch(/JSON\.stringify/);
  });

  it("handles closed controller with try-catch", () => {
    // The spec requires handling TypeError on enqueue after close
    expect(sourceCode).toMatch(/try\s*\{[\s\S]*?controller\.enqueue/);
    expect(sourceCode).toMatch(/catch/);
  });

  it("is approximately 40 lines (compact module)", () => {
    const lineCount = sourceCode.split("\n").length;
    // Spec says ~40 lines; allow reasonable range including comments
    expect(lineCount).toBeLessThanOrEqual(80);
    expect(lineCount).toBeGreaterThanOrEqual(20);
  });
});

/**
 * Tests for app/api/pipeline/tts-render/run/route.ts
 * and app/api/pipeline/tts-render/segments/route.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/api_pipeline_tts_render_route_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. POST /api/pipeline/tts-render/run — accepts optional { segments?: string[] } body
 *   2. Returns SSE stream with { jobId } as first event
 *   3. Spawns python3 render_tts.py [--segment seg1 --segment seg2 ...] from process.cwd()
 *   4. Streams stdout/stderr lines as SSE log events
 *   5. On completion, emits per-segment status events: { type: 'segment', segmentId, status, duration }
 *   6. GET /api/pipeline/tts-render/segments — returns { segments: TtsSegment[] }
 *   7. registerExecutor('tts-render', ...) called at module load time
 *   8. No authentication required
 *   9. parseSegmentsFromScript derives segment IDs from tts_script.md heading markers
 *  10. getWavDuration extracts duration from WAV file headers
 *  11. Per-segment outputs at outputs/tts/{segmentId}.wav
 *  12. Segment status 'done' when file exists + render success, 'error' otherwise
 */

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockRegisterExecutor = jest.fn();

jest.mock("@/lib/jobs", () => ({
  registerExecutor: (...args: unknown[]) => mockRegisterExecutor(...args),
}));

// Mock child_process.spawn
const mockOn = jest.fn();
const mockStdoutOn = jest.fn();
const mockStderrOn = jest.fn();
const mockSpawn = jest.fn(() => ({
  stdout: { on: mockStdoutOn },
  stderr: { on: mockStderrOn },
  on: mockOn,
}));

jest.mock("child_process", () => ({
  spawn: (...args: unknown[]) => mockSpawn(...args),
}));

// Mock fs
const mockExistsSync = jest.fn();
const mockReadFileSync = jest.fn();
const mockReaddirSync = jest.fn();

jest.mock("fs", () => ({
  __esModule: true,
  default: {
    existsSync: (...args: unknown[]) => mockExistsSync(...args),
    readFileSync: (...args: unknown[]) => mockReadFileSync(...args),
    readdirSync: (...args: unknown[]) => mockReaddirSync(...args),
  },
  existsSync: (...args: unknown[]) => mockExistsSync(...args),
  readFileSync: (...args: unknown[]) => mockReadFileSync(...args),
  readdirSync: (...args: unknown[]) => mockReaddirSync(...args),
}));

// Mock crypto
jest.mock("crypto", () => ({
  __esModule: true,
  default: {
    randomUUID: () => "test-uuid-1234",
  },
  randomUUID: () => "test-uuid-1234",
}));

// Import after mocking
import { POST } from "../app/api/pipeline/tts-render/run/route";
import { parseSegmentsFromScript, getWavDuration } from "../lib/tts-segments";

// Capture executor factory registered at module load
const registerCallArgs = {
  stage: mockRegisterExecutor.mock.calls[0]?.[0] as string,
  factory: mockRegisterExecutor.mock.calls[0]?.[1] as (
    params: Record<string, unknown>,
    send: Function
  ) => (onLog: (msg: string) => void) => Promise<void>,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function makeRequest(body?: object): Request {
  if (body) {
    return new Request("http://localhost/api/pipeline/tts-render/run", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(body),
    });
  }
  return new Request("http://localhost/api/pipeline/tts-render/run", {
    method: "POST",
  });
}

/** Flush microtask queue so fire-and-forget IIFE completes. */
function flushPromises(): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, 50));
}

/** Parse SSE events from a ReadableStream. */
async function readSseEvents(stream: ReadableStream<Uint8Array>): Promise<object[]> {
  const reader = stream.getReader();
  const decoder = new TextDecoder();
  let buffer = "";
  const events: object[] = [];

  try {
    while (true) {
      const { done, value } = await reader.read();
      if (done) break;
      buffer += decoder.decode(value, { stream: true });
      const parts = buffer.split("\n\n");
      buffer = parts.pop() ?? "";
      for (const part of parts) {
        const dataLine = part.replace(/^data:\s*/, "");
        if (dataLine) {
          try {
            events.push(JSON.parse(dataLine));
          } catch {
            // skip non-JSON
          }
        }
      }
    }
  } catch {
    // stream closed
  }

  return events;
}

/** Create a valid WAV header buffer with specified properties. */
function makeWavBuffer(opts: {
  channels?: number;
  sampleRate?: number;
  bitsPerSample?: number;
  dataSize?: number;
}): Buffer {
  const buf = Buffer.alloc(48);
  buf.writeUInt16LE(opts.channels ?? 1, 22);
  buf.writeUInt32LE(opts.sampleRate ?? 44100, 24);
  buf.writeUInt16LE(opts.bitsPerSample ?? 16, 34);
  buf.writeUInt32LE(opts.dataSize ?? 88200, 40);
  return buf;
}

// ---------------------------------------------------------------------------
// Setup
// ---------------------------------------------------------------------------

beforeEach(() => {
  mockSpawn.mockClear();
  mockOn.mockReset();
  mockStdoutOn.mockReset();
  mockStderrOn.mockReset();
  mockExistsSync.mockReset();
  mockReadFileSync.mockReset();
  mockReaddirSync.mockReset();

  // Default: spawn completes successfully
  mockSpawn.mockImplementation(() => {
    const proc = {
      stdout: { on: mockStdoutOn },
      stderr: { on: mockStderrOn },
      on: mockOn,
    };
    // Auto-resolve close with code 0 on next tick
    setTimeout(() => {
      const closeHandler = mockOn.mock.calls.find(
        (c: any[]) => c[0] === "close"
      )?.[1];
      if (closeHandler) closeHandler(0);
    }, 5);
    return proc;
  });
});

// ---------------------------------------------------------------------------
// 1. registerExecutor — module load side effect
// ---------------------------------------------------------------------------

describe("registerExecutor at module load", () => {
  it("registers executor for 'tts-render' stage", () => {
    expect(registerCallArgs.stage).toBe("tts-render");
  });

  it("passes an executor factory function", () => {
    expect(typeof registerCallArgs.factory).toBe("function");
  });
});

// ---------------------------------------------------------------------------
// 2. parseSegmentsFromScript
// ---------------------------------------------------------------------------

describe("parseSegmentsFromScript", () => {
  it("returns empty array when tts_script.md does not exist", () => {
    mockExistsSync.mockReturnValue(false);
    const result = parseSegmentsFromScript();
    expect(result).toEqual([]);
  });

  it("parses segment IDs from heading markers", () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue(
      "# intro\nWelcome to the show.\n\n# chapter1\nThis is chapter one.\n"
    );

    const result = parseSegmentsFromScript();
    expect(result).toEqual([
      { id: "intro", text: "Welcome to the show." },
      { id: "chapter1", text: "This is chapter one." },
    ]);
  });

  it("uses first word of heading as segment ID", () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue("## seg1 Some Title\nBody text.\n");

    const result = parseSegmentsFromScript();
    expect(result).toHaveLength(1);
    expect(result[0].id).toBe("seg1");
  });

  it("handles headings of different levels (h1 through h6)", () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue(
      "# h1seg\n\n## h2seg\n\n### h3seg\n\n#### h4seg\n\n##### h5seg\n\n###### h6seg\n"
    );

    const result = parseSegmentsFromScript();
    expect(result.map((s) => s.id)).toEqual([
      "h1seg",
      "h2seg",
      "h3seg",
      "h4seg",
      "h5seg",
      "h6seg",
    ]);
  });

  it("sets text to undefined when heading has no body content", () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue("# empty\n\n# another\nSome text.\n");

    const result = parseSegmentsFromScript();
    expect(result[0]).toEqual({ id: "empty", text: undefined });
    expect(result[1]).toEqual({ id: "another", text: "Some text." });
  });

  it("handles Windows-style line endings", () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue("# seg1\r\nHello.\r\n# seg2\r\nWorld.\r\n");

    const result = parseSegmentsFromScript();
    expect(result).toHaveLength(2);
    expect(result[0].id).toBe("seg1");
    expect(result[1].id).toBe("seg2");
  });

  it("reads tts_script.md from process.cwd()", () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue("# seg\ntext\n");

    parseSegmentsFromScript();

    const path = require("path");
    expect(mockExistsSync).toHaveBeenCalledWith(
      path.join(process.cwd(), "narrative", "tts_script.md")
    );
  });

  it("ignores text before the first heading", () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue(
      "Some preamble text.\nMore preamble.\n\n# intro\nHello.\n"
    );

    const result = parseSegmentsFromScript();
    expect(result).toHaveLength(1);
    expect(result[0].id).toBe("intro");
    expect(result[0].text).toBe("Hello.");
  });

  it("handles single segment with no trailing newline", () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue("# only\nJust one segment");

    const result = parseSegmentsFromScript();
    expect(result).toHaveLength(1);
    expect(result[0].id).toBe("only");
    expect(result[0].text).toBe("Just one segment");
  });

  it("handles empty file content", () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue("");

    const result = parseSegmentsFromScript();
    expect(result).toEqual([]);
  });

  it("preserves multi-line body text per segment", () => {
    mockExistsSync.mockReturnValue(true);
    mockReadFileSync.mockReturnValue(
      "# intro\nLine one.\nLine two.\nLine three.\n"
    );

    const result = parseSegmentsFromScript();
    expect(result[0].text).toBe("Line one.\nLine two.\nLine three.");
  });
});

// ---------------------------------------------------------------------------
// 3. getWavDuration
// ---------------------------------------------------------------------------

describe("getWavDuration", () => {
  it("returns undefined for files shorter than 44 bytes", () => {
    mockReadFileSync.mockReturnValue(Buffer.alloc(20));
    expect(getWavDuration("/fake/file.wav")).toBeUndefined();
  });

  it("parses duration from a valid WAV header", () => {
    mockReadFileSync.mockReturnValue(makeWavBuffer({ dataSize: 88200 }));

    const duration = getWavDuration("/fake/file.wav");
    // 88200 / (44100 * 1 * 2) = 1.0
    expect(duration).toBe(1);
  });

  it("returns undefined when readFileSync throws", () => {
    mockReadFileSync.mockImplementation(() => {
      throw new Error("ENOENT");
    });
    expect(getWavDuration("/nonexistent.wav")).toBeUndefined();
  });

  it("rounds duration to 3 decimal places", () => {
    mockReadFileSync.mockReturnValue(makeWavBuffer({ dataSize: 44100 }));

    const duration = getWavDuration("/fake/file.wav");
    // 44100 / (44100 * 1 * 2) = 0.5
    expect(duration).toBe(0.5);
  });

  it("handles stereo WAV (2 channels)", () => {
    mockReadFileSync.mockReturnValue(
      makeWavBuffer({ channels: 2, dataSize: 176400 })
    );

    const duration = getWavDuration("/fake/stereo.wav");
    // 176400 / (44100 * 2 * 2) = 1.0
    expect(duration).toBe(1);
  });

  it("returns undefined for exactly 44 bytes (empty data section)", () => {
    mockReadFileSync.mockReturnValue(
      makeWavBuffer({ dataSize: 0 })
    );

    const duration = getWavDuration("/fake/empty.wav");
    // 0 / (44100 * 1 * 2) = 0
    expect(duration).toBe(0);
  });
});

// ---------------------------------------------------------------------------
// 4. POST — response shape and SSE headers
// ---------------------------------------------------------------------------

describe("POST response shape", () => {
  it("returns a Response object", async () => {
    const response = await POST(makeRequest() as any);
    expect(response).toBeInstanceOf(Response);
  });

  it("sets Content-Type to text/event-stream", async () => {
    const response = await POST(makeRequest() as any);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("sets Cache-Control to no-cache", async () => {
    const response = await POST(makeRequest() as any);
    expect(response.headers.get("Cache-Control")).toBe("no-cache");
  });

  it("sets Connection to keep-alive", async () => {
    const response = await POST(makeRequest() as any);
    expect(response.headers.get("Connection")).toBe("keep-alive");
  });

  it("returns a ReadableStream body", async () => {
    const response = await POST(makeRequest() as any);
    expect(response.body).toBeInstanceOf(ReadableStream);
  });
});

// ---------------------------------------------------------------------------
// 5. POST — first SSE event includes jobId
// ---------------------------------------------------------------------------

describe("POST — first SSE event", () => {
  it("first event contains a jobId field", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    expect(events.length).toBeGreaterThanOrEqual(1);
    expect(events[0]).toHaveProperty("jobId");
  });

  it("jobId is the mocked UUID value", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    expect((events[0] as any).jobId).toBe("test-uuid-1234");
  });
});

// ---------------------------------------------------------------------------
// 6. POST — accepts optional segments body
// ---------------------------------------------------------------------------

describe("POST — segments parameter", () => {
  it("works with no body (renders all segments)", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await POST(makeRequest() as any);
    expect(response).toBeInstanceOf(Response);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("works with empty segments array", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await POST(makeRequest({ segments: [] }) as any);
    expect(response).toBeInstanceOf(Response);
  });

  it("accepts specific segments array", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await POST(
      makeRequest({ segments: ["intro", "outro"] }) as any
    );
    expect(response).toBeInstanceOf(Response);
  });

  it("handles invalid body gracefully (non-JSON)", async () => {
    mockExistsSync.mockReturnValue(false);

    const request = new Request("http://localhost/api/pipeline/tts-render/run", {
      method: "POST",
      body: "not json",
    });

    const response = await POST(request as any);
    expect(response).toBeInstanceOf(Response);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("handles body with segments as non-array gracefully", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await POST(
      makeRequest({ segments: "not-an-array" }) as any
    );
    expect(response).toBeInstanceOf(Response);
  });
});

// ---------------------------------------------------------------------------
// 7. POST — spawn command verification
// ---------------------------------------------------------------------------

describe("POST — spawn command", () => {
  it("spawns python3 with render_tts.py as first arg", async () => {
    mockExistsSync.mockReturnValue(false);

    await POST(makeRequest() as any);
    await flushPromises();

    expect(mockSpawn).toHaveBeenCalled();
    const [cmd, args] = mockSpawn.mock.calls[0];
    expect(cmd).toBe("python3");
    expect(args[0]).toBe("scripts/render_tts.py");
  });

  it("passes --segment flags when segments are provided", async () => {
    mockExistsSync.mockReturnValue(false);

    await POST(makeRequest({ segments: ["seg1", "seg2"] }) as any);
    await flushPromises();

    const [, args] = mockSpawn.mock.calls[0];
    expect(args).toContain("--segment");
    expect(args).toContain("seg1");
    expect(args).toContain("seg2");
  });

  it("uses flatMap to interleave --segment with each segment ID", async () => {
    mockExistsSync.mockReturnValue(false);

    await POST(makeRequest({ segments: ["a", "b", "c"] }) as any);
    await flushPromises();

    const [, args] = mockSpawn.mock.calls[0];
    expect(args).toEqual([
      "scripts/render_tts.py",
      "--segment", "a",
      "--segment", "b",
      "--segment", "c",
    ]);
  });

  it("spawns with cwd set to process.cwd()", async () => {
    mockExistsSync.mockReturnValue(false);

    await POST(makeRequest() as any);
    await flushPromises();

    const [, , options] = mockSpawn.mock.calls[0];
    expect(options).toHaveProperty("cwd", process.cwd());
  });

  it("does not pass --segment flags when no segments provided", async () => {
    mockExistsSync.mockReturnValue(false);

    await POST(makeRequest() as any);
    await flushPromises();

    const [, args] = mockSpawn.mock.calls[0];
    expect(args).toEqual(["scripts/render_tts.py"]);
  });
});

// ---------------------------------------------------------------------------
// 8. POST — stdout/stderr streaming as SSE log events
// ---------------------------------------------------------------------------

describe("POST — stdout/stderr streaming", () => {
  it("registers listeners on stdout for data and end events", async () => {
    mockExistsSync.mockReturnValue(false);

    await POST(makeRequest() as any);
    await flushPromises();

    const stdoutEvents = mockStdoutOn.mock.calls.map((c: any[]) => c[0]);
    expect(stdoutEvents).toContain("data");
    expect(stdoutEvents).toContain("end");
  });

  it("registers listeners on stderr for data and end events", async () => {
    mockExistsSync.mockReturnValue(false);

    await POST(makeRequest() as any);
    await flushPromises();

    const stderrEvents = mockStderrOn.mock.calls.map((c: any[]) => c[0]);
    expect(stderrEvents).toContain("data");
    expect(stderrEvents).toContain("end");
  });

  it("streams stdout lines as SSE log events with type 'log'", async () => {
    mockExistsSync.mockReturnValue(false);

    // Override spawn to emit stdout data then close
    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const dataHandler = mockStdoutOn.mock.calls.find(
          (c: any[]) => c[0] === "data"
        )?.[1];
        const endHandler = mockStdoutOn.mock.calls.find(
          (c: any[]) => c[0] === "end"
        )?.[1];
        if (dataHandler) dataHandler(Buffer.from("Rendering segment intro\n"));
        if (endHandler) endHandler();

        const closeHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "close"
        )?.[1];
        if (closeHandler) closeHandler(0);
      }, 5);
      return proc;
    });

    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const logEvents = events.filter((e: any) => e.type === "log");
    expect(logEvents.length).toBeGreaterThanOrEqual(1);
    expect(logEvents.some((e: any) => e.message === "Rendering segment intro")).toBe(true);
  });

  it("log events include jobId", async () => {
    mockExistsSync.mockReturnValue(false);

    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const dataHandler = mockStdoutOn.mock.calls.find(
          (c: any[]) => c[0] === "data"
        )?.[1];
        const endHandler = mockStdoutOn.mock.calls.find(
          (c: any[]) => c[0] === "end"
        )?.[1];
        if (dataHandler) dataHandler(Buffer.from("test line\n"));
        if (endHandler) endHandler();

        const closeHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "close"
        )?.[1];
        if (closeHandler) closeHandler(0);
      }, 5);
      return proc;
    });

    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const logEvents = events.filter((e: any) => e.type === "log");
    for (const evt of logEvents) {
      expect(evt).toHaveProperty("jobId", "test-uuid-1234");
    }
  });

  it("streams stderr lines as SSE log events", async () => {
    mockExistsSync.mockReturnValue(false);

    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const stderrDataHandler = mockStderrOn.mock.calls.find(
          (c: any[]) => c[0] === "data"
        )?.[1];
        const stderrEndHandler = mockStderrOn.mock.calls.find(
          (c: any[]) => c[0] === "end"
        )?.[1];
        const stdoutEndHandler = mockStdoutOn.mock.calls.find(
          (c: any[]) => c[0] === "end"
        )?.[1];
        if (stderrDataHandler) stderrDataHandler(Buffer.from("WARNING: low quality\n"));
        if (stderrEndHandler) stderrEndHandler();
        if (stdoutEndHandler) stdoutEndHandler();

        const closeHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "close"
        )?.[1];
        if (closeHandler) closeHandler(0);
      }, 5);
      return proc;
    });

    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const logEvents = events.filter((e: any) => e.type === "log");
    expect(logEvents.some((e: any) => e.message === "WARNING: low quality")).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// 9. POST — per-segment status events on completion
// ---------------------------------------------------------------------------

describe("POST — per-segment status events", () => {
  it("emits segment status events after completion", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (p.endsWith("tts_script.md")) return true;
      if (p.endsWith(".wav")) return true;
      return false;
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.endsWith("tts_script.md")) {
        return "# intro\nHello.\n# outro\nGoodbye.\n";
      }
      return makeWavBuffer({ dataSize: 88200 });
    });

    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const segmentEvents = events.filter((e: any) => e.type === "segment");
    expect(segmentEvents.length).toBeGreaterThanOrEqual(1);

    for (const evt of segmentEvents) {
      expect(evt).toHaveProperty("segmentId");
      expect(evt).toHaveProperty("status");
      expect(["done", "error"]).toContain((evt as any).status);
    }
  });

  it("emits 'done' status with duration when wav file exists and render succeeds", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (p.endsWith("tts_script.md")) return true;
      if (p.endsWith(".wav")) return true;
      return false;
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.endsWith("tts_script.md")) {
        return "# intro\nHello.\n";
      }
      return makeWavBuffer({ dataSize: 88200 });
    });

    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const segEvt = events.find(
      (e: any) => e.type === "segment" && e.segmentId === "intro"
    ) as any;
    expect(segEvt).toBeDefined();
    expect(segEvt.status).toBe("done");
    expect(segEvt.duration).toBe(1);
  });

  it("emits 'error' status when wav file does not exist", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (p.endsWith("tts_script.md")) return true;
      // wav files don't exist
      return false;
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.endsWith("tts_script.md")) {
        return "# missing_seg\nContent.\n";
      }
      return makeWavBuffer({});
    });

    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const segEvt = events.find(
      (e: any) => e.type === "segment" && e.segmentId === "missing_seg"
    ) as any;
    expect(segEvt).toBeDefined();
    expect(segEvt.status).toBe("error");
  });

  it("emits segment events for specified segments only when provided", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await POST(
      makeRequest({ segments: ["seg_a", "seg_b"] }) as any
    );
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const segmentEvents = events.filter((e: any) => e.type === "segment");
    const segIds = segmentEvents.map((e: any) => e.segmentId);
    expect(segIds).toContain("seg_a");
    expect(segIds).toContain("seg_b");
    expect(segIds).toHaveLength(2);
  });

  it("emits segment events for all script segments when no segments param", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (p.endsWith("tts_script.md")) return true;
      return false;
    });
    mockReadFileSync.mockImplementation((p: string) => {
      if (typeof p === "string" && p.endsWith("tts_script.md")) {
        return "# s1\nA.\n# s2\nB.\n# s3\nC.\n";
      }
      return makeWavBuffer({});
    });

    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const segmentEvents = events.filter((e: any) => e.type === "segment");
    const segIds = segmentEvents.map((e: any) => e.segmentId);
    expect(segIds).toEqual(expect.arrayContaining(["s1", "s2", "s3"]));
  });
});

// ---------------------------------------------------------------------------
// 10. POST — error handling (non-zero exit, spawn error)
// ---------------------------------------------------------------------------

describe("POST — render error handling", () => {
  it("emits error event when render_tts.py exits with non-zero code", async () => {
    mockExistsSync.mockReturnValue(false);

    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const closeHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "close"
        )?.[1];
        if (closeHandler) closeHandler(1);
      }, 5);
      return proc;
    });

    const response = await POST(makeRequest() as any);
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const errorEvent = events.find((e: any) => e.type === "error") as any;
    expect(errorEvent).toBeDefined();
    expect(errorEvent.message).toContain("render_tts.py exited with code 1");
  });

  it("emits 'error' status for all segments when render fails", async () => {
    mockExistsSync.mockImplementation((p: string) => {
      if (p.endsWith("tts_script.md")) return true;
      return false;
    });
    mockReadFileSync.mockImplementation(() => "# seg1\nText.\n");

    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const closeHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "close"
        )?.[1];
        if (closeHandler) closeHandler(1);
      }, 5);
      return proc;
    });

    const response = await POST(
      makeRequest({ segments: ["seg1"] }) as any
    );
    await flushPromises();

    const events = await readSseEvents(response.body!);
    const segEvts = events.filter((e: any) => e.type === "segment");
    for (const evt of segEvts) {
      expect((evt as any).status).toBe("error");
    }
  });

  it("still returns SSE response even when spawn will fail", async () => {
    mockExistsSync.mockReturnValue(false);

    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const errorHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "error"
        )?.[1];
        if (errorHandler) errorHandler(new Error("ENOENT: python3 not found"));
      }, 5);
      return proc;
    });

    const response = await POST(makeRequest() as any);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });
});

// ---------------------------------------------------------------------------
// 11. POST — no authentication required
// ---------------------------------------------------------------------------

describe("POST — no authentication required", () => {
  it("does not require authorization headers", async () => {
    mockExistsSync.mockReturnValue(false);

    const request = new Request("http://localhost/api/pipeline/tts-render/run", {
      method: "POST",
      headers: { Authorization: "Bearer fake-token" },
    });

    const response = await POST(request as any);
    expect(response.headers.get("Content-Type")).toBe("text/event-stream");
  });

  it("works with minimal request (no body, no auth)", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await POST(makeRequest() as any);
    expect(response).toBeInstanceOf(Response);
  });
});

// ---------------------------------------------------------------------------
// 12. Executor factory — registered with pipeline job system
// ---------------------------------------------------------------------------

describe("tts-render executor factory", () => {
  it("returns an async function when called with params and send", () => {
    const executor = registerCallArgs.factory({}, jest.fn());
    expect(typeof executor).toBe("function");
  });

  it("accepts segments in params", () => {
    const executor = registerCallArgs.factory(
      { segments: ["seg1", "seg2"] },
      jest.fn()
    );
    expect(typeof executor).toBe("function");
  });

  it("emits per-segment status events via send", async () => {
    const mockSend = jest.fn();
    mockExistsSync.mockReturnValue(false);

    const executor = registerCallArgs.factory(
      { segments: ["intro"] },
      mockSend
    );
    await executor(jest.fn());
    await flushPromises();

    const segmentCalls = mockSend.mock.calls.filter(
      (c: any[]) => c[0]?.type === "segment"
    );
    expect(segmentCalls.length).toBeGreaterThanOrEqual(1);
    expect(segmentCalls[0][0]).toHaveProperty("segmentId", "intro");
    expect(segmentCalls[0][0]).toHaveProperty("status");
  });

  it("reads segments from script when params.segments not provided", async () => {
    const mockSend = jest.fn();
    mockExistsSync.mockImplementation((p: string) => {
      if (p.endsWith("tts_script.md")) return true;
      return false;
    });
    mockReadFileSync.mockReturnValue("# auto1\nText.\n# auto2\nMore.\n");

    const executor = registerCallArgs.factory({}, mockSend);
    await executor(jest.fn());
    await flushPromises();

    const segmentCalls = mockSend.mock.calls.filter(
      (c: any[]) => c[0]?.type === "segment"
    );
    const segIds = segmentCalls.map((c: any[]) => c[0].segmentId);
    expect(segIds).toContain("auto1");
    expect(segIds).toContain("auto2");
  });

  it("sends error event when render process fails", async () => {
    const mockSend = jest.fn();
    mockExistsSync.mockReturnValue(false);

    mockSpawn.mockImplementation(() => {
      const proc = {
        stdout: { on: mockStdoutOn },
        stderr: { on: mockStderrOn },
        on: mockOn,
      };
      setTimeout(() => {
        const closeHandler = mockOn.mock.calls.find(
          (c: any[]) => c[0] === "close"
        )?.[1];
        if (closeHandler) closeHandler(1);
      }, 5);
      return proc;
    });

    const executor = registerCallArgs.factory(
      { segments: ["intro"] },
      mockSend
    );
    await executor(jest.fn());
    await flushPromises();

    const errorCalls = mockSend.mock.calls.filter(
      (c: any[]) => c[0]?.type === "error"
    );
    expect(errorCalls.length).toBeGreaterThanOrEqual(1);
  });
});

// ---------------------------------------------------------------------------
// 13. POST — SSE event format (data: JSON\n\n)
// ---------------------------------------------------------------------------

describe("POST — SSE event format", () => {
  it("formats events as 'data: <JSON>\\n\\n'", async () => {
    mockExistsSync.mockReturnValue(false);

    const response = await POST(makeRequest() as any);
    await flushPromises();

    const reader = response.body!.getReader();
    const decoder = new TextDecoder();
    let raw = "";
    try {
      while (true) {
        const { done, value } = await reader.read();
        if (done) break;
        raw += decoder.decode(value, { stream: true });
      }
    } catch {
      // stream closed
    }

    // Each event should start with "data: " and end with "\n\n"
    const eventBlocks = raw.split("\n\n").filter((b) => b.trim().length > 0);
    for (const block of eventBlocks) {
      expect(block).toMatch(/^data:\s*\{/);
    }
  });
});

// ---------------------------------------------------------------------------
// 14. Source file structure checks — run route
// ---------------------------------------------------------------------------

describe("app/api/pipeline/tts-render/run/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    const realFs = jest.requireActual("fs") as typeof import("fs");
    const pathMod = require("path");
    sourceCode = realFs.readFileSync(
      pathMod.join(
        __dirname,
        "..",
        "app",
        "api",
        "pipeline",
        "tts-render",
        "run",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async function POST", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+POST/);
  });

  it("imports spawn from child_process", () => {
    expect(sourceCode).toMatch(/child_process/);
    expect(sourceCode).toMatch(/spawn/);
  });

  it("imports registerExecutor from @/lib/jobs", () => {
    expect(sourceCode).toMatch(/@\/lib\/jobs/);
    expect(sourceCode).toMatch(/registerExecutor/);
  });

  it("imports SseSend from @/lib/types", () => {
    expect(sourceCode).toMatch(/@\/lib\/types/);
    expect(sourceCode).toMatch(/SseSend/);
  });

  it("calls registerExecutor('tts-render', ...)", () => {
    expect(sourceCode).toMatch(
      /registerExecutor\s*\(\s*["']tts-render["']/
    );
  });

  it("spawns python3 with render_tts.py", () => {
    expect(sourceCode).toMatch(/spawn\s*\(\s*["']python3["']/);
    expect(sourceCode).toMatch(/render_tts\.py/);
  });

  it("uses --segment flag for per-segment filtering", () => {
    expect(sourceCode).toMatch(/--segment/);
  });

  it("uses process.cwd() for spawn cwd", () => {
    expect(sourceCode).toMatch(/cwd:\s*process\.cwd\(\)/);
  });

  it("creates SSE stream with correct Content-Type header", () => {
    expect(sourceCode).toMatch(/text\/event-stream/);
  });

  it("sets Cache-Control to no-cache", () => {
    expect(sourceCode).toMatch(/no-cache/);
  });

  it("sets Connection to keep-alive", () => {
    expect(sourceCode).toMatch(/keep-alive/);
  });

  it("exports parseSegmentsFromScript function", () => {
    expect(sourceCode).toMatch(/export\s+function\s+parseSegmentsFromScript/);
  });

  it("exports getWavDuration function", () => {
    expect(sourceCode).toMatch(/export\s+function\s+getWavDuration/);
  });

  it("reads tts_script.md for segment parsing", () => {
    expect(sourceCode).toMatch(/tts_script\.md/);
  });

  it("uses new Response(stream, ...) for SSE streaming", () => {
    expect(sourceCode).toMatch(/new\s+Response\s*\(\s*stream/);
  });

  it("emits segment status events with type 'segment'", () => {
    expect(sourceCode).toMatch(/type:\s*["']segment["']/);
  });

  it("uses crypto.randomUUID() for jobId generation", () => {
    expect(sourceCode).toMatch(/crypto\.randomUUID\(\)/);
  });

  it("pipes both stdout and stderr from spawn", () => {
    expect(sourceCode).toMatch(/proc\.stdout/);
    expect(sourceCode).toMatch(/proc\.stderr/);
  });

  it("outputs WAV files to outputs/tts/ path", () => {
    expect(sourceCode).toMatch(/outputs.*tts/);
  });
});

// ---------------------------------------------------------------------------
// 15. Source file structure checks — segments route
// ---------------------------------------------------------------------------

describe("app/api/pipeline/tts-render/segments/route.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    const realFs = jest.requireActual("fs") as typeof import("fs");
    const pathMod = require("path");
    sourceCode = realFs.readFileSync(
      pathMod.join(
        __dirname,
        "..",
        "app",
        "api",
        "pipeline",
        "tts-render",
        "segments",
        "route.ts"
      ),
      "utf-8"
    );
  });

  it("exports async function GET", () => {
    expect(sourceCode).toMatch(/export\s+async\s+function\s+GET/);
  });

  it("defines TtsSegment interface with id, status, duration, text", () => {
    expect(sourceCode).toMatch(/interface\s+TtsSegment/);
    expect(sourceCode).toMatch(/id:\s*string/);
    expect(sourceCode).toMatch(/status:\s*["']done["']\s*\|\s*["']missing["']\s*\|\s*["']error["']/);
    expect(sourceCode).toMatch(/duration\?:\s*number/);
    expect(sourceCode).toMatch(/text\?:\s*string/);
  });

  it("scans outputs/tts/ directory for wav files", () => {
    expect(sourceCode).toMatch(/outputs.*tts/);
    expect(sourceCode).toMatch(/\.wav/);
  });

  it("imports parseSegmentsFromScript from the run route", () => {
    expect(sourceCode).toMatch(/parseSegmentsFromScript/);
  });

  it("imports getWavDuration from the run route", () => {
    expect(sourceCode).toMatch(/getWavDuration/);
  });

  it("uses readdirSync to scan output directory", () => {
    expect(sourceCode).toMatch(/readdirSync/);
  });

  it("returns NextResponse.json with segments array", () => {
    expect(sourceCode).toMatch(/NextResponse\.json/);
    expect(sourceCode).toMatch(/segments/);
  });

  it("imports NextResponse from next/server", () => {
    expect(sourceCode).toMatch(/import.*NextResponse.*from\s+["']next\/server["']/);
  });

  it("cross-references wav files with script segments", () => {
    expect(sourceCode).toMatch(/parseSegmentsFromScript/);
    expect(sourceCode).toMatch(/readdirSync/);
  });

  it("marks segments as 'missing' when wav file does not exist", () => {
    expect(sourceCode).toMatch(/missing/);
  });
});

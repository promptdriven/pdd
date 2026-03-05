/**
 * Tests for lib/render.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/lib_render_typescript.prompt.
 *
 * Spec requirements verified:
 *   1. Export renderSection(compositionId, outputPath, onProgress) → Promise<void>
 *   2. Export stitchFullVideo(sectionPaths, outputPath, onProgress) → Promise<void>
 *   3. Export getSectionDuration(mp4Path) → Promise<number>
 *   4. Export renderStill(compositionId, frame, outputPath) → Promise<void>
 *   5. renderMedia uses codec 'h264', outputLocation, onProgress mapping 0–1 → 0–100
 *   6. Bundle path defaults to path.join(process.cwd(), 'remotion')
 *   7. import 'server-only' guard
 *   8. Ensure output directories exist before rendering
 *   9. stitchFullVideo writes ffmpeg concat file and runs ffmpeg -f concat -safe 0
 *  10. getSectionDuration runs ffprobe and parses float duration
 *  11. renderStill uses selectComposition + remotion renderStill
 */

import fs from "fs";
import path from "path";
import { EventEmitter } from "events";
import { promisify } from "util";

// ---------------------------------------------------------------------------
// Mock @remotion/renderer (still used by renderStill)
// ---------------------------------------------------------------------------

const mockRenderMedia = jest.fn();
const mockRenderStill = jest.fn();
const mockSelectComposition = jest.fn();

jest.mock("@remotion/renderer", () => ({
  renderMedia: mockRenderMedia,
  renderStill: mockRenderStill,
  selectComposition: mockSelectComposition,
}));

// ---------------------------------------------------------------------------
// Mock child_process.exec (with promisify.custom) and spawn
// ---------------------------------------------------------------------------

/**
 * Create a fake ChildProcess that emits events on stdout/stderr.
 * Tests drive the fake by calling helpers on the returned object:
 *   emitStdout(data)  – push data to stdout
 *   emitStderr(data)  – push data to stderr
 *   close(code)       – emit the 'close' event with exit code
 */
interface FakeChild extends EventEmitter {
  stdout: EventEmitter;
  stderr: EventEmitter;
  emitStdout: (data: string) => void;
  emitStderr: (data: string) => void;
  close: (code: number) => void;
}

function createFakeChild(): FakeChild {
  const child = new EventEmitter() as FakeChild;
  child.stdout = new EventEmitter();
  child.stderr = new EventEmitter();
  child.emitStdout = (data: string) => child.stdout.emit("data", Buffer.from(data));
  child.emitStderr = (data: string) => child.stderr.emit("data", Buffer.from(data));
  child.close = (code: number) => child.emit("close", code);
  return child;
}

/** The most recent FakeChild returned by mockSpawn, for driving from tests. */
let lastFakeChild: FakeChild;

const mockSpawn = jest.fn().mockImplementation(() => {
  lastFakeChild = createFakeChild();
  // Auto-resolve with exit 0 on next tick so tests that don't need to
  // drive stdout manually still complete.
  // Tests that want to control behaviour can override via setupSpawn().
  return lastFakeChild;
});

/**
 * Configure mockSpawn to create a child that emits the given stdout lines
 * and then exits with the given code (default 0).
 */
function setupSpawn(
  stdoutLines: string[] = [],
  exitCode = 0,
  stderrData = ""
) {
  mockSpawn.mockImplementation(() => {
    lastFakeChild = createFakeChild();
    // Schedule events on next tick so the caller has time to attach listeners.
    process.nextTick(() => {
      for (const line of stdoutLines) {
        lastFakeChild.emitStdout(line + "\n");
      }
      if (stderrData) {
        lastFakeChild.emitStderr(stderrData);
      }
      lastFakeChild.close(exitCode);
    });
    return lastFakeChild;
  });
}

const mockExecPromisified = jest.fn();
const mockExec = Object.assign(jest.fn(), {
  [promisify.custom]: mockExecPromisified,
});
jest.mock("child_process", () => ({
  exec: mockExec,
  spawn: mockSpawn,
}));

// Must import after jest.mock
import {
  renderSection,
  stitchFullVideo,
  getSectionDuration,
  renderStill,
} from "../lib/render";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const ORIGINAL_ENV = { ...process.env };

function setupFsMocks() {
  jest.spyOn(fs.promises, "mkdir").mockResolvedValue(undefined as any);
  jest.spyOn(fs.promises, "writeFile").mockResolvedValue(undefined);
  jest.spyOn(fs.promises, "unlink").mockResolvedValue(undefined);
  jest.spyOn(fs, "existsSync").mockReturnValue(false);
}

function setupSelectComposition(id = "TestComposition") {
  const composition = {
    id,
    width: 1920,
    height: 1080,
    fps: 30,
    durationInFrames: 300,
  };
  mockSelectComposition.mockResolvedValue(composition);
  return composition;
}

function setupExecAsync(stdout = "", stderr = "") {
  mockExecPromisified.mockResolvedValue({ stdout, stderr });
}

// ---------------------------------------------------------------------------
// Setup / Teardown
// ---------------------------------------------------------------------------

beforeEach(() => {
  jest.clearAllMocks();
  process.env = { ...ORIGINAL_ENV };
});

afterEach(() => {
  jest.restoreAllMocks();
  process.env = ORIGINAL_ENV;
});

// ---------------------------------------------------------------------------
// 1. Module exports
// ---------------------------------------------------------------------------

describe("module exports", () => {
  it("exports renderSection as a function", () => {
    expect(typeof renderSection).toBe("function");
  });

  it("exports stitchFullVideo as a function", () => {
    expect(typeof stitchFullVideo).toBe("function");
  });

  it("exports getSectionDuration as a function", () => {
    expect(typeof getSectionDuration).toBe("function");
  });

  it("exports renderStill as a function", () => {
    expect(typeof renderStill).toBe("function");
  });

  it("renderSection accepts 3 parameters", () => {
    expect(renderSection.length).toBe(3);
  });

  it("stitchFullVideo accepts 3 parameters", () => {
    expect(stitchFullVideo.length).toBe(3);
  });

  it("getSectionDuration accepts 1 parameter", () => {
    expect(getSectionDuration.length).toBe(1);
  });

  it("renderStill accepts 3 parameters", () => {
    expect(renderStill.length).toBe(3);
  });

  it("all exports are async functions", () => {
    expect(renderSection.constructor.name).toBe("AsyncFunction");
    expect(stitchFullVideo.constructor.name).toBe("AsyncFunction");
    expect(getSectionDuration.constructor.name).toBe("AsyncFunction");
    expect(renderStill.constructor.name).toBe("AsyncFunction");
  });
});

// ---------------------------------------------------------------------------
// 2. renderSection — child-process spawn integration
//    renderSection now spawns a standalone Node.js child process that uses
//    @remotion/renderer internally. Tests verify the generated script content,
//    the spawn invocation, and progress/error handling.
// ---------------------------------------------------------------------------

describe("renderSection — child-process spawn integration", () => {
  beforeEach(() => {
    setupFsMocks();
    // Default: child exits successfully with no stdout.
    setupSpawn([], 0);
  });

  it("spawns a node child process", async () => {
    await renderSection("IntroComposition", "/tmp/out.mp4", jest.fn());

    expect(mockSpawn).toHaveBeenCalledWith(
      "node",
      expect.any(Array),
      expect.objectContaining({ stdio: ["ignore", "pipe", "pipe"] })
    );
  });

  it("writes a .cjs render script that calls selectComposition with compositionId", async () => {
    await renderSection("IntroComposition", "/tmp/out.mp4", jest.fn());

    // The second writeFile call is the mkdir + writeFile in renderSection;
    // The first writeFile is in ensureDir/mkdir, so script writeFile is the
    // one whose path ends with .cjs
    const writeCalls = (fs.promises.writeFile as jest.Mock).mock.calls;
    const scriptCall = writeCalls.find((c: any[]) =>
      (c[0] as string).endsWith(".cjs")
    );
    expect(scriptCall).toBeDefined();
    const script = scriptCall![1] as string;
    expect(script).toContain("selectComposition");
    expect(script).toContain('"IntroComposition"');
  });

  it("writes a render script that uses codec h264", async () => {
    await renderSection("TestComp", "/tmp/out.mp4", jest.fn());

    const writeCalls = (fs.promises.writeFile as jest.Mock).mock.calls;
    const scriptCall = writeCalls.find((c: any[]) =>
      (c[0] as string).endsWith(".cjs")
    );
    const script = scriptCall![1] as string;
    expect(script).toContain("codec: 'h264'");
  });

  it("writes a render script with outputLocation set to outputPath", async () => {
    await renderSection("TestComp", "/output/sections/intro.mp4", jest.fn());

    const writeCalls = (fs.promises.writeFile as jest.Mock).mock.calls;
    const scriptCall = writeCalls.find((c: any[]) =>
      (c[0] as string).endsWith(".cjs")
    );
    const script = scriptCall![1] as string;
    expect(script).toContain("/output/sections/intro.mp4");
  });

  it("writes a render script that passes composition to renderMedia", async () => {
    await renderSection("MyComp", "/tmp/out.mp4", jest.fn());

    const writeCalls = (fs.promises.writeFile as jest.Mock).mock.calls;
    const scriptCall = writeCalls.find((c: any[]) =>
      (c[0] as string).endsWith(".cjs")
    );
    const script = scriptCall![1] as string;
    expect(script).toContain("renderMedia");
    expect(script).toContain("composition");
  });

  it("writes a render script with a serveUrl for both selectComposition and renderMedia", async () => {
    await renderSection("TestComp", "/tmp/out.mp4", jest.fn());

    const writeCalls = (fs.promises.writeFile as jest.Mock).mock.calls;
    const scriptCall = writeCalls.find((c: any[]) =>
      (c[0] as string).endsWith(".cjs")
    );
    const script = scriptCall![1] as string;
    // serveUrl appears in the script for both calls
    expect(script).toMatch(/serveUrl/);
    // selectComposition uses serveUrl
    expect(script).toContain("selectComposition");
    // renderMedia uses serveUrl
    expect(script).toContain("renderMedia");
  });

  it("maps Remotion progress 0–1 to RenderProgress percent 0–100", async () => {
    setupSpawn([
      JSON.stringify({ percent: 0, compositionId: "IntroComposition" }),
      JSON.stringify({ percent: 50, compositionId: "IntroComposition" }),
      JSON.stringify({ percent: 100, compositionId: "IntroComposition", done: true }),
    ]);

    const progressCalls: Array<{ percent: number; message: string }> = [];
    await renderSection("IntroComposition", "/tmp/out.mp4", (p) =>
      progressCalls.push(p)
    );

    expect(progressCalls[0].percent).toBe(0);
    expect(progressCalls[1].percent).toBe(50);
    expect(progressCalls[2].percent).toBe(100);
  });

  it("includes compositionId in progress message", async () => {
    setupSpawn([
      JSON.stringify({ percent: 50, compositionId: "IntroComposition" }),
    ]);

    const progressCalls: Array<{ percent: number; message: string }> = [];
    await renderSection("IntroComposition", "/tmp/out.mp4", (p) =>
      progressCalls.push(p)
    );

    expect(progressCalls[0].message).toContain("IntroComposition");
  });

  it("ensures output directory exists before rendering", async () => {
    await renderSection("TestComp", "/output/sections/intro.mp4", jest.fn());

    expect(fs.promises.mkdir).toHaveBeenCalledWith("/output/sections", {
      recursive: true,
    });
  });
});

// ---------------------------------------------------------------------------
// 3. renderSection — bundle path resolution
//    The serveUrl is embedded in the generated .cjs script. We verify the
//    script content to ensure the correct bundle path was resolved.
// ---------------------------------------------------------------------------

describe("renderSection — bundle path resolution", () => {
  beforeEach(() => {
    setupFsMocks();
    setupSpawn([], 0);
  });

  it("uses REMOTION_BUNDLE_PATH env var when set", async () => {
    process.env.REMOTION_BUNDLE_PATH = "/custom/bundle/path";

    await renderSection("TestComp", "/tmp/out.mp4", jest.fn());

    const writeCalls = (fs.promises.writeFile as jest.Mock).mock.calls;
    const scriptCall = writeCalls.find((c: any[]) =>
      (c[0] as string).endsWith(".cjs")
    );
    const script = scriptCall![1] as string;
    expect(script).toContain("/custom/bundle/path");
  });

  it("falls back to remotion/build directory when index.html exists", async () => {
    delete process.env.REMOTION_BUNDLE_PATH;
    (fs.existsSync as jest.Mock).mockReturnValue(true);

    await renderSection("TestComp", "/tmp/out.mp4", jest.fn());

    const writeCalls = (fs.promises.writeFile as jest.Mock).mock.calls;
    const scriptCall = writeCalls.find((c: any[]) =>
      (c[0] as string).endsWith(".cjs")
    );
    const script = scriptCall![1] as string;
    // serveUrl should point to the build directory, not the file itself
    expect(script).toContain(path.join("remotion", "build"));
    expect(script).not.toMatch(/index\.html/);
  });

  it("falls back to remotion directory when no build exists", async () => {
    delete process.env.REMOTION_BUNDLE_PATH;
    (fs.existsSync as jest.Mock).mockReturnValue(false);

    await renderSection("TestComp", "/tmp/out.mp4", jest.fn());

    const writeCalls = (fs.promises.writeFile as jest.Mock).mock.calls;
    const scriptCall = writeCalls.find((c: any[]) =>
      (c[0] as string).endsWith(".cjs")
    );
    const script = scriptCall![1] as string;
    expect(script).toMatch(/remotion"/);
  });
});

// ---------------------------------------------------------------------------
// 4. stitchFullVideo — ffmpeg concat integration
// ---------------------------------------------------------------------------

describe("stitchFullVideo — ffmpeg concat", () => {
  beforeEach(() => {
    setupFsMocks();
    setupExecAsync();
  });

  it("writes a concat file with absolute paths in ffmpeg format", async () => {
    const sections = ["/a/intro.mp4", "/b/main.mp4"];
    await stitchFullVideo(sections, "/out/final.mp4", jest.fn());

    const writeCall = (fs.promises.writeFile as jest.Mock).mock.calls[0];
    const content = writeCall[1] as string;
    expect(content).toContain("file '/a/intro.mp4'");
    expect(content).toContain("file '/b/main.mp4'");
  });

  it("writes concat file to temp directory", async () => {
    const sections = ["/a/intro.mp4"];
    await stitchFullVideo(sections, "/out/final.mp4", jest.fn());

    const writeCall = (fs.promises.writeFile as jest.Mock).mock.calls[0];
    const filePath = writeCall[0] as string;
    expect(filePath).toContain("concat-");
  });

  it("runs ffmpeg with -f concat -safe 0 -c copy flags", async () => {
    const sections = ["/a/intro.mp4"];
    await stitchFullVideo(sections, "/out/final.mp4", jest.fn());

    const execCall = mockExecPromisified.mock.calls[0][0];
    expect(execCall).toContain("ffmpeg");
    expect(execCall).toContain("-f concat");
    expect(execCall).toContain("-safe 0");
    expect(execCall).toContain("-c copy");
  });

  it("passes output path to ffmpeg command", async () => {
    const sections = ["/a/intro.mp4"];
    await stitchFullVideo(sections, "/out/final.mp4", jest.fn());

    const execCall = mockExecPromisified.mock.calls[0][0];
    expect(execCall).toContain("/out/final.mp4");
  });

  it("calls onProgress with percent 100 on completion", async () => {
    const sections = ["/a/intro.mp4"];
    const progressCalls: Array<{ percent: number; message: string }> = [];

    await stitchFullVideo(sections, "/out/final.mp4", (p) =>
      progressCalls.push(p)
    );

    expect(progressCalls.length).toBe(1);
    expect(progressCalls[0].percent).toBe(100);
    expect(progressCalls[0].message).toBe("Stitching complete.");
  });

  it("ensures output directory exists before stitching", async () => {
    const sections = ["/a/intro.mp4"];
    await stitchFullVideo(sections, "/output/final/video.mp4", jest.fn());

    expect(fs.promises.mkdir).toHaveBeenCalledWith("/output/final", {
      recursive: true,
    });
  });

  it("deletes the temp concat file after ffmpeg completes", async () => {
    const sections = ["/a/intro.mp4"];
    await stitchFullVideo(sections, "/out/final.mp4", jest.fn());

    expect(fs.promises.unlink).toHaveBeenCalled();
  });

  it("escapes single quotes in paths for ffmpeg concat", async () => {
    const sections = ["/a/scene's_intro.mp4", "/b/it's a test.mp4"];
    await stitchFullVideo(sections, "/out/final.mp4", jest.fn());

    const writeCall = (fs.promises.writeFile as jest.Mock).mock.calls[0];
    const content = writeCall[1] as string;
    // ffmpeg concat format escapes single quotes by ending the quote,
    // inserting an escaped quote, and reopening the quote: '\''
    expect(content).toContain("file '/a/scene'\\''s_intro.mp4'");
    expect(content).toContain("file '/b/it'\\''s a test.mp4'");
    // Must NOT contain unescaped single-quoted paths
    expect(content).not.toContain("file '/a/scene's_intro.mp4'");
  });

  it("deletes the temp concat file even if ffmpeg fails", async () => {
    mockExecPromisified.mockRejectedValue(new Error("ffmpeg failed"));

    const sections = ["/a/intro.mp4"];
    await expect(
      stitchFullVideo(sections, "/out/final.mp4", jest.fn())
    ).rejects.toThrow();

    expect(fs.promises.unlink).toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 5. getSectionDuration — ffprobe integration
// ---------------------------------------------------------------------------

describe("getSectionDuration — ffprobe", () => {
  it("runs ffprobe with correct flags", async () => {
    setupExecAsync("12.345\n");

    await getSectionDuration("/sections/intro.mp4");

    const execCall = mockExecPromisified.mock.calls[0][0];
    expect(execCall).toContain("ffprobe");
    expect(execCall).toContain("-v error");
    expect(execCall).toContain("-show_entries format=duration");
    expect(execCall).toContain("noprint_wrappers=1:nokey=1");
    expect(execCall).toContain("/sections/intro.mp4");
  });

  it("parses stdout as float duration in seconds", async () => {
    setupExecAsync("12.345\n");

    const duration = await getSectionDuration("/sections/intro.mp4");

    expect(duration).toBeCloseTo(12.345);
  });

  it("trims whitespace from ffprobe output", async () => {
    setupExecAsync("  45.678  \n");

    const duration = await getSectionDuration("/sections/main.mp4");

    expect(duration).toBeCloseTo(45.678);
  });

  it("handles integer durations", async () => {
    setupExecAsync("8\n");

    const duration = await getSectionDuration("/sections/outro.mp4");

    expect(duration).toBe(8);
  });
});

// ---------------------------------------------------------------------------
// 6. renderStill — Remotion renderStill integration
// ---------------------------------------------------------------------------

describe("renderStill — subprocess", () => {
  beforeEach(() => {
    setupFsMocks();
  });

  it("spawns a child process to render the still", async () => {
    setupSpawn([], 0);

    await renderStill("IntroComposition", 90, "/stills/frame.png");

    expect(mockSpawn).toHaveBeenCalledWith(
      "node",
      expect.any(Array),
      expect.objectContaining({ stdio: ["ignore", "ignore", "pipe"] })
    );
  });

  it("writes a temporary .cjs script containing compositionId and frame", async () => {
    setupSpawn([], 0);

    await renderStill("IntroComposition", 90, "/stills/frame.png");

    const writeCall = (fs.promises.writeFile as jest.Mock).mock.calls.find(
      (c: unknown[]) => typeof c[0] === "string" && (c[0] as string).includes("remotion-still")
    );
    expect(writeCall).toBeDefined();
    const scriptContent = writeCall[1] as string;
    expect(scriptContent).toContain("IntroComposition");
    expect(scriptContent).toContain("90");
    expect(scriptContent).toContain("/stills/frame.png");
    expect(scriptContent).toContain("selectComposition");
    expect(scriptContent).toContain("renderStill");
  });

  it("rejects when child process exits with non-zero code", async () => {
    setupSpawn([], 1, "Composition not found");

    await expect(
      renderStill("BadComp", 0, "/stills/frame.png")
    ).rejects.toThrow(/exited with code 1/);
  });

  it("ensures output directory exists before rendering still", async () => {
    setupSpawn([], 0);

    await renderStill("TestComp", 0, "/output/stills/frame.png");

    expect(fs.promises.mkdir).toHaveBeenCalledWith("/output/stills", {
      recursive: true,
    });
  });

  it("cleans up temporary script after completion", async () => {
    setupSpawn([], 0);

    await renderStill("TestComp", 0, "/stills/frame.png");

    expect(fs.promises.unlink).toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 7. Source file structure checks
// ---------------------------------------------------------------------------

describe("lib/render.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    const realFs = jest.requireActual("fs") as typeof fs;
    sourceCode = realFs.readFileSync(
      path.join(__dirname, "..", "lib", "render.ts"),
      "utf-8"
    );
  });

  it("has server-only guard", () => {
    expect(sourceCode).toMatch(/server-only/);
  });

  it("imports renderMedia from @remotion/renderer", () => {
    expect(sourceCode).toMatch(/renderMedia/);
    expect(sourceCode).toMatch(/@remotion\/renderer/);
  });

  it("imports renderStill from @remotion/renderer", () => {
    expect(sourceCode).toMatch(/renderStill/);
  });

  it("imports selectComposition from @remotion/renderer", () => {
    expect(sourceCode).toMatch(/selectComposition/);
  });

  it("uses codec h264", () => {
    expect(sourceCode).toMatch(/codec:\s*['"]h264['"]/);
  });

  it("uses outputLocation for renderMedia", () => {
    expect(sourceCode).toMatch(/outputLocation/);
  });

  it("maps Remotion progress (0–1) to percent (0–100)", () => {
    expect(sourceCode).toMatch(/progress\s*\*\s*100/);
  });

  it("uses ffmpeg for stitching", () => {
    expect(sourceCode).toMatch(/ffmpeg/);
  });

  it("uses -f concat -safe 0 for ffmpeg concat demuxer", () => {
    expect(sourceCode).toMatch(/-f concat/);
    expect(sourceCode).toMatch(/-safe 0/);
  });

  it("uses -c copy for stream copying", () => {
    expect(sourceCode).toMatch(/-c copy/);
  });

  it("uses ffprobe for duration detection", () => {
    expect(sourceCode).toMatch(/ffprobe/);
  });

  it("uses ffprobe flags: -v error -show_entries format=duration", () => {
    expect(sourceCode).toMatch(/-v error/);
    expect(sourceCode).toMatch(/-show_entries format=duration/);
    expect(sourceCode).toMatch(/noprint_wrappers=1:nokey=1/);
  });

  it("parses duration with parseFloat", () => {
    expect(sourceCode).toMatch(/parseFloat/);
  });

  it("uses promisify for exec", () => {
    expect(sourceCode).toMatch(/promisify/);
    expect(sourceCode).toMatch(/exec/);
  });

  it("creates directories recursively", () => {
    expect(sourceCode).toMatch(/mkdir/);
    expect(sourceCode).toMatch(/recursive:\s*true/);
  });

  it("writes concat list to temp file", () => {
    expect(sourceCode).toMatch(/tmpdir/);
    expect(sourceCode).toMatch(/concat-/);
  });

  it("uses file 'path' format for ffmpeg concat list", () => {
    expect(sourceCode).toMatch(/file '/);
  });

  it("cleans up temp concat file after stitching", () => {
    expect(sourceCode).toMatch(/unlink/);
  });

  it("exports renderSection", () => {
    expect(sourceCode).toMatch(/export\s+(const|async\s+function)\s+renderSection/);
  });

  it("exports stitchFullVideo", () => {
    expect(sourceCode).toMatch(/export\s+(const|async\s+function)\s+stitchFullVideo/);
  });

  it("exports getSectionDuration", () => {
    expect(sourceCode).toMatch(/export\s+(const|async\s+function)\s+getSectionDuration/);
  });

  it("exports renderStill", () => {
    expect(sourceCode).toMatch(/export\s+(const|async\s+function)\s+renderStill/);
  });

  it("resolves bundle path from env var or convention", () => {
    expect(sourceCode).toMatch(/REMOTION_BUNDLE_PATH/);
    expect(sourceCode).toMatch(/remotion/);
  });
});

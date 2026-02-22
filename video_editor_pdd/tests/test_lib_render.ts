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
import { promisify } from "util";

// ---------------------------------------------------------------------------
// Mock @remotion/renderer
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
// Mock child_process.exec with promisify.custom support
// ---------------------------------------------------------------------------

const mockExecPromisified = jest.fn();
const mockExec = Object.assign(jest.fn(), {
  [promisify.custom]: mockExecPromisified,
});
jest.mock("child_process", () => ({
  exec: mockExec,
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
// 2. renderSection — Remotion renderMedia integration
// ---------------------------------------------------------------------------

describe("renderSection — renderMedia integration", () => {
  beforeEach(() => {
    setupFsMocks();
  });

  it("calls selectComposition with compositionId", async () => {
    setupSelectComposition("IntroComposition");
    mockRenderMedia.mockResolvedValue(undefined);

    await renderSection("IntroComposition", "/tmp/out.mp4", jest.fn());

    expect(mockSelectComposition).toHaveBeenCalledWith(
      expect.objectContaining({ id: "IntroComposition" })
    );
  });

  it("calls renderMedia with codec h264", async () => {
    setupSelectComposition();
    mockRenderMedia.mockResolvedValue(undefined);

    await renderSection("TestComp", "/tmp/out.mp4", jest.fn());

    expect(mockRenderMedia).toHaveBeenCalledWith(
      expect.objectContaining({ codec: "h264" })
    );
  });

  it("calls renderMedia with outputLocation set to outputPath", async () => {
    setupSelectComposition();
    mockRenderMedia.mockResolvedValue(undefined);

    await renderSection("TestComp", "/output/sections/intro.mp4", jest.fn());

    expect(mockRenderMedia).toHaveBeenCalledWith(
      expect.objectContaining({ outputLocation: "/output/sections/intro.mp4" })
    );
  });

  it("passes composition from selectComposition to renderMedia", async () => {
    const comp = setupSelectComposition("MyComp");
    mockRenderMedia.mockResolvedValue(undefined);

    await renderSection("MyComp", "/tmp/out.mp4", jest.fn());

    expect(mockRenderMedia).toHaveBeenCalledWith(
      expect.objectContaining({ composition: comp })
    );
  });

  it("passes serveUrl to both selectComposition and renderMedia", async () => {
    setupSelectComposition();
    mockRenderMedia.mockResolvedValue(undefined);

    await renderSection("TestComp", "/tmp/out.mp4", jest.fn());

    const selectCall = mockSelectComposition.mock.calls[0][0];
    const renderCall = mockRenderMedia.mock.calls[0][0];
    expect(selectCall.serveUrl).toBeDefined();
    expect(renderCall.serveUrl).toBe(selectCall.serveUrl);
  });

  it("maps Remotion progress 0–1 to RenderProgress percent 0–100", async () => {
    setupSelectComposition("IntroComposition");
    mockRenderMedia.mockImplementation(async (opts: any) => {
      opts.onProgress({ progress: 0 });
      opts.onProgress({ progress: 0.5 });
      opts.onProgress({ progress: 1.0 });
    });

    const progressCalls: Array<{ percent: number; message: string }> = [];
    await renderSection("IntroComposition", "/tmp/out.mp4", (p) =>
      progressCalls.push(p)
    );

    expect(progressCalls[0].percent).toBe(0);
    expect(progressCalls[1].percent).toBe(50);
    expect(progressCalls[2].percent).toBe(100);
  });

  it("includes compositionId in progress message", async () => {
    setupSelectComposition("IntroComposition");
    mockRenderMedia.mockImplementation(async (opts: any) => {
      opts.onProgress({ progress: 0.5 });
    });

    const progressCalls: Array<{ percent: number; message: string }> = [];
    await renderSection("IntroComposition", "/tmp/out.mp4", (p) =>
      progressCalls.push(p)
    );

    expect(progressCalls[0].message).toContain("IntroComposition");
  });

  it("ensures output directory exists before rendering", async () => {
    setupSelectComposition();
    mockRenderMedia.mockResolvedValue(undefined);

    await renderSection("TestComp", "/output/sections/intro.mp4", jest.fn());

    expect(fs.promises.mkdir).toHaveBeenCalledWith("/output/sections", {
      recursive: true,
    });
  });
});

// ---------------------------------------------------------------------------
// 3. renderSection — bundle path resolution
// ---------------------------------------------------------------------------

describe("renderSection — bundle path resolution", () => {
  beforeEach(() => {
    setupFsMocks();
    setupSelectComposition();
    mockRenderMedia.mockResolvedValue(undefined);
  });

  it("uses REMOTION_BUNDLE_PATH env var when set", async () => {
    process.env.REMOTION_BUNDLE_PATH = "/custom/bundle/path";

    await renderSection("TestComp", "/tmp/out.mp4", jest.fn());

    const selectCall = mockSelectComposition.mock.calls[0][0];
    expect(selectCall.serveUrl).toBe("/custom/bundle/path");
  });

  it("falls back to remotion/build/index.js when file exists", async () => {
    delete process.env.REMOTION_BUNDLE_PATH;
    (fs.existsSync as jest.Mock).mockReturnValue(true);

    await renderSection("TestComp", "/tmp/out.mp4", jest.fn());

    const selectCall = mockSelectComposition.mock.calls[0][0];
    expect(selectCall.serveUrl).toContain(
      path.join("remotion", "build", "index.js")
    );
  });

  it("falls back to remotion directory when no build exists", async () => {
    delete process.env.REMOTION_BUNDLE_PATH;
    (fs.existsSync as jest.Mock).mockReturnValue(false);

    await renderSection("TestComp", "/tmp/out.mp4", jest.fn());

    const selectCall = mockSelectComposition.mock.calls[0][0];
    expect(selectCall.serveUrl).toMatch(/remotion$/);
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

describe("renderStill — Remotion renderStill", () => {
  beforeEach(() => {
    setupFsMocks();
  });

  it("calls selectComposition with compositionId", async () => {
    setupSelectComposition("IntroComposition");
    mockRenderStill.mockResolvedValue(undefined);

    await renderStill("IntroComposition", 90, "/stills/frame.png");

    expect(mockSelectComposition).toHaveBeenCalledWith(
      expect.objectContaining({ id: "IntroComposition" })
    );
  });

  it("calls remotion renderStill with composition and frame", async () => {
    const comp = setupSelectComposition("IntroComposition");
    mockRenderStill.mockResolvedValue(undefined);

    await renderStill("IntroComposition", 90, "/stills/frame.png");

    expect(mockRenderStill).toHaveBeenCalledWith(
      expect.objectContaining({
        composition: comp,
        frame: 90,
      })
    );
  });

  it("passes output path to renderStill", async () => {
    setupSelectComposition();
    mockRenderStill.mockResolvedValue(undefined);

    await renderStill("TestComp", 0, "/output/stills/frame.png");

    expect(mockRenderStill).toHaveBeenCalledWith(
      expect.objectContaining({ output: "/output/stills/frame.png" })
    );
  });

  it("passes serveUrl to selectComposition and renderStill", async () => {
    setupSelectComposition();
    mockRenderStill.mockResolvedValue(undefined);

    await renderStill("TestComp", 0, "/stills/frame.png");

    const selectCall = mockSelectComposition.mock.calls[0][0];
    const stillCall = mockRenderStill.mock.calls[0][0];
    expect(selectCall.serveUrl).toBeDefined();
    expect(stillCall.serveUrl).toBe(selectCall.serveUrl);
  });

  it("ensures output directory exists before rendering still", async () => {
    setupSelectComposition();
    mockRenderStill.mockResolvedValue(undefined);

    await renderStill("TestComp", 0, "/output/stills/frame.png");

    expect(fs.promises.mkdir).toHaveBeenCalledWith("/output/stills", {
      recursive: true,
    });
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

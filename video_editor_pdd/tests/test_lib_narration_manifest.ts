import fs from "fs";
import os from "os";
import path from "path";

import {
  loadNarrationManifest,
  resolveSegmentTimingForSection,
} from "../lib/narration-manifest";

describe("lib/narration-manifest", () => {
  let tmpDir: string;

  beforeEach(() => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "narration-manifest-"));
  });

  afterEach(() => {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  });

  function writeManifest(segments: unknown[]) {
    const dir = path.join(tmpDir, "outputs", "tts");
    fs.mkdirSync(dir, { recursive: true });
    fs.writeFileSync(
      path.join(dir, "segments.json"),
      JSON.stringify({ segments })
    );
  }

  function writeWordTimestamps(sectionId: string, words: unknown[]) {
    const dir = path.join(tmpDir, "outputs", "tts", sectionId);
    fs.mkdirSync(dir, { recursive: true });
    fs.writeFileSync(
      path.join(dir, "word_timestamps.json"),
      JSON.stringify(words)
    );
  }

  it("loadNarrationManifest returns segments with timing", () => {
    writeManifest([
      {
        id: "cold_open_001",
        sectionId: "cold_open",
        startSeconds: 0.0,
        endSeconds: 1.1,
        text: "Welcome.",
        cleanText: "Welcome.",
      },
    ]);

    const result = loadNarrationManifest(tmpDir);

    expect(result).not.toBeNull();
    expect(result!.segments).toHaveLength(1);
    expect(result!.segments[0].startSeconds).toBe(0.0);
    expect(result!.segments[0].endSeconds).toBe(1.1);
  });

  it("loadNarrationManifest returns null timing for legacy segments", () => {
    writeManifest([
      {
        id: "intro_001",
        sectionId: "intro",
        text: "Hello.",
        cleanText: "Hello.",
      },
    ]);

    const result = loadNarrationManifest(tmpDir);

    expect(result).not.toBeNull();
    expect(result!.segments[0].startSeconds).toBeUndefined();
    expect(result!.segments[0].endSeconds).toBeUndefined();
  });

  it("resolveSegmentTimingForSection returns section-filtered segments", () => {
    writeManifest([
      {
        id: "cold_open_001",
        sectionId: "cold_open",
        startSeconds: 0.0,
        endSeconds: 1.0,
        text: "A",
        cleanText: "A",
      },
      {
        id: "intro_001",
        sectionId: "intro",
        startSeconds: 0.0,
        endSeconds: 2.0,
        text: "B",
        cleanText: "B",
      },
    ]);

    const result = resolveSegmentTimingForSection("cold_open", tmpDir);

    expect(result).toHaveLength(1);
    expect(result[0].id).toBe("cold_open_001");
  });

  it("resolveSegmentTimingForSection falls back to word_timestamps", () => {
    // Legacy manifest without timing
    writeManifest([
      {
        id: "demo_001",
        sectionId: "demo",
        text: "Hello world.",
        cleanText: "Hello world.",
      },
      {
        id: "demo_002",
        sectionId: "demo",
        text: "Goodbye.",
        cleanText: "Goodbye.",
      },
    ]);

    writeWordTimestamps("demo", [
      { word: "Hello", start: 0.0, end: 0.3, segmentId: "demo_001" },
      { word: "world", start: 0.3, end: 0.7, segmentId: "demo_001" },
      { word: "Goodbye", start: 1.0, end: 1.5, segmentId: "demo_002" },
    ]);

    const result = resolveSegmentTimingForSection("demo", tmpDir);

    expect(result).toHaveLength(2);
    expect(result[0].startSeconds).toBe(0.0);
    expect(result[0].endSeconds).toBe(0.7);
    expect(result[1].startSeconds).toBe(1.0);
    expect(result[1].endSeconds).toBe(1.5);
  });

  it("loadNarrationManifest returns null when manifest is missing", () => {
    const result = loadNarrationManifest(tmpDir);
    expect(result).toBeNull();
  });
});

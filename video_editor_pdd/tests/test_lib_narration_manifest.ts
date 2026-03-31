import fs from "fs";
import os from "os";
import path from "path";

import {
  buildNarrativeStructureManifest,
  loadNarrationManifest,
  loadNarrativeStructureManifest,
  normalizeAndPersistNarrativeStructureManifest,
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

  const mainScriptWithFoldedDemo = [
    "## COLD OPEN: THE SOCK HOOK (0:00 - 2:00)",
    "",
    "**NARRATOR:**",
    "If you use Cursor...",
    "",
    "## THE THIRTY-SECOND DEMO (2:00 - 2:30)",
    "",
    "**NARRATOR:**",
    "Watch this.",
    "",
    "## PART 1: THE ECONOMICS OF DARNING (2:30 - 8:30)",
    "",
    "**NARRATOR:**",
    "This isn't nostalgia.",
    "",
  ].join("\n");

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

  it("resolveSegmentTimingForSection prefers newer failed timestamps over older accepted timestamps", () => {
    writeManifest([
      {
        id: "demo_001",
        sectionId: "demo",
        text: "Hello world.",
        cleanText: "Hello world.",
      },
    ]);

    const dir = path.join(tmpDir, "outputs", "tts", "demo");
    fs.mkdirSync(dir, { recursive: true });
    const acceptedPath = path.join(dir, "word_timestamps.json");
    const failedPath = path.join(dir, "word_timestamps.failed.json");
    fs.writeFileSync(
      acceptedPath,
      JSON.stringify([
        { word: "Hello", start: 0.0, end: 0.2, segmentId: "demo_001" },
      ])
    );
    fs.writeFileSync(
      failedPath,
      JSON.stringify([
        { word: "Hello", start: 1.0, end: 1.3, segmentId: "demo_001" },
        { word: "world", start: 1.3, end: 1.7, segmentId: "demo_001" },
      ])
    );
    const now = new Date();
    fs.utimesSync(acceptedPath, new Date(now.getTime() - 60_000), new Date(now.getTime() - 60_000));
    fs.utimesSync(failedPath, now, now);

    const result = resolveSegmentTimingForSection("demo", tmpDir);

    expect(result).toHaveLength(1);
    expect(result[0].startSeconds).toBe(1.0);
    expect(result[0].endSeconds).toBe(1.7);
  });

  it("loadNarrationManifest returns null when manifest is missing", () => {
    const result = loadNarrationManifest(tmpDir);
    expect(result).toBeNull();
  });

  it("buildNarrativeStructureManifest preserves every timed heading with explicit owner and kind", () => {
    const manifest = buildNarrativeStructureManifest(mainScriptWithFoldedDemo, [
      { id: "cold_open", label: "Cold Open" },
      { id: "part1_economics", label: "Part 1: Economics of Darning" },
    ]);

    expect(manifest.headings).toEqual([
      expect.objectContaining({
        order: 0,
        heading: "COLD OPEN: THE SOCK HOOK (0:00 - 2:00)",
        pipelineSectionId: "cold_open",
        kind: "section",
      }),
      expect.objectContaining({
        order: 1,
        heading: "THE THIRTY-SECOND DEMO (2:00 - 2:30)",
        pipelineSectionId: "cold_open",
        kind: "folded_heading",
      }),
      expect.objectContaining({
        order: 2,
        heading: "PART 1: THE ECONOMICS OF DARNING (2:30 - 8:30)",
        pipelineSectionId: "part1_economics",
        kind: "section",
      }),
    ]);
  });

  it("normalizeAndPersistNarrativeStructureManifest writes and loadNarrativeStructureManifest reads the canonical artifact", () => {
    const manifest = normalizeAndPersistNarrativeStructureManifest({
      projectDir: tmpDir,
      mainScript: mainScriptWithFoldedDemo,
      projectSections: [
        { id: "cold_open", label: "Cold Open" },
        { id: "part1_economics", label: "Part 1: Economics of Darning" },
      ],
    });

    expect(
      fs.existsSync(path.join(tmpDir, "outputs", "narrative", "structure.json")),
    ).toBe(true);
    expect(loadNarrativeStructureManifest(tmpDir)).toEqual(manifest);
  });

  it("excludes untimed appendix headings from the canonical narrative structure manifest", () => {
    const manifest = buildNarrativeStructureManifest(
      [
        mainScriptWithFoldedDemo,
        "",
        "## VISUAL DESIGN NOTES",
        "",
        "Design appendix.",
        "",
        "## RESEARCH CITATIONS",
        "",
        "Citation appendix.",
        "",
      ].join("\n"),
      [
        { id: "cold_open", label: "Cold Open" },
        { id: "part1_economics", label: "Part 1: Economics of Darning" },
      ],
    );

    expect(manifest.headings.map((heading) => heading.heading)).toEqual([
      "COLD OPEN: THE SOCK HOOK (0:00 - 2:00)",
      "THE THIRTY-SECOND DEMO (2:00 - 2:30)",
      "PART 1: THE ECONOMICS OF DARNING (2:30 - 8:30)",
    ]);
  });
});

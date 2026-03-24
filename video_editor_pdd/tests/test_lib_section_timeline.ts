import fs from "fs";
import os from "os";
import path from "path";

import {
  loadSectionTimeline,
  resolveSectionTimelineEntries,
  buildSectionTimeline,
  writeSectionTimelineManifest,
  type SectionTimelineManifest,
  type SectionTimeline,
  type TimelineEntry,
} from "../lib/section-timeline";

// Mock projects module so getProjectDir returns our tmpDir
let mockProjectDir = "";
jest.mock("@/lib/projects", () => ({
  getProjectDir: () => mockProjectDir,
}));

describe("lib/section-timeline", () => {
  let tmpDir: string;

  beforeEach(() => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "section-timeline-"));
    mockProjectDir = tmpDir;
  });

  afterEach(() => {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  });

  // -----------------------------------------------------------------------
  // Helpers
  // -----------------------------------------------------------------------

  function writeTimelineManifest(manifest: SectionTimelineManifest) {
    const dir = path.join(tmpDir, "outputs", "compositions");
    fs.mkdirSync(dir, { recursive: true });
    fs.writeFileSync(
      path.join(dir, "section-timeline.json"),
      JSON.stringify(manifest)
    );
  }

  function writeVisualManifest(sections: unknown[]) {
    const dir = path.join(tmpDir, "outputs", "compositions");
    fs.mkdirSync(dir, { recursive: true });
    fs.writeFileSync(
      path.join(dir, "visual-manifest.json"),
      JSON.stringify({
        version: 1,
        updatedAt: new Date().toISOString(),
        sections,
      })
    );
  }

  function writeNarrationManifest(segments: unknown[]) {
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

  function writeSpec(sectionId: string, specName: string, content: string) {
    const dir = path.join(tmpDir, "specs", sectionId);
    fs.mkdirSync(dir, { recursive: true });
    fs.writeFileSync(path.join(dir, `${specName}.md`), content);
  }

  // -----------------------------------------------------------------------
  // Phase 3A: Loader tests
  // -----------------------------------------------------------------------

  describe("loader", () => {
    it("loadSectionTimeline returns null when manifest missing", () => {
      expect(loadSectionTimeline(tmpDir)).toBeNull();
    });

    it("loadSectionTimeline parses valid manifest", () => {
      const manifest: SectionTimelineManifest = {
        version: 1,
        updatedAt: "2026-03-23T00:00:00Z",
        sections: [
          {
            sectionId: "cold_open",
            durationSeconds: 10,
            entries: [
              {
                id: "cold_open_01_title",
                startSeconds: 0,
                endSeconds: 3,
                lane: 0,
                source: "segment-anchor",
                desc: "01 title",
              },
            ],
          },
        ],
      };
      writeTimelineManifest(manifest);

      const result = loadSectionTimeline(tmpDir);
      expect(result).not.toBeNull();
      expect(result!.sections).toHaveLength(1);
      expect(result!.sections[0].entries[0].id).toBe("cold_open_01_title");
    });

    it("loadSectionTimeline returns null for malformed json", () => {
      const dir = path.join(tmpDir, "outputs", "compositions");
      fs.mkdirSync(dir, { recursive: true });
      fs.writeFileSync(
        path.join(dir, "section-timeline.json"),
        "not valid json"
      );

      expect(loadSectionTimeline(tmpDir)).toBeNull();
    });

    it("resolveSectionTimelineEntries returns entries for section", () => {
      writeTimelineManifest({
        version: 1,
        updatedAt: "2026-03-23T00:00:00Z",
        sections: [
          {
            sectionId: "cold_open",
            durationSeconds: 10,
            entries: [
              {
                id: "v1",
                startSeconds: 0,
                endSeconds: 3,
                lane: 0,
                source: "segment-anchor",
                desc: "v1",
              },
            ],
          },
        ],
      });

      const entries = resolveSectionTimelineEntries("cold_open", tmpDir);
      expect(entries).toHaveLength(1);
      expect(entries[0].id).toBe("v1");
    });

    it("resolveSectionTimelineEntries returns empty for unknown section", () => {
      writeTimelineManifest({
        version: 1,
        updatedAt: "2026-03-23T00:00:00Z",
        sections: [],
      });

      expect(resolveSectionTimelineEntries("nonexistent", tmpDir)).toEqual([]);
    });
  });

  // -----------------------------------------------------------------------
  // Phase 3B: Resolver tests
  // -----------------------------------------------------------------------

  describe("buildSectionTimeline", () => {
    const baseSectionConfig = {
      id: "cold_open",
      specDir: "cold_open",
      durationSeconds: 10,
      compositionId: "ColdOpen",
    };

    it("uses coverSegments for timing", () => {
      writeNarrationManifest([
        {
          id: "cold_open_001",
          sectionId: "cold_open",
          startSeconds: 0.0,
          endSeconds: 2.5,
          text: "A",
          cleanText: "A",
        },
        {
          id: "cold_open_002",
          sectionId: "cold_open",
          startSeconds: 2.5,
          endSeconds: 5.0,
          text: "B",
          cleanText: "B",
        },
      ]);

      writeVisualManifest([
        {
          id: "cold_open",
          visuals: [
            {
              id: "cold_open_01_title",
              specBaseName: "01_title",
              coverSegments: ["cold_open_001", "cold_open_002"],
            },
          ],
        },
      ]);

      // Need word_timestamps so narrative timing works
      writeWordTimestamps("cold_open", [
        { word: "A", start: 0.0, end: 2.5, segmentId: "cold_open_001" },
        { word: "B", start: 2.5, end: 5.0, segmentId: "cold_open_002" },
      ]);

      const timeline = buildSectionTimeline(tmpDir, baseSectionConfig);
      expect(timeline.entries).toHaveLength(1);
      expect(timeline.entries[0].source).toBe("segment-anchor");
      expect(timeline.entries[0].start).toEqual({
        type: "segmentStart",
        segmentId: "cold_open_001",
      });
      expect(timeline.entries[0].end).toEqual({
        type: "segmentEnd",
        segmentId: "cold_open_002",
      });
      expect(timeline.entries[0].resolvedStartSeconds).toBe(0.0);
      expect(timeline.entries[0].resolvedEndSeconds).toBe(5.0);
      expect(timeline.entries[0].startSeconds).toBe(0.0);
      expect(timeline.entries[0].endSeconds).toBe(5.0);
      expect(timeline.entries[0].coverSegments).toEqual([
        "cold_open_001",
        "cold_open_002",
      ]);
    });

    it("falls back to spec timestamp", () => {
      writeVisualManifest([
        {
          id: "cold_open",
          visuals: [
            {
              id: "cold_open_01_title",
              specBaseName: "01_title",
              specPath: "specs/cold_open/01_title.md",
            },
          ],
        },
      ]);

      writeSpec(
        "cold_open",
        "01_title",
        "**Timestamp:** 0:03 - 0:08\n\n# Title"
      );

      writeWordTimestamps("cold_open", [
        { word: "Hello", start: 0.0, end: 10.0 },
      ]);

      const timeline = buildSectionTimeline(tmpDir, baseSectionConfig);
      expect(timeline.entries).toHaveLength(1);
      expect(timeline.entries[0].source).toBe("timestamp-fallback");
      expect(timeline.entries[0].start).toEqual({
        type: "absolute",
        seconds: 3.75,
      });
      expect(timeline.entries[0].end).toEqual({
        type: "absolute",
        seconds: 10,
      });
      expect(timeline.entries[0].startSeconds).toBeGreaterThanOrEqual(0);
    });

    it("preserves lane from visual contract", () => {
      writeVisualManifest([
        {
          id: "cold_open",
          visuals: [
            {
              id: "v_main",
              specBaseName: "01_main",
              laneHint: "main",
              coverSegments: ["cold_open_001"],
            },
            {
              id: "v_overlay",
              specBaseName: "02_badge",
              laneHint: "overlay",
              coverSegments: ["cold_open_001"],
            },
          ],
        },
      ]);

      writeNarrationManifest([
        {
          id: "cold_open_001",
          sectionId: "cold_open",
          startSeconds: 0.0,
          endSeconds: 5.0,
          text: "A",
          cleanText: "A",
        },
      ]);

      writeWordTimestamps("cold_open", [
        { word: "A", start: 0.0, end: 5.0, segmentId: "cold_open_001" },
      ]);

      const timeline = buildSectionTimeline(tmpDir, baseSectionConfig);
      const mainEntry = timeline.entries.find((e) => e.id === "v_main");
      const overlayEntry = timeline.entries.find((e) => e.id === "v_overlay");

      expect(mainEntry!.lane).toBe(0);
      expect(overlayEntry!.lane).toBe(1);
    });

    it("allows overlapping entries on different lanes", () => {
      writeVisualManifest([
        {
          id: "cold_open",
          visuals: [
            {
              id: "v_main",
              specBaseName: "01_main",
              laneHint: "main",
              coverSegments: ["cold_open_001"],
            },
            {
              id: "v_overlay",
              specBaseName: "02_badge",
              laneHint: "overlay",
              coverSegments: ["cold_open_001"],
            },
          ],
        },
      ]);

      writeNarrationManifest([
        {
          id: "cold_open_001",
          sectionId: "cold_open",
          startSeconds: 0.0,
          endSeconds: 5.0,
          text: "A",
          cleanText: "A",
        },
      ]);

      writeWordTimestamps("cold_open", [
        { word: "A", start: 0.0, end: 5.0, segmentId: "cold_open_001" },
      ]);

      const timeline = buildSectionTimeline(tmpDir, baseSectionConfig);
      const mainEntry = timeline.entries.find((e) => e.id === "v_main")!;
      const overlayEntry = timeline.entries.find(
        (e) => e.id === "v_overlay"
      )!;

      // Both cover the same segment → same time range, different lanes
      expect(mainEntry.startSeconds).toBe(0.0);
      expect(overlayEntry.startSeconds).toBe(0.0);
      expect(mainEntry.endSeconds).toBe(5.0);
      expect(overlayEntry.endSeconds).toBe(5.0);
    });

    it("preserves same-lane overlaps instead of rewriting them", () => {
      writeVisualManifest([
        {
          id: "cold_open",
          visuals: [
            {
              id: "v1",
              specBaseName: "01_a",
              coverSegments: ["cold_open_001"],
            },
            {
              id: "v2",
              specBaseName: "02_b",
              coverSegments: ["cold_open_001"],
            },
          ],
        },
      ]);

      writeNarrationManifest([
        {
          id: "cold_open_001",
          sectionId: "cold_open",
          startSeconds: 0.0,
          endSeconds: 5.0,
          text: "A",
          cleanText: "A",
        },
      ]);

      writeWordTimestamps("cold_open", [
        { word: "A", start: 0.0, end: 5.0, segmentId: "cold_open_001" },
      ]);

      const timeline = buildSectionTimeline(tmpDir, baseSectionConfig);
      const v1 = timeline.entries.find((e) => e.id === "v1")!;
      const v2 = timeline.entries.find((e) => e.id === "v2")!;

      expect(v1.startSeconds).toBe(0.0);
      expect(v2.startSeconds).toBe(0.0);
      expect(v1.endSeconds).toBe(5.0);
      expect(v2.endSeconds).toBe(5.0);
    });

    it("resolves explicit absolute and sectionEnd anchors", () => {
      writeVisualManifest([
        {
          id: "cold_open",
          visuals: [
            {
              id: "v_pause",
              specBaseName: "07_pause",
              startAnchor: { type: "absolute", seconds: 4.25 },
              endAnchor: { type: "sectionEnd" },
            },
          ],
        },
      ]);

      writeWordTimestamps("cold_open", [
        { word: "Hello", start: 0.0, end: 10.0 },
      ]);

      const timeline = buildSectionTimeline(tmpDir, baseSectionConfig);
      expect(timeline.entries).toHaveLength(1);
      expect(timeline.entries[0].source).toBe("absolute");
      expect(timeline.entries[0].start).toEqual({
        type: "absolute",
        seconds: 4.25,
      });
      expect(timeline.entries[0].end).toEqual({
        type: "sectionEnd",
      });
      expect(timeline.entries[0].resolvedStartSeconds).toBe(4.25);
      expect(timeline.entries[0].resolvedEndSeconds).toBe(10);
    });

    it("excludes children from entries", () => {
      writeVisualManifest([
        {
          id: "cold_open",
          visuals: [
            {
              id: "v_parent",
              specBaseName: "01_split",
              children: ["v_child"],
              coverSegments: ["cold_open_001"],
            },
            {
              id: "v_child",
              specBaseName: "02_veo",
              parentId: "v_parent",
            },
          ],
        },
      ]);

      writeNarrationManifest([
        {
          id: "cold_open_001",
          sectionId: "cold_open",
          startSeconds: 0.0,
          endSeconds: 5.0,
          text: "A",
          cleanText: "A",
        },
      ]);

      writeWordTimestamps("cold_open", [
        { word: "A", start: 0.0, end: 5.0, segmentId: "cold_open_001" },
      ]);

      const timeline = buildSectionTimeline(tmpDir, baseSectionConfig);
      expect(timeline.entries.map((e) => e.id)).toContain("v_parent");
      expect(timeline.entries.map((e) => e.id)).not.toContain("v_child");
    });

    it("distributes untimed gaps (fallback entries)", () => {
      writeVisualManifest([
        {
          id: "cold_open",
          visuals: [
            {
              id: "v1",
              specBaseName: "01_a",
              coverSegments: ["cold_open_001"],
            },
            { id: "v2", specBaseName: "02_b" },
            { id: "v3", specBaseName: "03_c" },
          ],
        },
      ]);

      writeNarrationManifest([
        {
          id: "cold_open_001",
          sectionId: "cold_open",
          startSeconds: 0.0,
          endSeconds: 4.0,
          text: "A",
          cleanText: "A",
        },
      ]);

      writeWordTimestamps("cold_open", [
        { word: "A", start: 0.0, end: 10.0, segmentId: "cold_open_001" },
      ]);

      const timeline = buildSectionTimeline(tmpDir, baseSectionConfig);
      const v2 = timeline.entries.find((e) => e.id === "v2")!;
      const v3 = timeline.entries.find((e) => e.id === "v3")!;

      expect(v2.source).toBe("fallback");
      expect(v3.source).toBe("fallback");
      // Fallback entries should be distributed after the timed entry
      expect(v2.startSeconds).toBeGreaterThanOrEqual(4.0);
      expect(v3.startSeconds).toBeGreaterThanOrEqual(v2.endSeconds);
    });
  });

  // -----------------------------------------------------------------------
  // Writer / merger tests
  // -----------------------------------------------------------------------

  describe("writeSectionTimelineManifest", () => {
    it("writes and merges timelines across section runs", () => {
      const timeline1: SectionTimeline = {
        sectionId: "cold_open",
        durationSeconds: 10,
        entries: [
          {
            id: "v1",
            startSeconds: 0,
            endSeconds: 5,
            lane: 0,
            source: "segment-anchor",
            desc: "v1",
          },
        ],
      };

      writeSectionTimelineManifest([timeline1], tmpDir);

      // Now write a second section — should merge
      const timeline2: SectionTimeline = {
        sectionId: "intro",
        durationSeconds: 8,
        entries: [
          {
            id: "v2",
            startSeconds: 0,
            endSeconds: 4,
            lane: 0,
            source: "fallback",
            desc: "v2",
          },
        ],
      };

      writeSectionTimelineManifest([timeline2], tmpDir);

      const result = loadSectionTimeline(tmpDir);
      expect(result!.sections).toHaveLength(2);
      expect(result!.sections.map((s) => s.sectionId).sort()).toEqual([
        "cold_open",
        "intro",
      ]);
    });
  });

  describe("project regressions", () => {
    it("uses explicit segment anchors for the closing beat in pdd-explainer", () => {
      const projectDir = path.join(process.cwd(), "projects", "pdd-explainer");
      const timeline = buildSectionTimeline(projectDir, {
        id: "closing",
        specDir: "closing",
        durationSeconds: 0,
        compositionId: "ClosingSection",
      });

      const beat = timeline.entries.find((entry) => entry.id === "07_the_beat");
      const titleCard = timeline.entries.find(
        (entry) => entry.id === "08_final_title_card"
      );

      expect(beat).toBeDefined();
      expect(titleCard).toBeDefined();
      expect(beat!.source).toBe("segment-anchor");
      expect(beat!.start).toEqual({
        type: "segmentEnd",
        segmentId: "closing_004",
      });
      expect(beat!.end).toEqual({
        type: "segmentStart",
        segmentId: "closing_005",
      });
      expect(beat!.resolvedEndSeconds).toBe(titleCard!.resolvedStartSeconds);
    });
  });
});

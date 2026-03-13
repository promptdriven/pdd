import fs from "fs";
import os from "os";
import path from "path";

import {
  parseSpecTimestampRange,
  listSectionVisualIds,
  resolveSpecAuditHints,
  resolveSectionVisualTimings,
  buildSectionConstantsSource,
} from "../lib/composition-timing";

describe("lib/composition-timing", () => {
  let tmpDir: string;

  beforeEach(() => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "composition-timing-"));
  });

  afterEach(() => {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  });

  it("parses markdown timestamp ranges into section seconds", () => {
    const result = parseSpecTimestampRange([
      "# Demo",
      "",
      "**Timestamp:** 0:03 - 0:08",
      "",
    ].join("\n"));

    expect(result).toEqual({ startSeconds: 3, endSeconds: 8 });
  });

  it("parses markdown timestamp ranges that use an en dash separator", () => {
    const result = parseSpecTimestampRange([
      "# Demo",
      "",
      "**Timestamp:** 0:03 – 0:08",
      "",
    ].join("\n"));

    expect(result).toEqual({ startSeconds: 3, endSeconds: 8 });
  });

  it("returns null when a spec has no timestamp range", () => {
    expect(parseSpecTimestampRange("# Demo\n\nNo timestamp here")).toBeNull();
  });

  it("prefers spec timestamp windows and scales them to the section duration", () => {
    const specDir = path.join(tmpDir, "specs", "animation_section");
    fs.mkdirSync(specDir, { recursive: true });
    fs.writeFileSync(
      path.join(specDir, "01_title_card.md"),
      "**Timestamp:** 0:00 - 0:03\n\n# Title"
    );
    fs.writeFileSync(
      path.join(specDir, "02_key_visual.md"),
      "**Timestamp:** 0:03 - 0:08\n\n# Key Visual"
    );

    const timings = resolveSectionVisualTimings(
      tmpDir,
      {
        id: "animation_section",
        specDir: "animation_section",
        durationSeconds: 6,
      },
      ["animation_section_01_title_card", "02_key_visual"]
    );

    expect(timings).toEqual([
      expect.objectContaining({
        id: "animation_section_01_title_card",
        startSeconds: 0,
        endSeconds: 2.25,
        source: "spec",
      }),
      expect.objectContaining({
        id: "02_key_visual",
        startSeconds: 2.25,
        endSeconds: 6,
        source: "spec",
      }),
    ]);
  });

  it("normalizes global spec timestamps into section-local time using the section offset", () => {
    const specDir = path.join(tmpDir, "specs", "veo_section");
    fs.mkdirSync(specDir, { recursive: true });
    fs.writeFileSync(
      path.join(specDir, "02_ocean_wave_broll.md"),
      "**Timestamp:** 0:10 – 0:14\n\n# Ocean Wave Broll"
    );

    const timings = resolveSectionVisualTimings(
      tmpDir,
      {
        id: "veo_section",
        specDir: "veo_section",
        durationSeconds: 7.344,
        offsetSeconds: 7,
      },
      ["02_ocean_wave_broll"]
    );

    expect(timings).toEqual([
      expect.objectContaining({
        id: "02_ocean_wave_broll",
        startSeconds: 3,
        endSeconds: 7.344,
        source: "spec",
      }),
    ]);
  });

  it("falls back to audio sync word timestamps when a spec timestamp is missing", () => {
    const specDir = path.join(tmpDir, "specs", "part1_economics");
    const wordsDir = path.join(tmpDir, "outputs", "tts", "part1_economics");
    fs.mkdirSync(specDir, { recursive: true });
    fs.mkdirSync(wordsDir, { recursive: true });
    fs.writeFileSync(
      path.join(specDir, "stat_callout_gitclear.md"),
      "# GitClear callout\n\nNo explicit timestamp"
    );
    fs.writeFileSync(
      path.join(wordsDir, "word_timestamps.json"),
      JSON.stringify([
        { word: "GitClear", start: 12.5, end: 13.0, segmentId: "part1_economics_001" },
      ])
    );

    const timings = resolveSectionVisualTimings(
      tmpDir,
      {
        id: "part1_economics",
        specDir: "part1_economics",
        durationSeconds: 20,
      },
      ["part1_economics_stat_callout_gitclear"]
    );

    expect(timings).toEqual([
      expect.objectContaining({
        id: "part1_economics_stat_callout_gitclear",
        startSeconds: 11.5,
        endSeconds: 20,
        source: "audio-sync",
      }),
    ]);
  });

  it("strips numeric prefixes before resolving audio-sync keywords", () => {
    const specDir = path.join(tmpDir, "specs", "animation_section");
    const wordsDir = path.join(tmpDir, "outputs", "tts", "animation_section");
    fs.mkdirSync(specDir, { recursive: true });
    fs.mkdirSync(wordsDir, { recursive: true });
    fs.writeFileSync(
      path.join(specDir, "05_split_comparison.md"),
      "# Split Comparison\n\nNo explicit timestamp"
    );
    fs.writeFileSync(
      path.join(wordsDir, "word_timestamps.json"),
      JSON.stringify([
        { word: "comparison", start: 4.25, end: 4.5, segmentId: "animation_section_001" },
      ])
    );

    const timings = resolveSectionVisualTimings(
      tmpDir,
      {
        id: "animation_section",
        specDir: "animation_section",
        durationSeconds: 9,
      },
      ["05_split_comparison"]
    );

    expect(timings).toEqual([
      expect.objectContaining({
        id: "05_split_comparison",
        startSeconds: 3.25,
        source: "audio-sync",
      }),
    ]);
    expect(timings[0]?.endSeconds).toBe(9);
  });

  it("fills untimed gaps deterministically without exceeding the section duration", () => {
    const specDir = path.join(tmpDir, "specs", "veo_section");
    fs.mkdirSync(specDir, { recursive: true });
    fs.writeFileSync(
      path.join(specDir, "01_title_card.md"),
      "**Timestamp:** 0:00 - 0:03\n\n# Title"
    );

    const timings = resolveSectionVisualTimings(
      tmpDir,
      {
        id: "veo_section",
        specDir: "veo_section",
        durationSeconds: 9,
      },
      ["veo_section_01_title_card", "03_overlay", "04_outro"]
    );

    expect(timings).toHaveLength(3);
    expect(timings[0]).toEqual(
      expect.objectContaining({
        id: "veo_section_01_title_card",
        startSeconds: 0,
        endSeconds: 3,
      })
    );
    expect(timings[1].source).toBe("fallback");
    expect(timings[2].source).toBe("fallback");
    expect(timings[1].startSeconds).toBeGreaterThanOrEqual(3);
    expect(timings[2].endSeconds).toBeLessThanOrEqual(9);
    expect(timings[1].startSeconds).toBeLessThan(timings[1].endSeconds);
    expect(timings[2].startSeconds).toBeLessThan(timings[2].endSeconds);
  });

  it("builds a full section timeline from spec files, including pure Veo visuals", () => {
    const specDir = path.join(tmpDir, "specs", "veo_section");
    const veoOutputDir = path.join(tmpDir, "outputs", "veo");
    fs.mkdirSync(specDir, { recursive: true });
    fs.mkdirSync(veoOutputDir, { recursive: true });
    fs.writeFileSync(
      path.join(specDir, "01_title_card.md"),
      "**Timestamp:** 0:00 - 0:03\n"
    );
    fs.writeFileSync(
      path.join(specDir, "02_ocean_wave_sunset.md"),
      "**Timestamp:** 0:03 - 0:06\n"
    );
    fs.writeFileSync(
      path.join(specDir, "03_narration_overlay_intro.md"),
      "**Timestamp:** 0:06 - 0:09\n"
    );
    fs.writeFileSync(
      path.join(veoOutputDir, "02_ocean_wave_sunset.mp4"),
      "stub veo asset"
    );

    const visualIds = listSectionVisualIds(
      tmpDir,
      {
        id: "veo_section",
        specDir: "veo_section",
        durationSeconds: 6,
        compositionId: "VeoSection",
      },
      ["veo_section_01_title_card", "03_narration_overlay_intro"]
    );

    expect(visualIds).toEqual([
      "veo_section_01_title_card",
      "02_ocean_wave_sunset",
      "03_narration_overlay_intro",
    ]);

    const source = buildSectionConstantsSource(
      tmpDir,
      {
        id: "veo_section",
        specDir: "veo_section",
        durationSeconds: 6,
        compositionId: "VeoSection",
      },
      ["veo_section_01_title_card", "03_narration_overlay_intro"]
    );

    expect(source).toContain('id: "veo_section_01_title_card"');
    expect(source).toContain('id: "02_ocean_wave_sunset"');
    expect(source).toContain('id: "03_narration_overlay_intro"');
  });

  it("drops spec-only visuals that have no component and no explicit staged media", () => {
    const specDir = path.join(tmpDir, "specs", "animation_section");
    fs.mkdirSync(specDir, { recursive: true });
    fs.writeFileSync(
      path.join(specDir, "01_title_card.md"),
      "**Timestamp:** 0:00 - 0:03\n"
    );
    fs.writeFileSync(
      path.join(specDir, "04_veo_broll.md"),
      "**Timestamp:** 0:03 - 0:06\n"
    );

    const visualIds = listSectionVisualIds(
      tmpDir,
      {
        id: "animation_section",
        specDir: "animation_section",
        durationSeconds: 6,
        compositionId: "AnimationSection",
      },
      ["animation_section_01_title_card"]
    );

    expect(visualIds).toEqual(["animation_section_01_title_card"]);
  });

  it("derives general audit hints from spec structure for layout, effects, and animation phases", () => {
    const hints = resolveSpecAuditHints([
      "# Split Comparison",
      "",
      "## Visual Description",
      "A split-screen comparison placing ocean footage side-by-side with forest footage.",
      "",
      "### Chart/Visual Elements",
      '- **Ocean at Sunset** label sits in the left panel',
      '- **Forest Canopy** label sits in the right panel',
      '- **Glowing separator line** divides the two panels',
      '- **Soft bloom accent** adds subtle polish',
      "",
      "### Animation Sequence",
      "1. **Frame 0–20 (0–0.67s):** Ocean plate holds steady",
      "2. **Frame 21–40 (0.70–1.33s):** Forest panel fades in",
    ].join("\n"));

    expect(hints.criticalElements).toEqual(
      expect.arrayContaining(["Ocean at Sunset", "Forest Canopy"])
    );
    expect(hints.decorativeElements).toEqual(
      expect.arrayContaining(["Glowing separator line", "Soft bloom accent"])
    );
    expect(hints.layoutKeywords).toEqual(
      expect.arrayContaining(["split-screen", "side-by-side", "left panel", "right panel"])
    );
    expect(hints.transitionWindows).toEqual([
      {
        startFrame: 0,
        endFrame: 20,
        description: "Ocean plate holds steady",
      },
      {
        startFrame: 21,
        endFrame: 40,
        description: "Forest panel fades in",
      },
    ]);
  });

  it("sequentializes overlapping spec windows instead of collapsing later visuals into one-frame slots", () => {
    const specDir = path.join(tmpDir, "specs", "animation_section");
    fs.mkdirSync(specDir, { recursive: true });
    fs.writeFileSync(
      path.join(specDir, "01_title_card.md"),
      "**Timestamp:** 0:00 - 0:05\n"
    );
    fs.writeFileSync(
      path.join(specDir, "02_key_visual.md"),
      "**Timestamp:** 0:00 - 0:05\n"
    );
    fs.writeFileSync(
      path.join(specDir, "03_split_summary.md"),
      "**Timestamp:** 0:00 - 0:05\n"
    );

    const timings = resolveSectionVisualTimings(
      tmpDir,
      {
        id: "animation_section",
        specDir: "animation_section",
        durationSeconds: 12,
        compositionId: "AnimationSection",
      },
      [
        "animation_section_01_title_card",
        "animation_section_02_key_visual",
        "animation_section_03_split_summary",
      ]
    );

    expect(timings).toHaveLength(3);
    expect(timings[0].startSeconds).toBe(0);
    expect(timings[1].startSeconds).toBeGreaterThan(3);
    expect(timings[2].startSeconds).toBeGreaterThan(7);
    expect(timings[2].endSeconds).toBe(12);
  });
});

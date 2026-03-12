import fs from "fs";
import os from "os";
import path from "path";

import {
  resolveAuditSampleWindow,
  resolveRenderedAuditSampleWindow,
} from "../lib/audit-timing";

describe("resolveAuditSampleWindow", () => {
  it("biases timestamp-only specs toward the later part of the window", () => {
    const spec = `
**Timestamp:** 0:00 - 0:03
`;

    const result = resolveAuditSampleWindow(spec, {
      sectionDurationSeconds: 10.752,
      fps: 30,
    });

    expect(result.source).toBe("timestamp");
    expect(result.startSeconds).toBe(0);
    expect(result.endSeconds).toBe(3);
    expect(result.sampleSeconds).toBe(2.25);
  });

  it("supports minute-second timestamp ranges", () => {
    const spec = `
**Timestamp:** 1:12 - 1:18
`;

    const result = resolveAuditSampleWindow(spec, {
      sectionDurationSeconds: 120,
      fps: 30,
    });

    expect(result.source).toBe("timestamp");
    expect(result.startSeconds).toBe(72);
    expect(result.endSeconds).toBe(78);
    expect(result.sampleSeconds).toBe(76.5);
  });

  it("supports timestamp ranges that use an en dash separator", () => {
    const spec = `
**Timestamp:** 0:10 – 0:14
`;

    const result = resolveAuditSampleWindow(spec, {
      sectionDurationSeconds: 20,
      fps: 30,
    });

    expect(result.source).toBe("timestamp");
    expect(result.startSeconds).toBe(10);
    expect(result.endSeconds).toBe(14);
    expect(result.sampleSeconds).toBe(13);
  });

  it("normalizes global timestamp ranges to section-local time when a section offset is provided", () => {
    const spec = `
**Timestamp:** 0:10 – 0:14
`;

    const result = resolveAuditSampleWindow(spec, {
      sectionDurationSeconds: 7.344,
      fps: 30,
      sectionOffsetSeconds: 7,
    });

    expect(result.source).toBe("timestamp");
    expect(result.startSeconds).toBe(3);
    expect(result.endSeconds).toBe(7);
    expect(result.sampleSeconds).toBe(6);
    expect(result.intrinsicSampleSeconds).toBeCloseTo(3, 3);
  });

  it("prefers the final animation-sequence range when timestamp is missing", () => {
    const spec = `
## Animation Sequence
1. Frame 15-45: Intro beat.
2. Frames 45-105: Main beat.
3. Frame 105-135: Hold.
`;

    const result = resolveAuditSampleWindow(spec, {
      sectionDurationSeconds: 10,
      fps: 30,
    });

    expect(result.source).toBe("frame-range");
    expect(result.startSeconds).toBeCloseTo(3.5);
    expect(result.endSeconds).toBeCloseTo(4.5);
    expect(result.sampleSeconds).toBeCloseTo(4);
  });

  it("prefers a hold range over the broader timestamp window when both are present", () => {
    const spec = `
**Timestamp:** 0:00 - 0:03

## Animation Sequence
1. Frame 0-15: Fade in.
2. Frame 15-45: Title reveal.
3. Frame 45-65: Rule expansion.
4. Frame 65-90: Hold — all elements static at full opacity.
`;

    const result = resolveAuditSampleWindow(spec, {
      sectionDurationSeconds: 10.752,
      fps: 30,
    });

    expect(result.source).toBe("frame-range");
    expect(result.startSeconds).toBeCloseTo(65 / 30);
    expect(result.endSeconds).toBeCloseTo(90 / 30);
    expect(result.sampleSeconds).toBeCloseTo(77.5 / 30);
  });

  it("parses bolded markdown frame ranges used in generated specs", () => {
    const spec = `
**Timestamp:** 0:00 - 0:03

## Animation Sequence
1. **Frame 0-15 (0-0.5s):** Fade in.
2. **Frame 15-45 (0.5-1.5s):** Title reveal.
3. **Frame 45-65 (1.5-2.17s):** Rule expansion.
4. **Frame 65-90 (2.17-3s):** Hold — all elements static at full opacity.
`;

    const result = resolveAuditSampleWindow(spec, {
      sectionDurationSeconds: 10.752,
      fps: 30,
    });

    expect(result.source).toBe("frame-range");
    expect(result.startSeconds).toBeCloseTo(65 / 30);
    expect(result.endSeconds).toBeCloseTo(90 / 30);
    expect(result.sampleSeconds).toBeCloseTo(77.5 / 30);
  });

  it("treats animation-sequence frame ranges as offsets within the timestamp window", () => {
    const spec = `
**Timestamp:** 0:03 - 0:08

## Animation Sequence
1. Frame 0-20: Circle appears.
2. Frame 20-40: Hold at full size.
3. Frame 40-60: Pulse.
4. Frame 60-90: Circle holds steady.
5. Frame 90-150: Circle remains on screen.
`;

    const result = resolveAuditSampleWindow(spec, {
      sectionDurationSeconds: 10.752,
      fps: 30,
    });

    expect(result.source).toBe("frame-range");
    expect(result.startSeconds).toBeCloseTo(6);
    expect(result.endSeconds).toBeCloseTo(8);
    expect(result.sampleSeconds).toBeCloseTo(7);
  });

  it("parses frame ranges that include parenthetical time hints before the colon", () => {
    const spec = `
**Timestamp:** 0:21 - 0:26

## Animation Sequence
1. Frame 0-20 (0-0.67s): Title fades in.
2. Frame 15-40 (0.5-1.33s): Node 1 scales in.
3. Frame 35-55 (1.17-1.83s): Arrow 1 draws.
4. Frame 50-75 (1.67-2.5s): Node 2 scales in.
5. Frame 70-90 (2.33-3s): Arrow 2 draws.
6. Frame 85-110 (2.83-3.67s): Node 3 scales in.
7. Frame 110-130 (3.67-4.33s): Descriptor 3 fades in.
8. Frame 130-150 (4.33-5s): Hold complete diagram.
`;

    const result = resolveAuditSampleWindow(spec, {
      sectionDurationSeconds: 30,
      fps: 30,
    });

    expect(result.source).toBe("frame-range");
    expect(result.startSeconds).toBeCloseTo(25.333, 3);
    expect(result.endSeconds).toBeCloseTo(26, 3);
    expect(result.sampleSeconds).toBeCloseTo(25.666, 3);
  });

  it("clamps local frame offsets to the end of the timestamp window", () => {
    const spec = `
**Timestamp:** 0:03 - 0:06

## Animation Sequence
1. Frame 0-120: Long clip that overruns the timestamp window.
`;

    const result = resolveAuditSampleWindow(spec, {
      sectionDurationSeconds: 12,
      fps: 30,
    });

    expect(result.source).toBe("frame-range");
    expect(result.startSeconds).toBeCloseTo(3);
    expect(result.endSeconds).toBeCloseTo(6);
    expect(result.sampleSeconds).toBeCloseTo(4.5);
  });

  it("falls back to section midpoint when the spec has no timing metadata", () => {
    const result = resolveAuditSampleWindow("No timing metadata here.", {
      sectionDurationSeconds: 12.5,
      fps: 30,
    });

    expect(result.source).toBe("fallback");
    expect(result.sampleSeconds).toBeCloseTo(6.25);
  });

  it("clamps the sample window to the section duration", () => {
    const spec = `
**Timestamp:** 0:08 - 0:20
`;

    const result = resolveAuditSampleWindow(spec, {
      sectionDurationSeconds: 10,
      fps: 30,
    });

    expect(result.source).toBe("timestamp");
    expect(result.startSeconds).toBeCloseTo(8);
    expect(result.endSeconds).toBeCloseTo(9.999);
    expect(result.sampleSeconds).toBeCloseTo(9.49925);
  });
});

describe("resolveRenderedAuditSampleWindow", () => {
  let tmpDir: string;

  beforeEach(() => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "audit-timing-"));
  });

  afterEach(() => {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  });

  it("uses the resolved rendered visual window for specs that map directly to a section composition", () => {
    const specDir = path.join(tmpDir, "specs", "animation_section");
    fs.mkdirSync(specDir, { recursive: true });
    const titleCardPath = path.join(specDir, "01_title_card.md");
    fs.writeFileSync(
      titleCardPath,
      [
        "**Timestamp:** 0:00 - 0:03",
        "",
        "## Animation Sequence",
        "1. Frame 0-15: Fade in.",
        "2. Frame 15-45: Title reveal.",
        "3. Frame 45-65: Rule expansion.",
        "4. Frame 65-90: Hold — all elements static at full opacity.",
      ].join("\n")
    );
    fs.writeFileSync(
      path.join(specDir, "02_blue_circle_pulse.md"),
      "**Timestamp:** 0:03 - 0:08\n"
    );

    const result = resolveRenderedAuditSampleWindow(
      fs.readFileSync(titleCardPath, "utf-8"),
      {
        projectDir: tmpDir,
        specPath: titleCardPath,
        section: {
          id: "animation_section",
          specDir: "animation_section",
          compositionId: "AnimationSection",
          durationSeconds: 6,
          offsetSeconds: 0,
          videoFile: "animation_section.mp4",
          remotionDir: "S00-AnimationSection",
          compositions: [
            "animation_section_01_title_card",
            "02_blue_circle_pulse",
          ],
          label: "Animation Section",
        },
        fps: 30,
      }
    );

    expect(result.source).toBe("frame-range");
    expect(result.startSeconds).toBeCloseTo(0);
    expect(result.endSeconds).toBeCloseTo(2.25);
    expect(result.sampleSeconds).toBeCloseTo(1.889, 3);
    expect(result.intrinsicDurationSeconds).toBeCloseTo(3, 3);
    expect(result.intrinsicSampleSeconds).toBeCloseTo((77.5 / 30) - 0.0005, 3);
    expect(result.intrinsicDurationFrames).toBe(90);
    expect(result.intrinsicSampleFrame).toBe(77);
  });

  it("falls back to the raw spec timing when the spec is not part of the rendered visual graph", () => {
    const specDir = path.join(tmpDir, "specs", "veo_section");
    fs.mkdirSync(specDir, { recursive: true });
    fs.writeFileSync(
      path.join(specDir, "01_title_card.md"),
      "**Timestamp:** 0:00 - 0:03\n"
    );
    const oceanPath = path.join(specDir, "02_ocean_wave_sunset.md");
    fs.writeFileSync(
      oceanPath,
      "**Timestamp:** 0:03 - 0:06\n"
    );
    fs.writeFileSync(
      path.join(specDir, "03_narration_overlay_intro.md"),
      "**Timestamp:** 0:06 - 0:09\n"
    );

    const result = resolveRenderedAuditSampleWindow(
      fs.readFileSync(oceanPath, "utf-8"),
      {
        projectDir: tmpDir,
        specPath: oceanPath,
        section: {
          id: "veo_section",
          specDir: "veo_section",
          compositionId: "VeoSection",
          durationSeconds: 6,
          offsetSeconds: 0,
          videoFile: "veo_section.mp4",
          remotionDir: "S01-VeoSection",
          compositions: [
            "veo_section_01_title_card",
            "03_narration_overlay_intro",
          ],
          label: "Veo Section",
        },
        fps: 30,
      }
    );

    expect(result.source).toBe("timestamp");
    expect(result.startSeconds).toBeCloseTo(3);
    expect(result.endSeconds).toBeCloseTo(6);
    expect(result.sampleSeconds).toBeCloseTo(5.25);
  });

  it("uses the final hold frame range when the rendered spec includes parenthetical timing hints", () => {
    const specDir = path.join(tmpDir, "specs", "veo_section");
    fs.mkdirSync(specDir, { recursive: true });
    fs.writeFileSync(
      path.join(specDir, "01_title_card.md"),
      "**Timestamp:** 0:00 - 0:08\n"
    );
    const infographicPath = path.join(specDir, "06_veo_pipeline_infographic.md");
    fs.writeFileSync(
      infographicPath,
      [
        "**Timestamp:** 0:21 - 0:26",
        "",
        "## Animation Sequence",
        "1. Frame 0-20 (0-0.67s): Title fades in.",
        "2. Frame 15-40 (0.5-1.33s): Node 1 scales in.",
        "3. Frame 35-55 (1.17-1.83s): Arrow 1 draws.",
        "4. Frame 50-75 (1.67-2.5s): Node 2 scales in.",
        "5. Frame 70-90 (2.33-3s): Arrow 2 draws.",
        "6. Frame 85-110 (2.83-3.67s): Node 3 scales in.",
        "7. Frame 110-130 (3.67-4.33s): Descriptor 3 fades in.",
        "8. Frame 130-150 (4.33-5s): Hold complete diagram.",
      ].join("\n")
    );

    const result = resolveRenderedAuditSampleWindow(
      fs.readFileSync(infographicPath, "utf-8"),
      {
        projectDir: tmpDir,
        specPath: infographicPath,
        section: {
          id: "veo_section",
          specDir: "veo_section",
          compositionId: "VeoSection",
          durationSeconds: 7.424,
          offsetSeconds: 0,
          videoFile: "veo_section.mp4",
          remotionDir: "S01-VeoSection",
          compositions: [
            "veo_section_01_title_card",
            "06_veo_pipeline_infographic",
          ],
          label: "Veo Section",
        },
        fps: 30,
      }
    );

    expect(result.source).toBe("frame-range");
    expect(result.startSeconds).toBeCloseTo(5.996, 3);
    expect(result.endSeconds).toBeCloseTo(7.424, 3);
    expect(result.sampleSeconds).toBeGreaterThan(6.7);
  });
});

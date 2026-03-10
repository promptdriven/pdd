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

  it("prefers the final stable range over a trailing fade-out range", () => {
    const spec = `
**Timestamp:** 0:06 - 0:09

## Animation Sequence
1. Frame 0-15: Pill fades in.
2. Frame 15-75: Progress bar fills while the overlay remains visible.
3. Frame 75-90: Entire overlay fades out to 0% opacity.
`;

    const result = resolveAuditSampleWindow(spec, {
      sectionDurationSeconds: 12,
      fps: 30,
    });

    expect(result.source).toBe("frame-range");
    expect(result.startSeconds).toBeCloseTo(6.5);
    expect(result.endSeconds).toBeCloseTo(8.5);
    expect(result.sampleSeconds).toBeCloseTo(7.5);
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
    expect(result.startSeconds).toBeCloseTo(1.625);
    expect(result.endSeconds).toBeCloseTo(2.25);
    expect(result.sampleSeconds).toBeCloseTo(1.9);
  });

  it("falls back to a normalized spec timeline for specs not present in section.compositions", () => {
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
    expect(result.startSeconds).toBeCloseTo(2);
    expect(result.endSeconds).toBeCloseTo(4);
    expect(result.sampleSeconds).toBeCloseTo(3.5);
  });

  it("uses the authored timestamp duration when mapping a rendered slot for late section visuals", () => {
    const specDir = path.join(tmpDir, "specs", "animation_section");
    fs.mkdirSync(specDir, { recursive: true });
    const closingCardPath = path.join(specDir, "07_section_closing_card.md");
    fs.writeFileSync(
      closingCardPath,
      [
        "**Timestamp:** 0:27 - 0:30",
        "",
        "## Animation Sequence",
        "1. Frame 0-15: Horizontal rule expands from center.",
        "2. Frame 15-35: Section text fades in.",
        "3. Frame 30-45: Decorative shapes pop in.",
        "4. Frame 45-65: Hold — all elements visible.",
        "5. Frame 65-90: All elements fade out to black.",
      ].join("\n")
    );

    const result = resolveRenderedAuditSampleWindow(
      fs.readFileSync(closingCardPath, "utf-8"),
      {
        projectDir: tmpDir,
        specPath: closingCardPath,
        section: {
          id: "animation_section",
          specDir: "animation_section",
          compositionId: "AnimationSection",
          durationSeconds: 10.88,
          offsetSeconds: 0,
          videoFile: "animation_section.mp4",
          remotionDir: "S00-AnimationSection",
          compositions: ["07_section_closing_card"],
          label: "Animation Section",
        },
        fps: 30,
      }
    );

    expect(result.source).toBe("frame-range");
    expect(result.startSeconds).toBeCloseTo(9.792 + 1.088 * 0.5, 3);
    expect(result.endSeconds).toBeCloseTo(9.792 + 1.088 * (65 / 90), 2);
    expect(result.sampleSeconds).toBeCloseTo(
      9.792 + 1.088 * ((45 / 90 + 65 / 90) / 2),
      2
    );
  });

  it("keeps very short rendered-slot samples away from the trailing cut boundary", () => {
    const specDir = path.join(tmpDir, "specs", "veo_section");
    fs.mkdirSync(specDir, { recursive: true });
    fs.writeFileSync(
      path.join(specDir, "11_veo_badge_reprise.md"),
      "**Timestamp:** 0:00 - 0:01\n"
    );
    const reprisePath = path.join(specDir, "12_split_ocean_forest_reprise.md");
    fs.writeFileSync(
      reprisePath,
      [
        "**Timestamp:** 0:01 - 0:02",
        "",
        "## Animation Sequence",
        "1. Frame 0-30: Ocean plate holds.",
        "2. Frame 30-75: Wipe reveal into forest.",
        "3. Frame 75-90: Hold — both plates visible before cut.",
      ].join("\n")
    );
    fs.writeFileSync(
      path.join(specDir, "13_veo_technology_reprise.md"),
      "**Timestamp:** 0:02 - 0:03\n"
    );

    const result = resolveRenderedAuditSampleWindow(
      fs.readFileSync(reprisePath, "utf-8"),
      {
        projectDir: tmpDir,
        specPath: reprisePath,
        section: {
          id: "veo_section",
          specDir: "veo_section",
          compositionId: "VeoSection",
          durationSeconds: 3,
          offsetSeconds: 0,
          videoFile: "veo_section.mp4",
          remotionDir: "S01-VeoSection",
          compositions: [
            "11_veo_badge_reprise",
            "12_split_ocean_forest_reprise",
            "13_veo_technology_reprise",
          ],
          label: "Veo Section",
        },
        fps: 30,
      }
    );

    expect(result.source).toBe("frame-range");
    expect(result.startSeconds).toBeCloseTo(1, 2);
    expect(result.endSeconds).toBeCloseTo(2, 2);
    expect(result.sampleSeconds).toBeGreaterThan(1.3);
    expect(result.sampleSeconds).toBeLessThan(1.95);
    expect(result.sampleSeconds).toBeCloseTo(1.5, 1);
  });
});

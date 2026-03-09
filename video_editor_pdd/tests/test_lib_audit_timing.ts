import { resolveAuditSampleWindow } from "../lib/audit-timing";

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

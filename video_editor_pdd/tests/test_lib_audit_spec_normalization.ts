import {
  detectSpecResolution,
  normalizeSpecForAudit,
} from "../lib/audit-spec-normalization";

describe("audit spec normalization", () => {
  it("detects the declared resolution from spec markdown", () => {
    expect(detectSpecResolution("- Resolution: 1920x1080 (16:9)")).toEqual({
      width: 1920,
      height: 1080,
    });
  });

  it("returns the original spec when no resolution is declared", () => {
    const content = "## Visual Elements\n- No explicit canvas resolution";
    expect(
      normalizeSpecForAudit(content, { width: 1280, height: 720 })
    ).toBe(content);
  });

  it("normalizes 1920x1080 canvas coordinates to the active project resolution", () => {
    const spec = `
### Canvas
- Resolution: 1920x1080 (16:9)

### Visual Elements
- Wave path spans the full 1920px width at y=540
- Accent dots at x=480, x=960, and x=1440
- Label anchored at (300, 780)
`.trim();

    const normalized = normalizeSpecForAudit(spec, {
      width: 1280,
      height: 720,
    });

    expect(normalized).toContain("Resolution: 1280x720");
    expect(normalized).toContain("1280px width");
    expect(normalized).toContain("y=360");
    expect(normalized).toContain("x=320");
    expect(normalized).toContain("x=640");
    expect(normalized).toContain("x=960");
    expect(normalized).toContain("(200, 520)");
  });
});

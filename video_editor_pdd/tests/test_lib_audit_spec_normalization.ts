import {
  buildClaudeAuditSpecSnapshot,
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

  it("strips stale annotation update blocks from the normalized audit snapshot", () => {
    const spec = `
### Canvas
- Resolution: 1920x1080 (16:9)

### Visual Elements
- Shape centered at (960, 540)

<!-- ANNOTATION_UPDATE_START: demo -->
## Annotation Update
Requested change: The shape is vertically off-center.
Technical assessment: The previous review thought the shape sat at y≈410.
<!-- ANNOTATION_UPDATE_END: demo -->
`.trim();

    const normalized = normalizeSpecForAudit(spec, {
      width: 1920,
      height: 1080,
    });

    expect(normalized).toContain("Shape centered at (960, 540)");
    expect(normalized).not.toContain("## Annotation Update");
    expect(normalized).not.toContain("y≈410");
  });

  it("builds a Claude-facing audit snapshot with relative layout descriptions instead of pixel anchors", () => {
    const spec = `
### Canvas
- Resolution: 1920x1080 (16:9)

### Visual Elements
- Shape centered at (960, 540)
- Wave path spans the full 1920px width at y=540
- Accent dots at x=480, x=960, and x=1440
- Label anchored at (300, 780)
`.trim();

    const snapshot = buildClaudeAuditSpecSnapshot(spec, {
      width: 1920,
      height: 1080,
    });

    expect(snapshot).toContain("Shape visually centered on the canvas");
    expect(snapshot).toContain("full frame width");
    expect(snapshot).toContain("expected vertical anchor");
    expect(snapshot).toContain("expected horizontal anchor");
    expect(snapshot).toContain("Label anchored at (intended anchor position)");
    expect(snapshot).not.toContain("(960, 540)");
    expect(snapshot).not.toContain("x=480");
    expect(snapshot).not.toContain("y=540");
  });

  it("keeps the structured visual contract while stripping code structure from the Claude-facing snapshot", () => {
    const spec = `
### Canvas
- Resolution: 1920x1080 (16:9)

### Chart/Visual Elements
- Node 1 centered at x=330, y=480

## Code Structure
\`\`\`typescript
<PipelineNode x={330} />
\`\`\`

## Data Points
\`\`\`json
{ "pipeline_steps": [{ "label": "Prompt", "x": 330 }] }
\`\`\`
`.trim();

    const snapshot = buildClaudeAuditSpecSnapshot(spec, {
      width: 1920,
      height: 1080,
    });

    expect(snapshot).toContain("expected horizontal anchor");
    expect(snapshot).not.toContain("<PipelineNode x={330} />");
    expect(snapshot).toContain("## Structured Visual Contract (authoritative)");
    expect(snapshot).toContain(
      "When descriptive prose and structured contract details disagree, trust this structured contract."
    );
    expect(snapshot).toContain('"x": "expected horizontal anchor"');
    expect(snapshot).not.toContain("## Code Structure");
    expect(snapshot).not.toContain("## Data Points");
  });
});

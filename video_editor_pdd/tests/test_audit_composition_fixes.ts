/**
 * Tests for audit-identified composition fixes.
 *
 * These tests verify fixes for general rendering issues found by the audit stage:
 *   1. Unicode escape sequences must render as actual characters, not literal \uXXXX
 *   2. Background colors must match spec values
 *   3. Chart curves must follow spec direction (HIGH→LOW for inverse decay)
 *   4. SVG glow filters must have expanded bounds to prevent clipping
 *   5. Typewriter animations must complete within their allocated frame window
 */

import fs from "fs";
import path from "path";

const REMOTION_SRC = path.join(
  __dirname,
  "..",
  "remotion",
  "src",
  "remotion"
);

// ---------------------------------------------------------------------------
// 1. Unicode escape sequences — must use actual characters, not \uXXXX
// ---------------------------------------------------------------------------

describe("Unicode characters in annotation components", () => {
  const filePath = path.join(
    REMOTION_SRC,
    "Part1Economics04ResearchAnnotations",
    "Part1Economics04ResearchAnnotations.tsx"
  );
  let source: string;

  beforeAll(() => {
    source = fs.readFileSync(filePath, "utf-8");
  });

  it("uses actual minus sign (−) instead of literal \\u2212", () => {
    expect(source).not.toMatch(/\\u2212/);
    expect(source).toContain("−"); // U+2212 MINUS SIGN
  });

  it("uses actual bullet (•) instead of literal \\u2022", () => {
    expect(source).not.toMatch(/\\u2022/);
    expect(source).toContain("•"); // U+2022 BULLET
  });
});

// ---------------------------------------------------------------------------
// 2. Background color — PDD title card must use spec color #0A0F1A
// ---------------------------------------------------------------------------

describe("PDD title card background color", () => {
  const filePath = path.join(
    REMOTION_SRC,
    "ColdOpen07PddTitleCard",
    "constants.ts"
  );
  let source: string;

  beforeAll(() => {
    source = fs.readFileSync(filePath, "utf-8");
  });

  it("uses #0A0F1A for BACKGROUND (spec requirement)", () => {
    expect(source).toMatch(/BACKGROUND:\s*['"]#0A0F1A['"]/);
  });

  it("does not use the wrong gray #0D1117 for BACKGROUND", () => {
    expect(source).not.toMatch(/BACKGROUND:\s*['"]#0D1117['"]/);
  });
});

// ---------------------------------------------------------------------------
// 3. Curve direction — inverse hyperbola must start HIGH and drop LOW
// ---------------------------------------------------------------------------

describe("Precision tradeoff curve direction", () => {
  const filePath = path.join(
    REMOTION_SRC,
    "Part4PrecisionTradeoff03PrecisionTradeoffCurve",
    "constants.ts"
  );

  // Import the actual functions to test their output
  let curvePoint: (testCount: number) => { x: number; y: number };

  beforeAll(() => {
    // eslint-disable-next-line @typescript-eslint/no-var-requires
    const mod = require(filePath);
    curvePoint = mod.curvePoint;
  });

  it("returns HIGH y-value (low pixel number) at testCount=0 (few tests)", () => {
    const point = curvePoint(0);
    // At 0 tests, y should be near the top of the chart (small pixel value ~180)
    expect(point.y).toBeLessThan(300);
  });

  it("returns LOW y-value (high pixel number) at testCount=50 (many tests)", () => {
    const point = curvePoint(50);
    // At 50 tests, y should be near the bottom of the chart (large pixel value ~700+)
    expect(point.y).toBeGreaterThan(600);
  });

  it("curve goes from high to low (y increases as testCount increases)", () => {
    const yAt0 = curvePoint(0).y;
    const yAt25 = curvePoint(25).y;
    const yAt50 = curvePoint(50).y;
    // In screen coordinates, increasing y = moving down = lower precision
    expect(yAt25).toBeGreaterThan(yAt0);
    expect(yAt50).toBeGreaterThan(yAt25);
  });
});

// ---------------------------------------------------------------------------
// 4. SVG glow filter bounds — must extend beyond path to avoid clipping
// ---------------------------------------------------------------------------

describe("SVG glow filter bounds in triangle compositions", () => {
  it("Closing06 TriangleGlow.tsx has expanded filter bounds", () => {
    const filePath = path.join(
      REMOTION_SRC,
      "Closing06MoldGlowFinale",
      "TriangleGlow.tsx"
    );
    const source = fs.readFileSync(filePath, "utf-8");
    // Filter must have x/y/width/height attributes to prevent clipping
    expect(source).toMatch(/x="-50%"\s+y="-50%"\s+width="200%"\s+height="200%"/);
  });
});

// ---------------------------------------------------------------------------
// 5. Typewriter animation speed — must complete within frame window
// ---------------------------------------------------------------------------

describe("Code regeneration typewriter speed", () => {
  const filePath = path.join(
    REMOTION_SRC,
    "ColdOpen07CodeRegeneration",
    "constants.ts"
  );
  let source: string;
  let CHARS_PER_SECOND: number;
  let REGEN_START: number;
  let REGEN_END: number;
  let FPS: number;
  let CODE_LINES: string[];

  beforeAll(() => {
    // eslint-disable-next-line @typescript-eslint/no-var-requires
    const mod = require(filePath);
    source = fs.readFileSync(filePath, "utf-8");
    CHARS_PER_SECOND = mod.CHARS_PER_SECOND;
    REGEN_START = mod.REGEN_START;
    REGEN_END = mod.REGEN_END;
    FPS = mod.FPS;
    CODE_LINES = mod.CLEAN_CODE_LINES || mod.NEW_CODE_LINES;
  });

  it("can type all code lines within the regeneration frame window", () => {
    const regenFrames = REGEN_END - REGEN_START;
    const charsPerFrame = CHARS_PER_SECOND / FPS;
    const maxChars = regenFrames * charsPerFrame;

    // Total characters needed (each line + newline)
    const totalChars = CODE_LINES.reduce(
      (sum, line) => sum + Math.max(line.length, 1) + 1,
      0
    );

    expect(maxChars).toBeGreaterThanOrEqual(totalChars);
  });
});

// ---------------------------------------------------------------------------
// 6. useVisualMediaSrc must NOT fall back to defaultSrc for split-specific keys
// ---------------------------------------------------------------------------

describe("Visual media src fallback for split keys", () => {
  const filePath = path.join(
    REMOTION_SRC,
    "_shared",
    "visual-runtime.tsx"
  );
  let source: string;

  beforeAll(() => {
    source = fs.readFileSync(filePath, "utf-8");
  });

  it("guards leftSrc/rightSrc from falling back to defaultSrc", () => {
    // Without this guard, leftSrc/rightSrc resolve to defaultSrc when undefined,
    // making isSplitVisual true and duplicating the video side-by-side.
    expect(source).toContain("SPLIT_ONLY_KEYS");
    expect(source).toMatch(/leftSrc/);
    expect(source).toMatch(/rightSrc/);
    expect(source).toMatch(/SPLIT_ONLY_KEYS\.has\(key\)/);
  });
});

// ---------------------------------------------------------------------------
// 7. Audit annotation sectionId must not be overridden by video playhead
// ---------------------------------------------------------------------------

describe("Audit annotation sectionId preservation", () => {
  const filePath = path.join(__dirname, "..", "app", "page.tsx");
  let source: string;

  beforeAll(() => {
    source = fs.readFileSync(filePath, "utf-8");
  });

  it("preserves explicitly provided sectionId from audit instead of overriding with playhead position", () => {
    // When options.sectionId is explicitly provided (e.g. from audit page),
    // effectiveSectionId must use captureSectionId directly instead of
    // recalculating from the video playhead via resolveSectionIdForGlobalTime.
    const fnBody = source.slice(
      source.indexOf("effectiveSectionId"),
      source.indexOf("effectiveSectionId") + 300
    );
    expect(fnBody).toMatch(/options\?\.sectionId/);
  });
});

// ---------------------------------------------------------------------------
// 8. Spec file fallback uses first file, not last
// ---------------------------------------------------------------------------

describe("Remotion spec fix fallback", () => {
  const filePath = path.join(
    __dirname,
    "..",
    "lib",
    "remotion-spec-fix.ts"
  );
  let source: string;

  beforeAll(() => {
    source = fs.readFileSync(filePath, "utf-8");
  });

  it("falls back to the first spec file when no timestamp match is found", () => {
    // The fallback should use specFiles[0] (first/title card), not
    // specFiles[specFiles.length - 1] (last), to avoid polluting
    // unrelated spec files with annotation notes.
    expect(source).toMatch(/specFiles\[0\]/);
    expect(source).not.toMatch(/specFiles\[specFiles\.length\s*-\s*1\]/);
  });
});

// ---------------------------------------------------------------------------
// 9. Batch resolve must limit concurrent jobs
// ---------------------------------------------------------------------------

describe("Batch resolve concurrency control", () => {
  it("resolve-batch route has a concurrency guard to prevent server overload", () => {
    const routePath = path.join(
      REMOTION_SRC,
      "..",
      "..",
      "..",
      "app",
      "api",
      "sections",
      "[id]",
      "resolve-batch",
      "route.ts"
    );
    const source = fs.readFileSync(routePath, "utf-8");
    // Must have some form of concurrency control
    expect(source).toMatch(/maxParallelResolves|activeResolveCount|resolveSemaphore|RESOLVE_CONCURRENCY/);
  });
});

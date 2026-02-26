/**
 * Tests for components/FixPreviewPanel.tsx
 *
 * Verifies that the FixPreviewPanel renders safely when the API response
 * includes preview objects whose optional `filesModified` field is undefined
 * or missing (defensive null guard).
 */

import fs from "fs";
import path from "path";

const SOURCE_PATH = path.join(
  __dirname,
  "..",
  "components",
  "FixPreviewPanel.tsx"
);
const sourceCode = fs.readFileSync(SOURCE_PATH, "utf-8");

// ---------------------------------------------------------------------------
// 1. Module structure
// ---------------------------------------------------------------------------

describe("FixPreviewPanel module structure", () => {
  it("file exists at expected path", () => {
    expect(fs.existsSync(SOURCE_PATH)).toBe(true);
  });

  it("has 'use client' as the very first line", () => {
    const firstLine = sourceCode.split("\n")[0].trim();
    expect(firstLine).toBe("'use client';");
  });

  it("exports FixPreviewPanel as default export", () => {
    expect(sourceCode).toMatch(
      /export\s+default\s+function\s+FixPreviewPanel/
    );
  });
});

// ---------------------------------------------------------------------------
// 2. filesModified null-safety (Bug: undefined crash on p.filesModified.length)
// ---------------------------------------------------------------------------

describe("filesModified null-safety", () => {
  it("does not access filesModified.length without a null guard", () => {
    // If the code uses `p.filesModified.length` (without optional chaining),
    // it will crash when the API omits the field.  The fix is to use
    // `p.filesModified?.length` or an equivalent guard.
    const unsafePattern = /p\.filesModified\.length/;
    expect(sourceCode).not.toMatch(unsafePattern);
  });

  it("uses optional chaining or equivalent guard for filesModified access", () => {
    // Acceptable patterns:
    //   p.filesModified?.length
    //   (p.filesModified ?? []).length
    //   p.filesModified && p.filesModified.length
    const safePatterns = [
      /p\.filesModified\?\.length/,
      /\(p\.filesModified\s*\?\?\s*\[\]\)\.length/,
      /p\.filesModified\s*&&\s*p\.filesModified\.length/,
    ];
    const hasSafePattern = safePatterns.some((re) => re.test(sourceCode));
    expect(hasSafePattern).toBe(true);
  });

  it("uses optional chaining or equivalent guard when joining filesModified", () => {
    // Similarly, p.filesModified.join(...) must be guarded.
    // Acceptable: p.filesModified?.join or (p.filesModified ?? []).join
    const unsafeJoin = /p\.filesModified\.join/;
    expect(sourceCode).not.toMatch(unsafeJoin);
  });
});

// ---------------------------------------------------------------------------
// 3. confidence NaN-safety (Bug: NaN% when confidence is undefined/null)
// ---------------------------------------------------------------------------

describe("confidence NaN-safety", () => {
  it("does not multiply p.confidence directly without a null/undefined guard", () => {
    // `p.confidence * 100` without a guard produces NaN when confidence is undefined.
    // The fix is `(p.confidence ?? 0) * 100` or similar.
    const unsafePattern = /Math\.round\(p\.confidence\s*\*\s*100\)/;
    expect(sourceCode).not.toMatch(unsafePattern);
  });

  it("uses null-coalescing or default fallback when computing confidence percentage", () => {
    // Acceptable patterns:
    //   (p.confidence ?? 0) * 100
    //   p.confidence != null ? p.confidence * 100 : 0
    const safePatterns = [
      /\(p\.confidence\s*\?\?\s*0\)\s*\*\s*100/,
      /p\.confidence\s*!=\s*null\s*\?/,
      /typeof\s+p\.confidence\s*===\s*['"]number['"]/,
    ];
    const hasSafePattern = safePatterns.some((re) => re.test(sourceCode));
    expect(hasSafePattern).toBe(true);
  });
});

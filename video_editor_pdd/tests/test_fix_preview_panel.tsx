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

// ---------------------------------------------------------------------------
// 4. Error state when fetch fails (item 12.2)
// ---------------------------------------------------------------------------

describe("error state when preview fetch fails (12.2)", () => {
  it("shows a red error box when the API returns a non-ok response", () => {
    // When fetch returns !res.ok, error state must be displayed.
    expect(sourceCode).toMatch(/error\s*\?/);
    // Red error styling
    expect(sourceCode).toMatch(/bg-red-500\/10/);
    expect(sourceCode).toMatch(/text-red-200/);
  });

  it("captures the error message from the thrown Error", () => {
    expect(sourceCode).toMatch(/Preview failed \(\$\{res\.status\}\)/);
  });

  it("renders the error message string in the error box", () => {
    // The {error} expression renders the caught error message
    expect(sourceCode).toMatch(/\{error\}/);
  });

  it("uses useState<string | null> for error state", () => {
    expect(sourceCode).toMatch(/useState\s*<\s*string\s*\|\s*null\s*>\s*\(\s*null\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 5. Empty state when no fixes to preview (item 12.3)
// ---------------------------------------------------------------------------

describe("empty state when no previews returned (12.3)", () => {
  it("renders 'No fixes to preview.' when previews array is empty", () => {
    expect(sourceCode).toMatch(/No fixes to preview\./);
  });

  it("checks previews.length === 0 for empty state", () => {
    expect(sourceCode).toMatch(/previews\.length\s*===\s*0/);
  });

  it("empty state is separate from error state", () => {
    // error ? <error box> : previews.length === 0 ? <empty msg> : <list>
    const errorIndex = sourceCode.indexOf('bg-red-500/10');
    const emptyIndex = sourceCode.indexOf('No fixes to preview.');
    expect(errorIndex).toBeGreaterThan(-1);
    expect(emptyIndex).toBeGreaterThan(-1);
    // empty state renders after error check
    expect(emptyIndex).toBeGreaterThan(errorIndex);
  });
});

// ---------------------------------------------------------------------------
// 6. Preview card content (items 12.7–12.10)
// ---------------------------------------------------------------------------

describe("preview card content (12.7–12.10)", () => {
  it("renders preview text description for each fix (12.7)", () => {
    // p.preview is shown as the description text
    expect(sourceCode).toMatch(/\{p\.preview\}/);
  });

  it("renders files modified list when present (12.8)", () => {
    // filesModified row is only shown when there are files
    expect(sourceCode).toMatch(/p\.filesModified\?\.length/);
    expect(sourceCode).toMatch(/Files:/);
  });

  it("renders 'Show diff' / 'Hide diff' toggle link when diff exists (12.9)", () => {
    expect(sourceCode).toMatch(/Show diff/);
    expect(sourceCode).toMatch(/Hide diff/);
    // Link is only rendered when p.diff is truthy
    expect(sourceCode).toMatch(/p\.diff\s*\?/);
  });

  it("diff viewer uses <pre> with font-mono for monospaced rendering (12.10)", () => {
    expect(sourceCode).toMatch(/<pre\s[^>]*font-mono/);
  });

  it("diff toggle is keyed per annotationId via expandedDiffs set", () => {
    expect(sourceCode).toMatch(/expandedDiffs/);
    expect(sourceCode).toMatch(/expandedDiffs\.has\(p\.annotationId\)/);
  });
});

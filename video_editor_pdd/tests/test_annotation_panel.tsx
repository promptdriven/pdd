/**
 * Tests for components/AnnotationPanel.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/annotation_panel_typescriptreact.prompt.
 *
 * Spec requirements verified:
 *   1. Props: annotations: Annotation[], sectionId: string, onBatchResolve: (jobId: string) => void
 *   2. Renders a scrollable list of annotation cards sorted by timestamp ascending.
 *   3. Each card shows: timestamp (MM:SS.ms), thumbnail (80×45px), text (2-line truncate), severity badge, fix type badge, analysis summary (1 line).
 *   4. Cards expand on click to show technicalAssessment, suggestedFixes list, [Retry] / [Mark Resolved] / [Delete] actions.
 *   5. [Apply N Fixes] button — N = unresolved annotations with non-null analysis. POSTs to /api/sections/${sectionId}/resolve-batch. Shows SseLogPanel.
 *   6. Resolving annotations (resolveJobId set): inline progress spinner with job status from SSE.
 *   7. Resolved annotations: green ✓ Resolved badge. Collapsed by default.
 *   8. Failed annotations: [Retry] button that POSTs to /api/jobs/${annotation.resolveJobId}/retry.
 *   9. 'use client' directive.
 *  10. Severity badge colors: critical=red, major=orange, minor=yellow, pass=green.
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "components", "AnnotationPanel.tsx");
const sourceCode = fs.readFileSync(SOURCE_PATH, "utf-8");

// ---------------------------------------------------------------------------
// 1. 'use client' directive
// ---------------------------------------------------------------------------

describe("'use client' directive", () => {
  it("has 'use client' as the very first line", () => {
    const firstLine = sourceCode.split("\n")[0].trim();
    expect(firstLine).toBe("'use client';");
  });
});

// ---------------------------------------------------------------------------
// 2. Module structure
// ---------------------------------------------------------------------------

describe("module structure", () => {
  it("file exists at expected path", () => {
    expect(fs.existsSync(SOURCE_PATH)).toBe(true);
  });

  it("is a TypeScript React file", () => {
    expect(SOURCE_PATH).toMatch(/\.tsx$/);
  });

  it("exports AnnotationPanel as default export", () => {
    expect(sourceCode).toMatch(/export\s+default\s+function\s+AnnotationPanel/);
  });
});

// ---------------------------------------------------------------------------
// 3. Props interface
// ---------------------------------------------------------------------------

describe("AnnotationPanel props", () => {
  it("declares annotations: Annotation[] prop", () => {
    expect(sourceCode).toMatch(/annotations\s*:\s*Annotation\[\]/);
  });

  it("declares sectionId: string prop", () => {
    expect(sourceCode).toMatch(/sectionId\s*:\s*string/);
  });

  it("declares onBatchResolve callback prop", () => {
    expect(sourceCode).toMatch(/onBatchResolve\s*:\s*\(jobId\s*:\s*string\)\s*=>\s*void/);
  });
});

// ---------------------------------------------------------------------------
// 4. Import structure
// ---------------------------------------------------------------------------

describe("import structure", () => {
  it("imports React and hooks from react", () => {
    expect(sourceCode).toMatch(/import\s+React/);
    expect(sourceCode).toMatch(/useState/);
    expect(sourceCode).toMatch(/useMemo/);
  });

  it("imports Annotation type from ../lib/types", () => {
    expect(sourceCode).toMatch(/import\s+type\s*\{.*Annotation/);
    expect(sourceCode).toMatch(/from\s+['"]\.\.\/lib\/types['"]/);
  });

  it("imports SseLogPanel from ./SseLogPanel", () => {
    expect(sourceCode).toMatch(/import\s*\{.*SseLogPanel.*\}\s*from\s+['"]\.\/SseLogPanel['"]/);
  });
});

// ---------------------------------------------------------------------------
// 5. Severity badge color map (Req 10)
// ---------------------------------------------------------------------------

describe("severity badge colors", () => {
  it("defines severityColors mapping", () => {
    expect(sourceCode).toMatch(/severityColors/);
  });

  it("maps critical to bg-red-500", () => {
    expect(sourceCode).toMatch(/critical\s*:\s*['"]bg-red-500['"]/);
  });

  it("maps major to bg-orange-500", () => {
    expect(sourceCode).toMatch(/major\s*:\s*['"]bg-orange-500['"]/);
  });

  it("maps minor to bg-yellow-500", () => {
    expect(sourceCode).toMatch(/minor\s*:\s*['"]bg-yellow-500['"]/);
  });

  it("maps pass to bg-green-500", () => {
    expect(sourceCode).toMatch(/pass\s*:\s*['"]bg-green-500['"]/);
  });
});

// ---------------------------------------------------------------------------
// 6. Fix type label map
// ---------------------------------------------------------------------------

describe("fix type labels", () => {
  it("defines fixTypeLabels mapping", () => {
    expect(sourceCode).toMatch(/fixTypeLabels/);
  });

  it("maps remotion to 'Remotion Fix'", () => {
    expect(sourceCode).toMatch(/remotion\s*:\s*['"]Remotion Fix['"]/);
  });

  it("maps veo to 'Veo Regen'", () => {
    expect(sourceCode).toMatch(/veo\s*:\s*['"]Veo Regen['"]/);
  });

  it("maps tts to 'TTS Re-render'", () => {
    expect(sourceCode).toMatch(/tts\s*:\s*['"]TTS Re-render['"]/);
  });

  it("maps none to 'No Fix'", () => {
    expect(sourceCode).toMatch(/none\s*:\s*['"]No Fix['"]/);
  });
});

// ---------------------------------------------------------------------------
// 7. Timestamp format helper (Req 3)
// ---------------------------------------------------------------------------

describe("formatTs helper", () => {
  it("defines formatTs function", () => {
    expect(sourceCode).toMatch(/const\s+formatTs\s*=/);
  });

  it("calculates minutes with Math.floor(s / 60)", () => {
    expect(sourceCode).toMatch(/Math\.floor\s*\(\s*s\s*\/\s*60\s*\)/);
  });

  it("calculates seconds with (s % 60).toFixed(1)", () => {
    expect(sourceCode).toMatch(/\(s\s*%\s*60\)\.toFixed\s*\(\s*1\s*\)/);
  });

  it("pads seconds with padStart(4, '0')", () => {
    expect(sourceCode).toMatch(/padStart\s*\(\s*4\s*,\s*['"]0['"]\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 8. Sorting by timestamp ascending (Req 2)
// ---------------------------------------------------------------------------

describe("annotation sorting", () => {
  it("sorts annotations by timestamp ascending", () => {
    expect(sourceCode).toMatch(/\.sort\s*\(\s*\(a\s*,\s*b\)\s*=>\s*a\.timestamp\s*-\s*b\.timestamp\s*\)/);
  });

  it("uses useMemo for sorted annotations", () => {
    expect(sourceCode).toMatch(/useMemo\s*\(\s*\(\)\s*=>\s*\{[\s\S]*?\.sort/);
  });

  it("creates a new array copy before sorting (immutable)", () => {
    expect(sourceCode).toMatch(/\[\.\.\.annotations\]\.sort/);
  });
});

// ---------------------------------------------------------------------------
// 9. Annotation card display (Req 3)
// ---------------------------------------------------------------------------

describe("annotation card display", () => {
  it("renders thumbnail image with w-20 h-11 classes", () => {
    expect(sourceCode).toMatch(/className="w-20 h-11 object-cover rounded flex-shrink-0"/);
  });

  it("renders a placeholder when compositeDataUrl is missing", () => {
    expect(sourceCode).toMatch(/h-11\s+w-20\s+flex-shrink-0\s+rounded\s+bg-white\/5/);
  });

  it("displays formatted timestamp", () => {
    expect(sourceCode).toMatch(/formatTs\s*\(\s*a\.timestamp\s*\)/);
  });

  it("displays annotation text with 2-line truncation", () => {
    expect(sourceCode).toMatch(/line-clamp-2/);
  });

  it("displays analysis summary with 1-line truncation", () => {
    expect(sourceCode).toMatch(/line-clamp-1/);
  });

  it("shows severity badge", () => {
    expect(sourceCode).toMatch(/severity\s*\?\?\s*['"]unknown['"]/);
  });

  it("shows fix type label", () => {
    expect(sourceCode).toMatch(/fixLabel/);
  });
});

// ---------------------------------------------------------------------------
// 10. Card expand/collapse behavior (Req 4)
// ---------------------------------------------------------------------------

describe("card expand/collapse", () => {
  it("uses useState for expanded card state as Record<string, boolean>", () => {
    expect(sourceCode).toMatch(/useState\s*<\s*Record\s*<\s*string\s*,\s*boolean\s*>\s*>/);
  });

  it("has handleToggle function to toggle expanded state", () => {
    expect(sourceCode).toMatch(/handleToggle/);
  });

  it("button has aria-expanded attribute", () => {
    expect(sourceCode).toMatch(/aria-expanded=\{isExpanded\}/);
  });

  it("expanded card shows technical assessment section", () => {
    expect(sourceCode).toMatch(/Technical assessment/);
  });

  it("expanded card shows suggested fixes section", () => {
    expect(sourceCode).toMatch(/Suggested fixes/);
  });

  it("renders suggested fixes as a list", () => {
    expect(sourceCode).toMatch(/suggestedFixes\.map/);
  });

  it("shows Mark Resolved button when not resolved", () => {
    expect(sourceCode).toMatch(/Mark Resolved/);
  });

  it("shows Delete button in expanded actions", () => {
    expect(sourceCode).toMatch(/Delete/);
  });

  it("conditionally renders expanded content", () => {
    expect(sourceCode).toMatch(/\{isExpanded\s*\?/);
  });
});

// ---------------------------------------------------------------------------
// 11. Apply N Fixes batch button (Req 5)
// ---------------------------------------------------------------------------

describe("Apply N Fixes button", () => {
  it("renders Apply N Fixes button text", () => {
    expect(sourceCode).toMatch(/Apply\s*\$\{unresolvedWithAnalysisCount\}\s*Fixes/);
  });

  it("counts unresolved annotations with non-null analysis", () => {
    expect(sourceCode).toMatch(/!a\.resolved\s*&&\s*!locallyResolvedIds\.has\(a\.id\)\s*&&\s*a\.analysis\s*!==\s*null/);
  });

  it("button is disabled when count is 0", () => {
    expect(sourceCode).toMatch(/disabled=\{unresolvedWithAnalysisCount\s*===\s*0/);
  });

  it("button is disabled when batch job is in progress", () => {
    expect(sourceCode).toMatch(/Boolean\(batchJobId\)/);
  });

  it("POSTs to /api/sections/${sectionId}/resolve-batch", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*`\/api\/sections\/\$\{sectionId\}\/resolve-batch`/);
  });

  it("uses POST method for batch resolve", () => {
    expect(sourceCode).toMatch(/method\s*:\s*['"]POST['"]/);
  });

  it("calls onBatchResolve with jobId after successful POST", () => {
    expect(sourceCode).toMatch(/onBatchResolve\s*\(\s*data\.jobId\s*\)/);
  });

  it("shows Applying spinner text while posting", () => {
    expect(sourceCode).toMatch(/Applying…/);
  });
});

// ---------------------------------------------------------------------------
// 12. SseLogPanel integration (Req 5)
// ---------------------------------------------------------------------------

describe("SseLogPanel integration", () => {
  it("stores batchJobId in state", () => {
    expect(sourceCode).toMatch(/useState\s*<\s*string\s*\|\s*null\s*>\s*\(\s*null\s*\)/);
  });

  it("renders SseLogPanel when batchJobId is set", () => {
    expect(sourceCode).toMatch(/<SseLogPanel/);
  });

  it("passes batchJobId as jobId prop to SseLogPanel", () => {
    expect(sourceCode).toMatch(/jobId=\{batchJobId\}/);
  });

  it("provides onDone callback to SseLogPanel", () => {
    expect(sourceCode).toMatch(/onDone=\{/);
  });

  it("shows Batch Resolve Job label", () => {
    expect(sourceCode).toMatch(/Batch Resolve Job/);
  });

  it("displays the jobId in the batch panel", () => {
    expect(sourceCode).toMatch(/jobId:\s*\{batchJobId\}/);
  });
});

// ---------------------------------------------------------------------------
// 13. Resolved annotations (Req 7)
// ---------------------------------------------------------------------------

describe("resolved annotations", () => {
  it("shows green ✓ Resolved badge for resolved annotations", () => {
    expect(sourceCode).toMatch(/✓ Resolved/);
  });

  it("resolved badge uses green styling", () => {
    expect(sourceCode).toMatch(/bg-green-500\/20/);
    expect(sourceCode).toMatch(/text-green-200/);
  });

  it("resolved annotations have green border styling", () => {
    expect(sourceCode).toMatch(/border-green-500\/30\s+bg-green-500\/5/);
  });

  it("resolved annotations are collapsed by default", () => {
    expect(sourceCode).toMatch(/expanded\[a\.id\]\s*\?\?\s*false/);
  });

  it("supports local Mark Resolved state", () => {
    expect(sourceCode).toMatch(/locallyResolvedIds/);
    expect(sourceCode).toMatch(/handleMarkResolved/);
  });

  it("tracks locally deleted annotations", () => {
    expect(sourceCode).toMatch(/locallyDeletedIds/);
    expect(sourceCode).toMatch(/handleDeleteAnnotation/);
  });

  it("isResolved checks both a.resolved and isLocallyResolved", () => {
    expect(sourceCode).toMatch(/a\.resolved\s*\|\|\s*isLocallyResolved/);
  });
});

// ---------------------------------------------------------------------------
// 14. Inline progress spinner for resolving annotations (Req 6)
// ---------------------------------------------------------------------------

describe("inline progress spinner", () => {
  it("defines Spinner component", () => {
    expect(sourceCode).toMatch(/function\s+Spinner/);
  });

  it("Spinner has animate-spin class", () => {
    expect(sourceCode).toMatch(/animate-spin/);
  });

  it("Spinner has aria-label Loading", () => {
    expect(sourceCode).toMatch(/aria-label="Loading"/);
  });

  it("shows inline progress when resolveJobId is set and not terminal", () => {
    expect(sourceCode).toMatch(/showInlineProgress/);
  });

  it("displays job status text", () => {
    expect(sourceCode).toMatch(/job\?\.status\s*\?\?\s*['"]running['"]/);
  });

  it("displays job progress percentage when available", () => {
    expect(sourceCode).toMatch(/job\.progress/);
  });
});

// ---------------------------------------------------------------------------
// 15. useJob hook for per-annotation SSE (Req 6)
// ---------------------------------------------------------------------------

describe("useJob hook", () => {
  it("defines useJob hook", () => {
    expect(sourceCode).toMatch(/function\s+useJob/);
  });

  it("fetches job status from /api/jobs/${id}", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*`\/api\/jobs\/\$\{id\}`/);
  });

  it("opens EventSource at /api/jobs/${jobId}/stream", () => {
    expect(sourceCode).toMatch(/new\s+EventSource\s*\(\s*`\/api\/jobs\/\$\{jobId\}\/stream`\s*\)/);
  });

  it("uses polling fallback every 2 seconds", () => {
    expect(sourceCode).toMatch(/setInterval\s*\(\s*\(\)\s*=>\s*\{[\s\S]*?\}\s*,\s*2000\s*\)/);
  });

  it("cleans up EventSource on unmount", () => {
    expect(sourceCode).toMatch(/eventSourceRef\.current\?\.close\(\)/);
  });

  it("cleans up interval on unmount", () => {
    expect(sourceCode).toMatch(/clearInterval\s*\(\s*interval\s*\)/);
  });

  it("defines isTerminal helper for done/error status", () => {
    expect(sourceCode).toMatch(/function\s+isTerminal/);
    expect(sourceCode).toMatch(/status\s*===\s*['"]done['"]/);
    expect(sourceCode).toMatch(/status\s*===\s*['"]error['"]/);
  });
});

// ---------------------------------------------------------------------------
// 16. Failed annotation retry (Req 8)
// ---------------------------------------------------------------------------

describe("failed annotation retry", () => {
  it("shows Retry button when job has error status", () => {
    expect(sourceCode).toMatch(/showFailed/);
    expect(sourceCode).toMatch(/>\s*Retry\s*<\/button>/);
  });

  it("POSTs to /api/jobs/${jobId}/retry on retry", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*`\/api\/jobs\/\$\{jobId\}\/retry`\s*,\s*\{\s*method\s*:\s*['"]POST['"]\s*\}/);
  });

  it("handleRetryJob is async and handles errors", () => {
    expect(sourceCode).toMatch(/handleRetryJob\s*=\s*async/);
    expect(sourceCode).toMatch(/console\.error/);
  });
});

// ---------------------------------------------------------------------------
// 17. Delete annotation
// ---------------------------------------------------------------------------

describe("delete annotation", () => {
  it("defines handleDeleteAnnotation as an async function", () => {
    expect(sourceCode).toMatch(/handleDeleteAnnotation\s*=\s*async/);
  });

  it("POSTs a DELETE request to /api/annotations/${annotationId}", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*`\/api\/annotations\/\$\{annotationId\}`\s*,\s*\{\s*method\s*:\s*['"]DELETE['"]/);
  });

  it("confirms deletion before removing the annotation", () => {
    expect(sourceCode).toMatch(/window\.confirm/);
  });

  it("optimistically removes deleted annotations from the rendered list", () => {
    expect(sourceCode).toMatch(/sorted\s*=\s*useMemo/);
    expect(sourceCode).toMatch(/!locallyDeletedIds\.has\(a\.id\)/);
  });

  it("shows deleting state on the Delete button", () => {
    expect(sourceCode).toMatch(/Deleting\.\.\.|Deleting…/);
  });
});

// ---------------------------------------------------------------------------
// 18. Empty state
// ---------------------------------------------------------------------------

describe("empty state", () => {
  it("shows empty message when no annotations", () => {
    expect(sourceCode).toMatch(/No annotations yet\./);
  });

  it("checks sorted.length === 0", () => {
    expect(sourceCode).toMatch(/sorted\.length\s*===\s*0/);
  });
});

// ---------------------------------------------------------------------------
// 19. Scrollable container (Req 2)
// ---------------------------------------------------------------------------

describe("scrollable list container", () => {
  it("uses overflow-y-auto for scrollable list", () => {
    expect(sourceCode).toMatch(/overflow-y-auto/);
  });

  it("has flex-1 and min-h-0 for proper scrolling", () => {
    expect(sourceCode).toMatch(/min-h-0\s+flex-1/);
  });
});

// ---------------------------------------------------------------------------
// 20. AnnotationCard sub-component
// ---------------------------------------------------------------------------

describe("AnnotationCard sub-component", () => {
  it("defines AnnotationCard as a separate function component", () => {
    expect(sourceCode).toMatch(/function\s+AnnotationCard\s*\(/);
  });

  it("receives annotation prop", () => {
    expect(sourceCode).toMatch(/annotation\s*:\s*Annotation/);
  });

  it("receives isLocallyResolved prop", () => {
    expect(sourceCode).toMatch(/isLocallyResolved\s*:\s*boolean/);
  });

  it("receives defaultExpanded prop", () => {
    expect(sourceCode).toMatch(/defaultExpanded\s*:\s*boolean/);
  });

  it("receives onToggle callback", () => {
    expect(sourceCode).toMatch(/onToggle\s*:\s*\(\)\s*=>\s*void/);
  });

  it("receives onRetryJob callback", () => {
    expect(sourceCode).toMatch(/onRetryJob\s*:\s*\(jobId\s*:\s*string\)\s*=>\s*void/);
  });

  it("receives onMarkResolved callback", () => {
    expect(sourceCode).toMatch(/onMarkResolved\s*:\s*\(annotationId\s*:\s*string\)\s*=>\s*void/);
  });

  it("receives onDelete callback", () => {
    expect(sourceCode).toMatch(/onDelete\s*:\s*\(annotationId\s*:\s*string\)\s*=>\s*void/);
  });
});

// ---------------------------------------------------------------------------
// 21. Analysis summary display
// ---------------------------------------------------------------------------

describe("analysis summary", () => {
  it("shows 'Awaiting analysis…' when no analysis", () => {
    expect(sourceCode).toMatch(/Awaiting analysis…/);
  });

  it("collapses whitespace in technicalAssessment for summary", () => {
    expect(sourceCode).toMatch(/technicalAssessment\.replace\s*\(\s*\/\\s\+\/g\s*,\s*['"] ['"]\s*\)\.trim\(\)/);
  });

  it("shows 'No analysis available.' in expanded view when no analysis", () => {
    expect(sourceCode).toMatch(/No analysis available\./);
  });

  it("shows 'None.' when no suggested fixes", () => {
    expect(sourceCode).toMatch(/>None\.<\/div>/);
  });
});

// ---------------------------------------------------------------------------
// 22. Batch resolve error handling
// ---------------------------------------------------------------------------

describe("batch resolve error handling", () => {
  it("throws on non-ok response from batch resolve", () => {
    expect(sourceCode).toMatch(/Batch resolve failed/);
  });

  it("catches errors and logs to console.error", () => {
    expect(sourceCode).toMatch(/catch\s*\(e\)\s*\{[\s\S]*?console\.error\(e\)/);
  });

  it("resets batchPosting in finally block", () => {
    expect(sourceCode).toMatch(/finally\s*\{[\s\S]*?setBatchPosting\s*\(\s*false\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 23. Thumbnail alt text
// ---------------------------------------------------------------------------

describe("thumbnail alt text", () => {
  it("has descriptive alt text using formatTs", () => {
    expect(sourceCode).toMatch(/alt=\{`Thumbnail at \$\{formatTs\(a\.timestamp\)\}`\}/);
  });
});

// ---------------------------------------------------------------------------
// 24. Annotations header
// ---------------------------------------------------------------------------

describe("header section", () => {
  it("renders 'Annotations' heading", () => {
    expect(sourceCode).toMatch(/>Annotations</);
  });

  it("batch button has disabled styling classes", () => {
    expect(sourceCode).toMatch(/disabled:cursor-not-allowed/);
    expect(sourceCode).toMatch(/disabled:opacity-50/);
  });
});

// ---------------------------------------------------------------------------
// 25. Card key prop
// ---------------------------------------------------------------------------

describe("card rendering", () => {
  it("uses annotation id as React key", () => {
    expect(sourceCode).toMatch(/key=\{a\.id\}/);
  });

  it("renders AnnotationCard for each sorted annotation", () => {
    expect(sourceCode).toMatch(/sorted\.map\s*\(\s*\(a\)/);
  });
});

// ---------------------------------------------------------------------------
// 26. View Diff / Revert Fix when fixCommitSha exists (items 10.8, 10.11)
// ---------------------------------------------------------------------------

describe("View Diff and Revert Fix buttons (10.8, 10.11)", () => {
  it("conditionally renders View Diff button when fixCommitSha exists", () => {
    // 10.8: "View Diff" button shown when fixCommitSha exists
    expect(sourceCode).toMatch(/a\.fixCommitSha\s*\?/);
    expect(sourceCode).toMatch(/View Diff/);
  });

  it("View Diff button toggles label to 'Hide Diff' when diff is visible (10.10)", () => {
    // The button text flips between "View Diff" and "Hide Diff" based on showDiff state
    expect(sourceCode).toMatch(/Hide Diff/);
    expect(sourceCode).toMatch(/showDiff\s*\?\s*['"]Hide Diff['"]\s*:\s*['"]View Diff['"]/);
  });

  it("conditionally renders Revert Fix button when fixCommitSha exists (10.11)", () => {
    expect(sourceCode).toMatch(/Revert Fix/);
  });

  it("both buttons are inside the fixCommitSha conditional block", () => {
    // Both View Diff and Revert Fix must appear together inside `a.fixCommitSha ?`
    const fixBlock = sourceCode.match(/a\.fixCommitSha\s*\?[\s\S]*?Revert Fix/);
    expect(fixBlock).not.toBeNull();
    expect(fixBlock![0]).toContain('View Diff');
  });
});

// ---------------------------------------------------------------------------
// 27. Diff panel display (items 10.9, 10.10)
// ---------------------------------------------------------------------------

describe("diff panel display (10.9, 10.10)", () => {
  it("shows diff panel when showDiff and diffText are truthy (10.9)", () => {
    expect(sourceCode).toMatch(/showDiff\s*&&\s*diffText/);
  });

  it("diff panel renders in a <pre> element (10.10)", () => {
    expect(sourceCode).toMatch(/<pre\s[^>]*font-mono/);
  });

  it("diff panel shows commit SHA", () => {
    expect(sourceCode).toMatch(/a\.fixCommitSha\?\.slice\(0,\s*8\)/);
  });

  it("fetches diff from /api/annotations/${id}/diff", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*`\/api\/annotations\/\$\{a\.id\}\/diff`/);
  });

  it("POSTs to /api/annotations/${id}/revert for revert action", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*`\/api\/annotations\/\$\{a\.id\}\/revert`/);
  });
});

// ---------------------------------------------------------------------------
// 28. SSE onDone triggers annotation refresh (item 13.5) — EXPECTED TO FAIL BEFORE FIX
// ---------------------------------------------------------------------------

describe("SseLogPanel onDone triggers annotation refresh (13.5)", () => {
  it("onDone callback calls onBatchResolve with batchJobId to refresh annotations", () => {
    // After the SSE 'done' event fires the batch resolve job is complete and
    // annotations must be re-fetched so resolved ones show '✓ Resolved'.
    // A no-op onDone means the parent never reloads — this is the bug.
    // Fix: call onBatchResolve(batchJobId) inside the onDone callback.
    expect(sourceCode).toMatch(/onDone=\{\s*\(\)\s*=>\s*\{[^}]*onBatchResolve/);
  });
});

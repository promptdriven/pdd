/**
 * Tests for components/stages/Stage10Audit.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/stage10_audit_typescriptreact.prompt.
 *
 * Spec requirements verified:
 *   1. Props: `onAdvance: () => void`.
 *   2. Section audit table: columns section, pass count, fail count, status badge,
 *      [View Report], [↺ Audit].
 *   3. [Audit All Sections] and [Audit Section ▾] dropdown toolbar buttons.
 *      Trigger `POST /api/pipeline/audit/run`.
 *   4. [View Report] expands the row inline showing per-spec verdict rows:
 *      verdict badge (PASS=green / FAIL=red), spec name, one-line summary.
 *   5. FAIL rows show inline frame/spec previews; [Play Video] swaps the
 *      frame preview into an inline section video player, plus [Create Annotation →].
 *   6. Audit run stream shows per-agent progress: `{ type: 'audit-section', sectionId, passCount, failCount }`.
 *   7. `'use client'` directive.
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "components", "stages", "Stage10Audit.tsx");
const sourceCode = fs.readFileSync(SOURCE_PATH, "utf-8");

// ---------------------------------------------------------------------------
// 1. 'use client' directive (Req 7)
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

  it("exports Stage10Audit", () => {
    expect(sourceCode).toMatch(/export\s+(default\s+function|const|default)\s+Stage10Audit/);
  });
});

// ---------------------------------------------------------------------------
// 3. Props interface (Req 1)
// ---------------------------------------------------------------------------

describe("Stage10Audit props", () => {
  it("declares onAdvance: () => void prop", () => {
    expect(sourceCode).toMatch(/onAdvance\s*:\s*\(\)\s*=>\s*void/);
  });

  it("defines Stage10AuditProps interface", () => {
    expect(sourceCode).toMatch(/interface\s+Stage10AuditProps/);
  });

  it("destructures onAdvance from props", () => {
    expect(sourceCode).toMatch(/\{\s*onAdvance/);
  });
});

// ---------------------------------------------------------------------------
// 4. API Endpoints
// ---------------------------------------------------------------------------

describe("API endpoints", () => {
  it("uses GET /api/pipeline/audit/results on mount", () => {
    expect(sourceCode).toMatch(/['"`]\/api\/pipeline\/audit\/results['"`]/);
  });

  it("uses POST /api/pipeline/audit/run for auditing", () => {
    expect(sourceCode).toMatch(/['"`]\/api\/pipeline\/audit\/run['"`]/);
    expect(sourceCode).toMatch(/method\s*:\s*['"]POST['"]/);
  });

  it("reads the audit run response stream for progress", () => {
    expect(sourceCode).toMatch(/res\.body\?\.getReader\(\)/);
    expect(sourceCode).toMatch(/new\s+TextDecoder/);
  });

  it("uses GET /api/pipeline/specs/file for spec viewer", () => {
    expect(sourceCode).toMatch(/\/api\/pipeline\/specs\/file\?path=/);
  });
});

// ---------------------------------------------------------------------------
// 5. Section Audit Table (Req 2)
// ---------------------------------------------------------------------------

describe("Section audit table", () => {
  it("renders Section column header", () => {
    expect(sourceCode).toContain("Section");
  });

  it("renders Pass column header", () => {
    expect(sourceCode).toContain("Pass");
  });

  it("renders Fail column header", () => {
    expect(sourceCode).toContain("Fail");
  });

  it("renders Status column header", () => {
    expect(sourceCode).toContain("Status");
  });

  it("renders Actions column header", () => {
    expect(sourceCode).toContain("Actions");
  });

  it("displays section label for each row", () => {
    expect(sourceCode).toMatch(/section\.sectionLabel/);
  });

  it("displays pass count for each row", () => {
    expect(sourceCode).toMatch(/section\.passCount/);
  });

  it("displays fail count for each row", () => {
    expect(sourceCode).toMatch(/section\.failCount/);
  });

  it("displays status badge for each row", () => {
    expect(sourceCode).toMatch(/section\.status/);
  });

  it("renders View Report button", () => {
    expect(sourceCode).toContain("View Report");
  });

  it("renders ↺ Audit button", () => {
    expect(sourceCode).toContain("↺ Audit");
  });
});

// ---------------------------------------------------------------------------
// 6. Toolbar Buttons (Req 3)
// ---------------------------------------------------------------------------

describe("Toolbar buttons", () => {
  it("renders Audit All Sections button", () => {
    expect(sourceCode).toContain("Audit All Sections");
  });

  it("renders Audit Section ▾ dropdown", () => {
    expect(sourceCode).toContain("Audit Section ▾");
  });

  it("Audit All Sections triggers POST /api/pipeline/audit/run", () => {
    expect(sourceCode).toMatch(/handleAuditRun\(\)/);
  });

  it("individual section audit passes sectionId", () => {
    expect(sourceCode).toMatch(/handleAuditRun\(.*\.id\)/);
  });

  it("handleAuditRun sends POST request", () => {
    expect(sourceCode).toMatch(/fetch\(\s*['"]\/api\/pipeline\/audit\/run['"]\s*,\s*\{/);
  });

  it("handleAuditRun sends JSON body with sections array when provided", () => {
    expect(sourceCode).toMatch(/JSON\.stringify\(sectionId\s*\?\s*\{\s*sections:\s*\[\s*sectionId\s*\]\s*\}\s*:\s*\{\}\)/);
  });
});

// ---------------------------------------------------------------------------
// 7. View Report / Expanded Row (Req 4)
// ---------------------------------------------------------------------------

describe("View Report expanded row", () => {
  it("uses useState<Record<string, boolean>> for expanded state", () => {
    expect(sourceCode).toMatch(/useState<Record<string,\s*boolean>>/);
  });

  it("toggleExpanded toggles expansion for a section", () => {
    expect(sourceCode).toMatch(/toggleExpanded/);
  });

  it("expanded rows show verdict badge", () => {
    expect(sourceCode).toMatch(/spec\.verdict/);
  });

  it("expanded rows show spec name", () => {
    expect(sourceCode).toMatch(/spec\.specName/);
  });

  it("expanded rows show summary", () => {
    expect(sourceCode).toMatch(/spec\.summary/);
  });

  it("verdict column header is present in expanded row", () => {
    expect(sourceCode).toContain("Verdict");
  });

  it("spec column header is present in expanded row", () => {
    expect(sourceCode).toContain("Spec");
  });

  it("summary column header is present in expanded row", () => {
    expect(sourceCode).toContain("Summary");
  });

  it("PASS verdict gets green styling", () => {
    expect(sourceCode).toMatch(/PASS.*green|green.*PASS/s);
  });

  it("FAIL verdict gets red styling", () => {
    expect(sourceCode).toMatch(/FAIL.*red|red.*FAIL/s);
  });
});

// ---------------------------------------------------------------------------
// 8. FAIL Row Actions (Req 5)
// ---------------------------------------------------------------------------

describe("FAIL row actions", () => {
  it("FAIL rows are conditionally rendered", () => {
    expect(sourceCode).toMatch(/spec\.verdict\s*===\s*['"]FAIL['"]/);
  });

  it("renders inline Frame Preview label for FAIL rows", () => {
    expect(sourceCode).toContain("Frame Preview");
  });

  it("renders inline Spec Preview label for FAIL rows", () => {
    expect(sourceCode).toContain("Spec Preview");
  });

  it("shows inline frame image beside the summary for FAIL rows", () => {
    expect(sourceCode).toMatch(/<img\s+src=\{frame\}/);
  });

  it("renders a two-column inline preview layout for FAIL rows", () => {
    expect(sourceCode).toMatch(/grid[\s\S]*lg:grid-cols-2/);
  });

  it("renders Play Video button for FAIL rows", () => {
    expect(sourceCode).toContain("Play Video");
  });

  it("does not render View Frame button anymore", () => {
    expect(sourceCode).not.toContain("View Frame");
  });

  it("does not render View Spec button anymore", () => {
    expect(sourceCode).not.toContain("View Spec");
  });

  it("renders Create Annotation → button for FAIL rows", () => {
    expect(sourceCode).toContain("Create Annotation →");
  });

  it("Play Video toggles inline section video playback", () => {
    expect(sourceCode).toMatch(/toggleVideoPreview/);
  });

  it("frame URL follows spec pattern /api/video/outputs/audit/{sectionId}/{specName}_frame.png", () => {
    expect(sourceCode).toMatch(/\/api\/video\/outputs\/audit\/\$\{.*sectionId.*\}\/\$\{.*specName.*\}_frame\.png/);
  });

  it("section video URL follows /api/video/outputs/sections/{sectionId}.mp4", () => {
    expect(sourceCode).toMatch(/\/api\/video\/outputs\/sections\/\$\{section\.sectionId\}\.mp4/);
  });

  it("Create Annotation → calls handleCreateAnnotation", () => {
    expect(sourceCode).toMatch(/handleCreateAnnotation/);
  });
});

describe("Inline spec preview loading", () => {
  it("prefetches spec content for expanded FAIL rows", () => {
    expect(sourceCode).toMatch(/loadSpecContent/);
  });

  it("shows Loading spec... in the inline preview while fetching", () => {
    expect(sourceCode).toContain("Loading spec...");
  });

  it("renders inline spec content with whitespace preservation", () => {
    expect(sourceCode).toMatch(/whitespace-pre-wrap/);
  });
});

// ---------------------------------------------------------------------------
// 9. Inline Video Preview
// ---------------------------------------------------------------------------

describe("Inline video preview", () => {
  it("renders an inline <video> element for the active section render", () => {
    expect(sourceCode).toMatch(/<video[\s\S]*src=\{sectionVideo\}/);
  });

  it("seeks the player to the spec playbackWindow startSeconds on metadata load", () => {
    expect(sourceCode).toMatch(/currentTime\s*=\s*spec\.playbackWindow\.startSeconds/);
  });

  it("pauses the player when currentTime reaches the spec playbackWindow endSeconds", () => {
    expect(sourceCode).toMatch(/currentTime\s*>=\s*spec\.playbackWindow\.endSeconds[\s\S]*pause\(\)/);
  });

  it("video element has controls enabled", () => {
    expect(sourceCode).toMatch(/<video[\s\S]*controls/);
  });

  it("video element autoplays when activated", () => {
    expect(sourceCode).toMatch(/<video[\s\S]*autoPlay/);
  });

  it("video element uses the audit frame as poster art", () => {
    expect(sourceCode).toMatch(/<video[\s\S]*poster=\{frame\}/);
  });

  it("shows the Frame Preview heading while toggling between image and video", () => {
    expect(sourceCode).toContain("Frame Preview");
  });

  it("does not render a dialog-based video modal anymore", () => {
    expect(sourceCode).not.toMatch(/<dialog/);
  });
});

// ---------------------------------------------------------------------------
// 10. Spec Preview (inline content)
// ---------------------------------------------------------------------------

describe("Spec viewer", () => {
  it("renders inline spec content container", () => {
    expect(sourceCode).toMatch(/whitespace-pre-wrap/);
  });

  it("fetches spec file from GET /api/pipeline/specs/file", () => {
    expect(sourceCode).toMatch(/fetch\(`\/api\/pipeline\/specs\/file\?path=\$\{encodeURIComponent/);
  });

  it("displays loading state while fetching spec", () => {
    expect(sourceCode).toContain("Loading spec...");
  });

  it("handles spec fetch failure", () => {
    expect(sourceCode).toContain("Failed to load spec file.");
  });

  it("stores spec content in state", () => {
    expect(sourceCode).toMatch(/setSpecContent/);
  });

  it("parses JSON response to extract content field (not raw JSON text)", () => {
    // The /api/pipeline/specs/file endpoint returns JSON: { content: string }
    // The spec viewer fetch must NOT use res.text() to get raw JSON string;
    // it must parse JSON and extract the content field
    // Look for the pattern: res.json() followed by using .content in the spec viewer logic
    const specViewerSection = sourceCode.slice(
      sourceCode.indexOf("loadSpecContent"),
      sourceCode.indexOf("loadSpecContent") + 800
    );
    expect(specViewerSection).not.toMatch(/res\.text\(\)/);
  });
});

// ---------------------------------------------------------------------------
// 11. Create Annotation → (Spec: pre-fill and advance)
// ---------------------------------------------------------------------------

describe("Create Annotation handler", () => {
  it("handleCreateAnnotation calls onCreateAnnotation", () => {
    expect(sourceCode).toMatch(/onCreateAnnotation\?\.\(/);
  });

  it("pre-fill shape includes text field", () => {
    expect(sourceCode).toMatch(/text:\s*finding/);
  });

  it("pre-fill shape includes sectionId field", () => {
    expect(sourceCode).toMatch(/sectionId,/);
  });

  it("pre-fill shape includes compositeDataUrl field", () => {
    expect(sourceCode).toMatch(/compositeDataUrl:\s*frameUrl/);
  });

  it("uses onCreateAnnotation callback", () => {
    expect(sourceCode).toMatch(/onCreateAnnotation\?\.\(/);
  });

  it("falls back to summary when finding is not present", () => {
    expect(sourceCode).toMatch(/spec\.finding\s*\|\|\s*spec\.summary/);
  });
});

// ---------------------------------------------------------------------------
// 12. SSE Stream Progress (Req 6)
// ---------------------------------------------------------------------------

describe("Audit run stream progress", () => {
  it("reads from the POST response stream", () => {
    expect(sourceCode).toMatch(/res\.body\?\.getReader\(\)/);
  });

  it("listens for audit-section events", () => {
    expect(sourceCode).toMatch(/['"]audit-section['"]/);
  });

  it("extracts sectionId from SSE events", () => {
    expect(sourceCode).toMatch(/data\.sectionId/);
  });

  it("updates passCount from SSE events", () => {
    expect(sourceCode).toMatch(/data\.passCount/);
  });

  it("updates failCount from SSE events", () => {
    expect(sourceCode).toMatch(/data\.failCount/);
  });

  it("updates status from streamed audit events", () => {
    expect(sourceCode).toMatch(/status:\s*data\.status/);
  });

  it("refreshes audit results after the stream completes", () => {
    expect(sourceCode).toMatch(/await\s+refreshResults\(\)/);
  });

  it("cancels the reader after consuming the stream", () => {
    expect(sourceCode).toMatch(/reader\.cancel\(\)/);
  });
});

// ---------------------------------------------------------------------------
// 13. Status Badge Styles (Spec: pending=gray, running=amber, done=green, error=red)
// ---------------------------------------------------------------------------

describe("Status badge styles", () => {
  it("pending status has gray/slate styling", () => {
    expect(sourceCode).toMatch(/pending:\s*['"].*slate/);
  });

  it("running status has amber styling", () => {
    expect(sourceCode).toMatch(/running:\s*['"].*amber/);
  });

  it("done status has green styling", () => {
    expect(sourceCode).toMatch(/done:\s*['"].*green/);
  });

  it("error status has red styling", () => {
    expect(sourceCode).toMatch(/error:\s*['"].*red/);
  });

  it("defines statusClasses record", () => {
    expect(sourceCode).toMatch(/const\s+statusClasses/);
  });
});

// ---------------------------------------------------------------------------
// 14. Verdict Badge Styles (Spec: PASS=green, FAIL=red)
// ---------------------------------------------------------------------------

describe("Verdict badge styles", () => {
  it("PASS verdict has green styling", () => {
    expect(sourceCode).toMatch(/PASS:\s*['"].*green/);
  });

  it("FAIL verdict has red styling", () => {
    expect(sourceCode).toMatch(/FAIL:\s*['"].*red/);
  });

  it("defines verdictClasses record", () => {
    expect(sourceCode).toMatch(/const\s+verdictClasses/);
  });
});

// ---------------------------------------------------------------------------
// 15. Loading and Error States
// ---------------------------------------------------------------------------

describe("Loading and error states", () => {
  it("shows loading skeleton while fetching", () => {
    expect(sourceCode).toMatch(/loading\s*&&/);
  });

  it("loading skeleton uses animate-pulse", () => {
    expect(sourceCode).toContain("animate-pulse");
  });

  it("displays error message when present", () => {
    expect(sourceCode).toMatch(/\{error\s*&&/);
  });

  it("error message has red styling", () => {
    expect(sourceCode).toContain("bg-red-900/30");
  });

  it("handles fetch error for audit results", () => {
    expect(sourceCode).toContain("Failed to load audit results.");
  });
});

// ---------------------------------------------------------------------------
// 16. Empty State
// ---------------------------------------------------------------------------

describe("Empty state", () => {
  it("displays message when no audit results available", () => {
    expect(sourceCode).toContain("No audit results available.");
  });

  it("shows a message when a section has no audit report rows yet", () => {
    expect(sourceCode).toContain("No audit reports found yet.");
  });

  it("empty state is conditional on sections length", () => {
    expect(sourceCode).toMatch(/sections\.length\s*===\s*0/);
  });
});

// ---------------------------------------------------------------------------
// 17. Type Definitions
// ---------------------------------------------------------------------------

describe("Type definitions", () => {
  it("defines AuditStatus type", () => {
    expect(sourceCode).toMatch(/type\s+AuditStatus\s*=.*pending.*running.*done.*error/s);
  });

  it("defines Verdict type with PASS and FAIL", () => {
    expect(sourceCode).toMatch(/type\s+Verdict\s*=\s*['"]PASS['"]\s*\|\s*['"]FAIL['"]/);
  });

  it("defines SpecVerdict interface", () => {
    expect(sourceCode).toMatch(/interface\s+SpecVerdict/);
  });

  it("SpecVerdict includes specName field", () => {
    expect(sourceCode).toMatch(/specName:\s*string/);
  });

  it("SpecVerdict includes verdict field", () => {
    expect(sourceCode).toMatch(/verdict:\s*Verdict/);
  });

  it("SpecVerdict includes summary field", () => {
    expect(sourceCode).toMatch(/summary:\s*string/);
  });

  it("SpecVerdict includes optional finding field", () => {
    expect(sourceCode).toMatch(/finding\?:\s*string/);
  });

  it("SpecVerdict includes optional specPath field", () => {
    expect(sourceCode).toMatch(/specPath\?:\s*string/);
  });

  it("SpecVerdict includes optional playbackWindow field", () => {
    expect(sourceCode).toMatch(/playbackWindow\?:\s*PlaybackWindow/);
  });

  it("defines SectionAudit interface", () => {
    expect(sourceCode).toMatch(/interface\s+SectionAudit/);
  });

  it("SectionAudit includes sectionId field", () => {
    expect(sourceCode).toMatch(/sectionId:\s*string/);
  });

  it("SectionAudit includes sectionLabel field", () => {
    expect(sourceCode).toMatch(/sectionLabel:\s*string/);
  });

  it("SectionAudit includes passCount field", () => {
    expect(sourceCode).toMatch(/passCount:\s*number/);
  });

  it("SectionAudit includes failCount field", () => {
    expect(sourceCode).toMatch(/failCount:\s*number/);
  });

  it("SectionAudit includes status field", () => {
    expect(sourceCode).toMatch(/status:\s*AuditStatus/);
  });

  it("SectionAudit includes specs array", () => {
    expect(sourceCode).toMatch(/specs:\s*SpecVerdict\[\]/);
  });

  it("defines AuditResultsResponse interface", () => {
    expect(sourceCode).toMatch(/interface\s+AuditResultsResponse/);
  });
});

// ---------------------------------------------------------------------------
// 18. React State Management
// ---------------------------------------------------------------------------

describe("React state management", () => {
  it("uses useState for sections", () => {
    expect(sourceCode).toMatch(/useState<SectionAudit\[\]>/);
  });

  it("uses useState for expanded rows", () => {
    expect(sourceCode).toMatch(/useState<Record<string,\s*boolean>>/);
  });

  it("uses useState for loading spec content", () => {
    expect(sourceCode).toMatch(/useState<Record<string,\s*boolean>>\(\{\}\)/);
  });

  it("uses useState for the active inline video key", () => {
    expect(sourceCode).toMatch(/useState<string\s*\|\s*null>\(null\)/);
  });

  it("uses useState for loading", () => {
    expect(sourceCode).toMatch(/useState\(true\)/);
  });

  it("uses useState for error", () => {
    expect(sourceCode).toMatch(/useState<string\s*\|\s*null>/);
  });

  it("uses useCallback for handlers", () => {
    expect(sourceCode).toMatch(/useCallback/);
  });

  it("uses useMemo for section options", () => {
    expect(sourceCode).toMatch(/useMemo/);
  });

  it("uses useEffect for mount fetch", () => {
    expect(sourceCode).toMatch(/useEffect/);
  });
});

// ---------------------------------------------------------------------------
// 19. Dropdown Section Options
// ---------------------------------------------------------------------------

describe("Dropdown section options", () => {
  it("maps section options to dropdown buttons", () => {
    expect(sourceCode).toMatch(/sectionOptions\.map/);
  });

  it("each dropdown option triggers handleAuditRun with section id", () => {
    expect(sourceCode).toMatch(/handleAuditRun\(opt\.id\)/);
  });
});

// ---------------------------------------------------------------------------
// 19b. Audit section dropdown — auto-close behavior
// ---------------------------------------------------------------------------

describe("Audit section dropdown", () => {
  it("uses custom dropdown instead of details/summary", () => {
    expect(sourceCode).not.toMatch(/<details/);
    expect(sourceCode).not.toMatch(/<summary/);
  });

  it("dropdown auto-closes after selection", () => {
    expect(sourceCode).toMatch(/setAuditDropdownOpen\(false\)/);
  });

  it("has click-outside handler to close dropdown", () => {
    expect(sourceCode).toMatch(/handleClickOutside/);
  });

  it("uses ref for click-outside detection", () => {
    expect(sourceCode).toMatch(/auditDropdownRef/);
  });
});

// ---------------------------------------------------------------------------
// 20. Cleanup and Mount Safety
// ---------------------------------------------------------------------------

describe("Cleanup and mount safety", () => {
  it("uses mountedRef to prevent state updates after unmount", () => {
    expect(sourceCode).toMatch(/mountedRef\s*=\s*useRef\(true\)/);
  });

  it("sets mountedRef.current to false in cleanup", () => {
    expect(sourceCode).toMatch(/mountedRef\.current\s*=\s*false/);
  });

  it("checks mountedRef.current before setting state", () => {
    expect(sourceCode).toMatch(/if\s*\(mountedRef\.current\)/);
  });
});

/**
 * Tests for components/stages/Stage6SpecGeneration.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/stage6_spec_generation_typescriptreact.prompt.
 *
 * Spec requirements verified:
 *   1. Props: onAdvance: () => void.
 *   2. Toolbar: [Generate All Specs] and per-section [↺ Regenerate] buttons. Trigger POST /api/pipeline/specs/run.
 *   3. Section groups are collapsible (expanded state persisted in localStorage).
 *   4. Each spec row shows: visual type badge [Remotion]/[veo:]/[title:]/[split:], status (exists/missing), [✎] open in editor, [↺] regenerate that file.
 *   5. Clicking [✎]: opens an inline CodeMirror Markdown editor below the table. Auto-saves via PUT /api/pipeline/specs/file on blur + 1s debounce.
 *   5b. The inline editor shows script context side by side with the selected spec, aligned by section heading and Narration Sync quotes.
 *   6. SSE log in an expandable drawer at the bottom.
 *   7. 'use client' directive.
 *   8. Visual type badge colors: Remotion=blue, veo=purple, title=teal, split=orange.
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "components", "stages", "Stage6SpecGeneration.tsx");
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

  it("exports Stage6SpecGeneration", () => {
    expect(sourceCode).toMatch(/export\s+(const|default)\s+Stage6SpecGeneration/);
  });

  it("has a default export", () => {
    expect(sourceCode).toMatch(/export\s+default/);
  });
});

// ---------------------------------------------------------------------------
// 3. Props interface (Req 1)
// ---------------------------------------------------------------------------

describe("Stage6SpecGeneration props", () => {
  it("declares onAdvance: () => void prop", () => {
    expect(sourceCode).toMatch(/onAdvance\s*:\s*\(\)\s*=>\s*void/);
  });

  it("defines Stage6SpecGenerationProps interface", () => {
    expect(sourceCode).toMatch(/interface\s+Stage6SpecGenerationProps/);
  });

  it("destructures onAdvance from props", () => {
    expect(sourceCode).toMatch(/\{\s*onAdvance\s*\}/);
  });
});

// ---------------------------------------------------------------------------
// 4. Import structure
// ---------------------------------------------------------------------------

describe("import structure", () => {
  it("imports React from react", () => {
    expect(sourceCode).toMatch(/import\s+React/);
    expect(sourceCode).toMatch(/from\s+['"]react['"]/);
  });

  it("imports useState from react", () => {
    expect(sourceCode).toMatch(/useState/);
  });

  it("imports useEffect from react", () => {
    expect(sourceCode).toMatch(/useEffect/);
  });

  it("imports useCallback from react", () => {
    expect(sourceCode).toMatch(/useCallback/);
  });

  it("imports useRef from react", () => {
    expect(sourceCode).toMatch(/useRef/);
  });

  it("imports useMemo from react", () => {
    expect(sourceCode).toMatch(/useMemo/);
  });

  it("imports CodeMirror from @uiw/react-codemirror", () => {
    expect(sourceCode).toMatch(/import\s+CodeMirror\s+from\s+['"]@uiw\/react-codemirror['"]/);
  });

  it("imports markdown from @codemirror/lang-markdown", () => {
    expect(sourceCode).toMatch(/import\s+\{\s*markdown\s*\}\s+from\s+['"]@codemirror\/lang-markdown['"]/);
  });

  it("imports SseLogPanel", () => {
    expect(sourceCode).toMatch(/import\s+\{?\s*SseLogPanel\s*\}?\s+from/);
  });

  it("imports script context helpers", () => {
    expect(sourceCode).toMatch(/from\s+['"]@\/lib\/spec-script-context['"]/);
    expect(sourceCode).toMatch(/parseScriptSections/);
    expect(sourceCode).toMatch(/findMatchingScriptSection/);
    expect(sourceCode).toMatch(/extractNarrationSyncQuotes/);
    expect(sourceCode).toMatch(/scriptLineMatchesNarration/);
  });
});

// ---------------------------------------------------------------------------
// 5. Type definitions
// ---------------------------------------------------------------------------

describe("type definitions", () => {
  it("defines SpecFile type with path and exists fields", () => {
    expect(sourceCode).toMatch(/type\s+SpecFile\s*=\s*\{/);
    expect(sourceCode).toMatch(/path\s*:\s*string/);
    expect(sourceCode).toMatch(/exists\s*:\s*boolean/);
  });

  it("SpecFile has optional firstLine field", () => {
    expect(sourceCode).toMatch(/firstLine\?\s*:\s*string/);
  });

  it("defines SpecSection type with id, label, and files", () => {
    expect(sourceCode).toMatch(/type\s+SpecSection\s*=\s*\{/);
    expect(sourceCode).toMatch(/id\s*:\s*string/);
    expect(sourceCode).toMatch(/label\s*:\s*string/);
    expect(sourceCode).toMatch(/files\s*:\s*SpecFile\[\]/);
  });

  it("defines SpecListResponse type with sections", () => {
    expect(sourceCode).toMatch(/type\s+SpecListResponse\s*=\s*\{/);
    expect(sourceCode).toMatch(/sections\s*:\s*SpecSection\[\]/);
  });

  it("defines BadgeInfo type with label and colorClass", () => {
    expect(sourceCode).toMatch(/type\s+BadgeInfo\s*=\s*\{/);
    expect(sourceCode).toMatch(/label\s*:\s*string/);
    expect(sourceCode).toMatch(/colorClass\s*:\s*string/);
  });
});

// ---------------------------------------------------------------------------
// 6. Badge helper function (Req 8 — badge colors)
// ---------------------------------------------------------------------------

describe("badgeFromFirstLine helper", () => {
  it("defines badgeFromFirstLine function", () => {
    expect(sourceCode).toMatch(/const\s+badgeFromFirstLine\s*=/);
  });

  it("returns null for undefined/empty input", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!line\s*\)\s*return\s+null/);
  });

  it("matches [Remotion] badge with blue colors", () => {
    expect(sourceCode).toContain("Remotion");
    expect(sourceCode).toContain("bg-blue-900/50");
    expect(sourceCode).toContain("text-blue-300");
  });

  it("matches [veo:...] badge with purple colors", () => {
    expect(sourceCode).toMatch(/\[veo:.*?\]/);
    expect(sourceCode).toMatch(/bg-purple-900\/50/);
    expect(sourceCode).toMatch(/text-purple-300/);
  });

  it("matches [title:...] badge with teal colors", () => {
    expect(sourceCode).toMatch(/\[title:.*?\]/);
    expect(sourceCode).toMatch(/bg-teal-900\/50/);
    expect(sourceCode).toMatch(/text-teal-300/);
  });

  it("matches [split:...] badge with orange colors", () => {
    expect(sourceCode).toMatch(/\[split:.*?\]/);
    expect(sourceCode).toMatch(/bg-orange-900\/50/);
    expect(sourceCode).toMatch(/text-orange-300/);
  });

  it("returns null when no badge pattern matches", () => {
    // The function should have a final return null
    const funcBody = sourceCode.match(/const\s+badgeFromFirstLine[\s\S]*?return\s+null;\s*\};/);
    expect(funcBody).not.toBeNull();
  });
});

// ---------------------------------------------------------------------------
// 7. localStorage key for collapsible state (Req 3)
// ---------------------------------------------------------------------------

describe("localStorage key", () => {
  it("defines LOCAL_STORAGE_KEY constant as 'spec-sections-expanded'", () => {
    expect(sourceCode).toMatch(/const\s+LOCAL_STORAGE_KEY\s*=\s*['"]spec-sections-expanded['"]/);
  });
});

// ---------------------------------------------------------------------------
// 8. State management
// ---------------------------------------------------------------------------

describe("state management", () => {
  it("tracks sections state as SpecSection[]", () => {
    expect(sourceCode).toMatch(/\[\s*sections\s*,\s*setSections\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*SpecSection\[\]\s*>/);
  });

  it("tracks loading state", () => {
    expect(sourceCode).toMatch(/\[\s*loading\s*,\s*setLoading\s*\]/);
  });

  it("tracks error state as string | null", () => {
    expect(sourceCode).toMatch(/\[\s*error\s*,\s*setError\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*string\s*\|\s*null\s*>/);
  });

  it("tracks expanded state as Record<string, boolean> initialized from localStorage", () => {
    expect(sourceCode).toMatch(/\[\s*expanded\s*,\s*setExpanded\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*Record\s*<\s*string\s*,\s*boolean\s*>\s*>/);
    expect(sourceCode).toMatch(/localStorage\.getItem\s*\(\s*LOCAL_STORAGE_KEY\s*\)/);
  });

  it("tracks selectedFile state as SpecFile | null", () => {
    expect(sourceCode).toMatch(/\[\s*selectedFile\s*,\s*setSelectedFile\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*SpecFile\s*\|\s*null\s*>/);
  });

  it("tracks selectedSectionId state as string | null", () => {
    expect(sourceCode).toMatch(/\[\s*selectedSectionId\s*,\s*setSelectedSectionId\s*\]/);
  });

  it("tracks editorValue state", () => {
    expect(sourceCode).toMatch(/\[\s*editorValue\s*,\s*setEditorValue\s*\]/);
  });

  it("tracks editorLoading state", () => {
    expect(sourceCode).toMatch(/\[\s*editorLoading\s*,\s*setEditorLoading\s*\]/);
  });

  it("tracks saving state", () => {
    expect(sourceCode).toMatch(/\[\s*saving\s*,\s*setSaving\s*\]/);
  });

  it("tracks latestJobId state as string | null", () => {
    expect(sourceCode).toMatch(/\[\s*latestJobId\s*,\s*setLatestJobId\s*\]/);
  });

  it("has saveTimerRef for debounce", () => {
    expect(sourceCode).toMatch(/saveTimerRef\s*=\s*useRef/);
  });

  it("has editorContainerRef for inline editor scrolling", () => {
    expect(sourceCode).toMatch(/editorContainerRef\s*=\s*useRef/);
  });

  it("tracks script content, loading, and error state", () => {
    expect(sourceCode).toMatch(/\[\s*scriptContent\s*,\s*setScriptContent\s*\]/);
    expect(sourceCode).toMatch(/\[\s*scriptLoading\s*,\s*setScriptLoading\s*\]/);
    expect(sourceCode).toMatch(/\[\s*scriptError\s*,\s*setScriptError\s*\]/);
  });
});

// ---------------------------------------------------------------------------
// 9. Spec list loading on mount (Req — load spec list)
// ---------------------------------------------------------------------------

describe("spec list loading on mount", () => {
  it("fetches spec list from GET /api/pipeline/specs/list", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/specs\/list['"]\s*\)/);
  });

  it("sets sections state from response data", () => {
    expect(sourceCode).toMatch(/setSections\s*\(\s*data\.sections\s*\)/);
  });

  it("initializes expanded defaults for new sections", () => {
    expect(sourceCode).toMatch(/setExpanded/);
    expect(sourceCode).toMatch(/next\[section\.id\]\s*===\s*undefined/);
  });

  it("handles loading state correctly", () => {
    expect(sourceCode).toMatch(/setLoading\s*\(\s*true\s*\)/);
    expect(sourceCode).toMatch(/setLoading\s*\(\s*false\s*\)/);
  });

  it("handles fetch errors", () => {
    expect(sourceCode).toMatch(/setError/);
  });

  it("defines fetchSpecList as reusable callback", () => {
    expect(sourceCode).toMatch(/const\s+fetchSpecList\s*=\s*useCallback/);
  });
});

// ---------------------------------------------------------------------------
// 9b. Script loading and section alignment
// ---------------------------------------------------------------------------

describe("script loading and alignment", () => {
  it("fetches main script from GET /api/project/script", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/project\/script['"]\s*\)/);
  });

  it("parses script sections and resolves the matching section for the selected spec", () => {
    expect(sourceCode).toMatch(/parseScriptSections\s*\(\s*scriptContent\s*\)/);
    expect(sourceCode).toMatch(/findMatchingScriptSection\s*\(/);
    expect(sourceCode).toMatch(/selectedSection\??/);
  });

  it("extracts Narration Sync quotes from the current spec content", () => {
    expect(sourceCode).toMatch(/extractNarrationSyncQuotes\s*\(\s*editorValue\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 10. Persist expanded state to localStorage (Req 3)
// ---------------------------------------------------------------------------

describe("persist expanded state", () => {
  it("saves expanded state to localStorage when it changes", () => {
    expect(sourceCode).toMatch(/localStorage\.setItem\s*\(\s*LOCAL_STORAGE_KEY\s*,\s*JSON\.stringify\s*\(\s*expanded\s*\)\s*\)/);
  });

  it("depends on expanded state in useEffect", () => {
    expect(sourceCode).toMatch(/\[\s*expanded\s*\]/);
  });
});

// ---------------------------------------------------------------------------
// 11. Section toggle handler (Req 3)
// ---------------------------------------------------------------------------

describe("section toggle handler", () => {
  it("defines handleToggleSection function", () => {
    expect(sourceCode).toMatch(/const\s+handleToggleSection\s*=/);
  });

  it("toggles section expanded state", () => {
    expect(sourceCode).toMatch(/\[id\]\s*:\s*!prev\[id\]/);
  });
});

// ---------------------------------------------------------------------------
// 12. Run specs handler (Req 2)
// ---------------------------------------------------------------------------

describe("run specs handler", () => {
  it("defines runSpecs function that POSTs to /api/pipeline/specs/run", () => {
    expect(sourceCode).toMatch(/const\s+runSpecs\s*=/);
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/specs\/run['"]/);
    expect(sourceCode).toMatch(/method\s*:\s*['"]POST['"]/);
  });

  it("sends Content-Type: application/json header", () => {
    expect(sourceCode).toMatch(/['"]Content-Type['"]\s*:\s*['"]application\/json['"]/);
  });

  it("sends payload as JSON body", () => {
    expect(sourceCode).toMatch(/JSON\.stringify\s*\(\s*payload\s*\)/);
  });

  it("uses readSseStartResult to extract jobId and errorMessage", () => {
    expect(sourceCode).toMatch(/readSseStartResult\s*\(\s*res\s*\)/);
    expect(sourceCode).toMatch(/const\s*\{\s*jobId\s*,\s*errorMessage\s*\}\s*=/);
    expect(sourceCode).toMatch(/setLatestJobId\s*\(\s*jobId\s*\)/);
    expect(sourceCode).toMatch(/if\s*\(\s*errorMessage\s*\)\s*\{\s*setError\s*\(\s*errorMessage\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 13. Generate All Specs handler (Req 2)
// ---------------------------------------------------------------------------

describe("Generate All Specs handler", () => {
  it("defines handleGenerateAll function", () => {
    expect(sourceCode).toMatch(/const\s+handleGenerateAll\s*=/);
  });

  it("calls runSpecs with empty object", () => {
    expect(sourceCode).toMatch(/runSpecs\s*\(\s*\{\s*\}\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 14. Per-section regenerate handler (Req 2)
// ---------------------------------------------------------------------------

describe("per-section regenerate handler", () => {
  it("defines handleRegenerateSection function", () => {
    expect(sourceCode).toMatch(/const\s+handleRegenerateSection\s*=/);
  });

  it("calls runSpecs with sections array containing sectionId", () => {
    expect(sourceCode).toMatch(/runSpecs\s*\(\s*\{\s*sections\s*:\s*\[\s*sectionId\s*\]\s*\}\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 15. Per-file regenerate handler (Req 4)
// ---------------------------------------------------------------------------

describe("per-file regenerate handler", () => {
  it("defines handleRegenerateFile function", () => {
    expect(sourceCode).toMatch(/const\s+handleRegenerateFile\s*=/);
  });

  it("calls runSpecs with files array containing filePath", () => {
    expect(sourceCode).toMatch(/runSpecs\s*\(\s*\{\s*files\s*:\s*\[\s*filePath\s*\]\s*\}\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 16. Load spec file for editor (Req 5)
// ---------------------------------------------------------------------------

describe("load spec file for editor", () => {
  it("defines loadSpecFile function", () => {
    expect(sourceCode).toMatch(/const\s+loadSpecFile\s*=/);
  });

  it("fetches file from GET /api/pipeline/specs/file with encoded path", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*`\/api\/pipeline\/specs\/file\?path=\$\{encodeURIComponent\s*\(\s*file\.path\s*\)\}/);
  });

  it("sets editorValue from response content", () => {
    expect(sourceCode).toMatch(/setEditorValue\s*\(\s*data\?\.content\s*\?\?\s*['"]['"]?\s*\)/);
  });

  it("sets selectedFile state", () => {
    expect(sourceCode).toMatch(/setSelectedFile\s*\(\s*file\s*\)/);
  });

  it("sets selectedSectionId state", () => {
    expect(sourceCode).toMatch(/setSelectedSectionId\s*\(\s*sectionId\s*\)/);
  });

  it("clears stale editor content before loading a new file", () => {
    expect(sourceCode).toMatch(/setEditorValue\s*\(\s*['"]['"]\s*\)/);
  });

  it("tracks editorLoading state", () => {
    expect(sourceCode).toMatch(/setEditorLoading\s*\(\s*true\s*\)/);
    expect(sourceCode).toMatch(/setEditorLoading\s*\(\s*false\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 17. Save spec file (Req 5 — auto-save)
// ---------------------------------------------------------------------------

describe("save spec file", () => {
  it("defines saveSpecFile function", () => {
    expect(sourceCode).toMatch(/const\s+saveSpecFile\s*=/);
  });

  it("PUTs to /api/pipeline/specs/file", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/specs\/file['"]\s*,/);
    expect(sourceCode).toMatch(/method\s*:\s*['"]PUT['"]/);
  });

  it("sends path and content in body", () => {
    expect(sourceCode).toMatch(/path\s*:\s*selectedFile\.path/);
    expect(sourceCode).toMatch(/content\s*:\s*editorValue/);
  });

  it("tracks saving state", () => {
    expect(sourceCode).toMatch(/setSaving\s*\(\s*true\s*\)/);
    expect(sourceCode).toMatch(/setSaving\s*\(\s*false\s*\)/);
  });

  it("returns early if no selectedFile", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!selectedFile\s*\)\s*return/);
  });
});

// ---------------------------------------------------------------------------
// 18. Editor blur handler with debounce (Req 5)
// ---------------------------------------------------------------------------

describe("editor blur handler with debounce", () => {
  it("defines handleEditorBlur function", () => {
    expect(sourceCode).toMatch(/const\s+handleEditorBlur\s*=/);
  });

  it("clears existing timer before setting new one", () => {
    expect(sourceCode).toMatch(/clearTimeout\s*\(\s*saveTimerRef\.current\s*\)/);
  });

  it("uses setTimeout with 1s (1000ms) debounce", () => {
    expect(sourceCode).toMatch(/setTimeout\s*\([\s\S]*?1000\s*\)/);
  });

  it("calls saveSpecFile in the timeout", () => {
    expect(sourceCode).toMatch(/saveSpecFile\s*\(\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 19. Editor title computation
// ---------------------------------------------------------------------------

describe("editor title", () => {
  it("defines editorTitle with useMemo", () => {
    expect(sourceCode).toMatch(/editorTitle\s*=\s*useMemo/);
  });

  it("shows editing path when file is selected", () => {
    expect(sourceCode).toMatch(/Editing:\s*\$\{selectedFile\.path\}/);
  });

  it("shows placeholder when no file is selected", () => {
    expect(sourceCode).toMatch(/Select a spec file to edit/);
  });
});

// ---------------------------------------------------------------------------
// 20a. Inline editor placement and visibility
// ---------------------------------------------------------------------------

describe("inline editor placement", () => {
  it("renders the editor directly under the selected file row", () => {
    expect(sourceCode).toMatch(/selectedFile\?\.path\s*===\s*file\.path/);
    expect(sourceCode).toMatch(/selectedSectionId\s*===\s*section\.id/);
    expect(sourceCode).toMatch(/<td\s+colSpan=\{4\}/);
  });

  it("scrolls the inline editor into view when a file is selected", () => {
    expect(sourceCode).toMatch(/editorContainerRef\.current\?\.scrollIntoView/);
  });

  it("renders a Script Context panel beside the spec editor", () => {
    expect(sourceCode).toContain("Script Context");
    expect(sourceCode).toMatch(/No matching script section found/);
    expect(sourceCode).toMatch(/scriptLineMatchesNarration/);
  });
});

// ---------------------------------------------------------------------------
// 20. Toolbar rendering (Req 2)
// ---------------------------------------------------------------------------

describe("toolbar rendering", () => {
  it("renders Stage 6 heading", () => {
    expect(sourceCode).toMatch(/Stage 6/);
  });

  it("renders Generate All Specs button", () => {
    expect(sourceCode).toMatch(/Generate All Specs/);
  });

  it("Generate All Specs button calls handleGenerateAll", () => {
    expect(sourceCode).toMatch(/onClick=\{handleGenerateAll\}/);
  });

  it("renders Continue button", () => {
    expect(sourceCode).toMatch(/Continue/);
  });

  it("Continue button calls onAdvance on click", () => {
    expect(sourceCode).toMatch(/onClick=\{onAdvance\}/);
  });
});

// ---------------------------------------------------------------------------
// 21. Loading and error states
// ---------------------------------------------------------------------------

describe("loading and error states", () => {
  it("shows loading message while fetching spec list", () => {
    expect(sourceCode).toMatch(/Loading spec list/);
  });

  it("shows error message when fetch fails", () => {
    expect(sourceCode).toMatch(/Error:/);
  });

  it("shows empty state when no sections found", () => {
    expect(sourceCode).toMatch(/No spec sections found/);
  });
});

// ---------------------------------------------------------------------------
// 22. Section rendering with collapsible state (Req 3)
// ---------------------------------------------------------------------------

describe("section rendering", () => {
  it("maps sections to rendered section blocks", () => {
    expect(sourceCode).toMatch(/sections\.map\s*\(\s*\(section\)\s*=>/);
  });

  it("uses section.id as key", () => {
    expect(sourceCode).toMatch(/key=\{section\.id\}/);
  });

  it("displays section label", () => {
    expect(sourceCode).toMatch(/section\.label/);
  });

  it("shows collapse indicator based on expanded state", () => {
    expect(sourceCode).toMatch(/expanded\[section\.id\]\s*\?\s*['"]▾['"]\s*:\s*['"]▸['"]/);
  });

  it("clicking section header toggles expanded", () => {
    expect(sourceCode).toMatch(/onClick=\{[\s\S]*?handleToggleSection\s*\(\s*section\.id\s*\)/);
  });

  it("per-section Regenerate button calls handleRegenerateSection", () => {
    expect(sourceCode).toMatch(/onClick=\{[\s\S]*?handleRegenerateSection\s*\(\s*section\.id\s*\)/);
  });

  it("renders per-section Regenerate button text", () => {
    expect(sourceCode).toMatch(/↺ Regenerate/);
  });

  it("conditionally renders section content when expanded", () => {
    expect(sourceCode).toMatch(/expanded\[section\.id\]\s*&&/);
  });
});

// ---------------------------------------------------------------------------
// 23. Spec file row rendering (Req 4)
// ---------------------------------------------------------------------------

describe("spec file row rendering", () => {
  it("maps section files to table rows", () => {
    expect(sourceCode).toMatch(/section\.files\.map\s*\(\s*\(file\)\s*=>/);
  });

  it("uses file.path as key", () => {
    expect(sourceCode).toMatch(/key=\{file\.path\}/);
  });

  it("computes badge from file.firstLine", () => {
    expect(sourceCode).toMatch(/badgeFromFirstLine\s*\(\s*file\.firstLine\s*\)/);
  });

  it("renders badge label in brackets", () => {
    expect(sourceCode).toMatch(/\[{badge\.label}\]/);
  });

  it("renders dash when no badge", () => {
    expect(sourceCode).toMatch(/—/);
  });

  it("displays file path in monospace", () => {
    expect(sourceCode).toMatch(/file\.path/);
    expect(sourceCode).toMatch(/font-mono/);
  });

  it("shows exists status in green", () => {
    expect(sourceCode).toMatch(/text-green-600/);
    expect(sourceCode).toMatch(/exists/);
  });

  it("shows missing status in red", () => {
    expect(sourceCode).toMatch(/text-red-500/);
    expect(sourceCode).toMatch(/missing/);
  });

  it("renders edit button (✎) that calls loadSpecFile", () => {
    expect(sourceCode).toMatch(/✎/);
    expect(sourceCode).toMatch(/onClick=\{[\s\S]*?loadSpecFile\s*\(\s*file\s*,\s*section\.id\s*\)/);
  });

  it("edit button has 'Open in editor' title", () => {
    expect(sourceCode).toMatch(/title="Open in editor"/);
  });

  it("renders regenerate button (↺) that calls handleRegenerateFile", () => {
    expect(sourceCode).toMatch(/onClick=\{[\s\S]*?handleRegenerateFile\s*\(\s*file\.path\s*\)/);
  });

  it("regenerate button has 'Regenerate file' title", () => {
    expect(sourceCode).toMatch(/title="Regenerate file"/);
  });
});

// ---------------------------------------------------------------------------
// 24. Table headers (Req 4)
// ---------------------------------------------------------------------------

describe("table headers", () => {
  it("renders Type column header", () => {
    expect(sourceCode).toMatch(/<th[\s\S]*?>Type<\/th>/);
  });

  it("renders Path column header", () => {
    expect(sourceCode).toMatch(/<th[\s\S]*?>Path<\/th>/);
  });

  it("renders Status column header", () => {
    expect(sourceCode).toMatch(/<th[\s\S]*?>Status<\/th>/);
  });

  it("renders Actions column header", () => {
    expect(sourceCode).toMatch(/<th[\s\S]*?>Actions<\/th>/);
  });
});

// ---------------------------------------------------------------------------
// 25. Inline CodeMirror editor (Req 5)
// ---------------------------------------------------------------------------

describe("inline CodeMirror editor", () => {
  it("renders CodeMirror component", () => {
    expect(sourceCode).toMatch(/<CodeMirror/);
  });

  it("passes editorValue as value prop", () => {
    expect(sourceCode).toMatch(/value=\{editorValue\}/);
  });

  it("uses markdown extension", () => {
    expect(sourceCode).toMatch(/extensions=\{\[markdown\(\)\]\}/);
  });

  it("has onChange handler that updates editorValue", () => {
    expect(sourceCode).toMatch(/onChange=\{[\s\S]*?setEditorValue/);
  });

  it("has onBlur handler for auto-save", () => {
    expect(sourceCode).toMatch(/onBlur=\{handleEditorBlur\}/);
  });

  it("editor is only shown when selectedFile matches current section", () => {
    expect(sourceCode).toMatch(/const\s+isSelectedFile\s*=/);
    expect(sourceCode).toMatch(/selectedSectionId\s*===\s*section\.id\s*&&\s*selectedFile\?\.path\s*===\s*file\.path/);
  });

  it("shows editor title", () => {
    expect(sourceCode).toMatch(/\{editorTitle\}/);
  });

  it("shows Saving indicator when saving", () => {
    expect(sourceCode).toMatch(/saving\s*&&/);
    expect(sourceCode).toMatch(/Saving/);
  });

  it("shows Loading file indicator when editorLoading", () => {
    expect(sourceCode).toMatch(/editorLoading/);
    expect(sourceCode).toMatch(/Loading file/);
  });

  it("sets editor height", () => {
    expect(sourceCode).toMatch(/height="240px"/);
  });
});

// ---------------------------------------------------------------------------
// 26. SSE log drawer (Req 6)
// ---------------------------------------------------------------------------

describe("SSE log panel", () => {
  it("renders SseLogPanel inside a <details> drawer", () => {
    expect(sourceCode).toMatch(/<details[\s\S]*?<SseLogPanel/);
    expect(sourceCode).toMatch(/<summary[\s\S]*?Spec Generation Logs/);
  });

  it("renders SseLogPanel component", () => {
    expect(sourceCode).toMatch(/<SseLogPanel/);
  });

  it("passes latestJobId to SseLogPanel", () => {
    expect(sourceCode).toMatch(/jobId=\{latestJobId\}/);
  });

  it("passes onDone={fetchSpecList} to SseLogPanel to refresh list after regeneration", () => {
    expect(sourceCode).toMatch(/onDone=\{fetchSpecList\}/);
  });

  it("passes logClassName with a tall height to SseLogPanel", () => {
    expect(sourceCode).toMatch(/logClassName=["'][^"']*max-h-/);
  });
});

// ---------------------------------------------------------------------------
// 27. Layout and structure
// ---------------------------------------------------------------------------

describe("layout and structure", () => {
  it("uses space-y-6 for main layout spacing", () => {
    expect(sourceCode).toMatch(/space-y-6/);
  });

  it("uses rounded border for section cards", () => {
    expect(sourceCode).toMatch(/rounded\s+border/);
  });

  it("uses flex items-center justify-between for toolbar", () => {
    expect(sourceCode).toMatch(/flex\s+items-center\s+justify-between/);
  });

  it("uses indigo styling for Generate All Specs button", () => {
    expect(sourceCode).toMatch(/bg-indigo-600/);
  });
});

// ---------------------------------------------------------------------------
// 28. API endpoints verification
// ---------------------------------------------------------------------------

describe("API endpoints", () => {
  it("uses GET /api/pipeline/specs/list for loading spec list", () => {
    expect(sourceCode).toMatch(/['"]\/api\/pipeline\/specs\/list['"]/);
  });

  it("uses GET /api/pipeline/specs/file for loading spec file", () => {
    expect(sourceCode).toMatch(/\/api\/pipeline\/specs\/file\?path=/);
  });

  it("uses PUT /api/pipeline/specs/file for saving spec file", () => {
    expect(sourceCode).toMatch(/['"]\/api\/pipeline\/specs\/file['"]/);
    expect(sourceCode).toMatch(/method\s*:\s*['"]PUT['"]/);
  });

  it("uses POST /api/pipeline/specs/run for running/regenerating specs", () => {
    expect(sourceCode).toMatch(/['"]\/api\/pipeline\/specs\/run['"]/);
    expect(sourceCode).toMatch(/method\s*:\s*['"]POST['"]/);
  });
});

// ---------------------------------------------------------------------------
// Dark theme compliance
// ---------------------------------------------------------------------------

describe("Dark theme compliance", () => {
  it("section cards use dark background instead of bg-white", () => {
    expect(sourceCode).not.toMatch(/border-slate-200 bg-white/);
  });

  it("section header text uses light color for dark theme", () => {
    expect(sourceCode).not.toMatch(/text-slate-800/);
  });

  it("table text uses dark-theme-friendly colors", () => {
    // text-slate-700 is too dark for a dark background
    expect(sourceCode).not.toMatch(/className="[^"]*text-slate-700[^"]*"/);
  });

  it("buttons use dark theme borders and hover states", () => {
    expect(sourceCode).not.toMatch(/hover:bg-slate-50/);
  });

  it("inline editor uses dark background", () => {
    expect(sourceCode).not.toMatch(/bg-slate-50/);
  });

  it("badge colors use dark theme variants", () => {
    expect(sourceCode).not.toMatch(/bg-blue-100 text-blue-700/);
    expect(sourceCode).not.toMatch(/bg-purple-100 text-purple-700/);
    expect(sourceCode).not.toMatch(/bg-teal-100 text-teal-700/);
    expect(sourceCode).not.toMatch(/bg-orange-100 text-orange-700/);
  });

  it("SSE log drawer uses dark background", () => {
    expect(sourceCode).toMatch(/bg-slate-900/);
  });

  it("Continue button uses dark theme styling", () => {
    expect(sourceCode).not.toMatch(/border-slate-300[^"]*text-slate-600/);
  });
});

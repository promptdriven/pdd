/**
 * Tests for components/stages/Stage2ScriptEditor.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/stage2_script_editor_typescriptreact.prompt.
 *
 * Spec requirements verified:
 *   1. Props: onAdvance: () => void.
 *   2. Left pane: CodeMirror 6 editor with Markdown syntax highlighting. Loads script from GET /api/project/script. Auto-saves via PUT /api/project/script on 1s debounce.
 *   3. Right pane: structured preview re-rendered on 200ms debounce. NARRATOR: blocks → blue ■ prefix. [VISUAL:] blocks → teal ▣ prefix. ## headers → gray section label.
 *   4. Resizable split pane: draggable vertical divider. Persists ratio in localStorage.
 *   5. [Generate TTS Script →] button: enabled only when ≥1 NARRATOR: block is detected. POSTs to /api/pipeline/tts-script/run. On success, calls onAdvance().
 *   6. 'use client' directive.
 *   7. Show SseLogPanel with returned jobId after triggering TTS script generation.
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "components", "stages", "Stage2ScriptEditor.tsx");
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

  it("exports Stage2ScriptEditor as default export", () => {
    expect(sourceCode).toMatch(/export\s+default\s+function\s+Stage2ScriptEditor/);
  });
});

// ---------------------------------------------------------------------------
// 3. Props interface
// ---------------------------------------------------------------------------

describe("Stage2ScriptEditor props", () => {
  it("declares onAdvance: () => void prop", () => {
    expect(sourceCode).toMatch(/onAdvance\s*:\s*\(\)\s*=>\s*void/);
  });

  it("defines Stage2ScriptEditorProps interface", () => {
    expect(sourceCode).toMatch(/interface\s+Stage2ScriptEditorProps/);
  });

  it("destructures onAdvance from props", () => {
    expect(sourceCode).toMatch(/\{\s*onAdvance\s*\}\s*:\s*Stage2ScriptEditorProps/);
  });
});

// ---------------------------------------------------------------------------
// 4. Import structure
// ---------------------------------------------------------------------------

describe("import structure", () => {
  it("imports React and hooks from react", () => {
    expect(sourceCode).toMatch(/import\s+React/);
    expect(sourceCode).toMatch(/from\s+['"]react['"]/);
  });

  it("imports useState from react", () => {
    expect(sourceCode).toMatch(/useState/);
  });

  it("imports useEffect from react", () => {
    expect(sourceCode).toMatch(/useEffect/);
  });

  it("imports useRef from react", () => {
    expect(sourceCode).toMatch(/useRef/);
  });

  it("imports useCallback from react", () => {
    expect(sourceCode).toMatch(/useCallback/);
  });

  it("imports useMemo from react", () => {
    expect(sourceCode).toMatch(/useMemo/);
  });

  it("imports EditorView from @codemirror/view", () => {
    expect(sourceCode).toMatch(/import\s*\{.*EditorView.*\}\s*from\s+['"]@codemirror\/view['"]/);
  });

  it("imports EditorState from @codemirror/state", () => {
    expect(sourceCode).toMatch(/import\s*\{.*EditorState.*\}\s*from\s+['"]@codemirror\/state['"]/);
  });

  it("imports markdown from @codemirror/lang-markdown", () => {
    expect(sourceCode).toMatch(/import\s*\{.*markdown.*\}\s*from\s+['"]@codemirror\/lang-markdown['"]/);
  });

  it("imports SseLogPanel", () => {
    expect(sourceCode).toMatch(/import\s+SseLogPanel\s+from/);
  });
});

// ---------------------------------------------------------------------------
// 5. CodeMirror 6 editor setup
// ---------------------------------------------------------------------------

describe("CodeMirror 6 editor setup", () => {
  it("uses useRef<EditorView | null> for editor view", () => {
    expect(sourceCode).toMatch(/useRef\s*<\s*EditorView\s*\|\s*null\s*>/);
  });

  it("uses useRef<HTMLDivElement | null> for editor container", () => {
    expect(sourceCode).toMatch(/useRef\s*<\s*HTMLDivElement\s*\|\s*null\s*>/);
  });

  it("creates EditorState with markdown extension", () => {
    expect(sourceCode).toMatch(/EditorState\.create\s*\(\s*\{/);
    expect(sourceCode).toMatch(/markdown\s*\(\s*\)/);
  });

  it("mounts EditorView with parent container ref", () => {
    expect(sourceCode).toMatch(/new\s+EditorView\s*\(\s*\{/);
    expect(sourceCode).toMatch(/parent\s*:\s*editorContainerRef\.current/);
  });

  it("includes line wrapping extension", () => {
    expect(sourceCode).toMatch(/EditorView\.lineWrapping/);
  });

  it("listens for doc changes via updateListener", () => {
    expect(sourceCode).toMatch(/EditorView\.updateListener\.of/);
    expect(sourceCode).toMatch(/update\.docChanged/);
  });

  it("destroys editor view on cleanup", () => {
    expect(sourceCode).toMatch(/editorViewRef\.current\?\.destroy\s*\(\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 6. Script loading on mount — GET /api/project/script
// ---------------------------------------------------------------------------

describe("script loading on mount", () => {
  it("fetches script from GET /api/project/script on mount", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/project\/script['"]\s*\)/);
  });

  it("parses response as JSON", () => {
    expect(sourceCode).toMatch(/res\.json\s*\(\s*\)/);
  });

  it("sets content from response data", () => {
    expect(sourceCode).toMatch(/setContent\s*\(\s*data\.content/);
  });

  it("handles fetch errors gracefully", () => {
    expect(sourceCode).toMatch(/catch\s*\(\s*err\s*\)/);
    expect(sourceCode).toMatch(/Failed to load script/);
  });

  it("uses isMounted flag to prevent state update after unmount", () => {
    expect(sourceCode).toMatch(/let\s+isMounted\s*=\s*true/);
    expect(sourceCode).toMatch(/if\s*\(\s*!isMounted\s*\)\s*return/);
    expect(sourceCode).toMatch(/isMounted\s*=\s*false/);
  });

  it("sets loading to false after fetch completes", () => {
    expect(sourceCode).toMatch(/setLoading\s*\(\s*false\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 7. CodeMirror controlled update — sync loaded content
// ---------------------------------------------------------------------------

describe("CodeMirror controlled update", () => {
  it("dispatches content changes to the editor view", () => {
    expect(sourceCode).toMatch(/view\.dispatch\s*\(\s*\{/);
  });

  it("replaces entire document content with changes object", () => {
    expect(sourceCode).toMatch(/changes\s*:\s*\{\s*from\s*:\s*0\s*,\s*to\s*:\s*view\.state\.doc\.length\s*,\s*insert\s*:\s*content\s*\}/);
  });

  it("only dispatches when document differs from content state", () => {
    expect(sourceCode).toMatch(/currentDoc\s*!==\s*content/);
  });
});

// ---------------------------------------------------------------------------
// 8. Auto-save with debounce (1s) — PUT /api/project/script
// ---------------------------------------------------------------------------

describe("auto-save with debounce", () => {
  it("uses setTimeout with 1000ms delay for auto-save", () => {
    expect(sourceCode).toMatch(/setTimeout\s*\(\s*async\s*\(\)\s*=>\s*\{[\s\S]*?\/api\/project\/script[\s\S]*?\}\s*,\s*1000\s*\)/);
  });

  it("sends PUT request to /api/project/script", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/project\/script['"]/);
    expect(sourceCode).toMatch(/method\s*:\s*['"]PUT['"]/);
  });

  it("sends content as JSON body", () => {
    expect(sourceCode).toMatch(/body\s*:\s*JSON\.stringify\s*\(\s*\{\s*content\s*\}\s*\)/);
  });

  it("sets Content-Type header to application/json", () => {
    expect(sourceCode).toMatch(/['"]Content-Type['"]\s*:\s*['"]application\/json['"]/);
  });

  it("clears timeout on cleanup to implement debounce", () => {
    expect(sourceCode).toMatch(/clearTimeout\s*\(\s*id\s*\)/);
  });

  it("skips auto-save while still loading", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*loading\s*\)\s*return/);
  });

  it("handles save errors gracefully", () => {
    expect(sourceCode).toMatch(/Failed to save script/);
  });
});

// ---------------------------------------------------------------------------
// 9. Structured preview parser
// ---------------------------------------------------------------------------

describe("structured preview parser", () => {
  it("defines parsePreview function with useCallback", () => {
    expect(sourceCode).toMatch(/const\s+parsePreview\s*=\s*useCallback/);
  });

  it("splits text into lines", () => {
    expect(sourceCode).toMatch(/text\.split\s*\(\s*\/\\r\?\\n\/\s*\)/);
  });

  it("detects NARRATOR: blocks with regex /^\\*{0,2}NARRATOR:\\*{0,2}/", () => {
    expect(sourceCode).toMatch(/\/\^\\\*\{0,2\}NARRATOR:\\\*\{0,2\}\/\.test\s*\(\s*line\s*\)/);
  });

  it("detects [VISUAL: blocks with regex /^\\*{0,2}\\[VISUAL:/", () => {
    expect(sourceCode).toMatch(/\/\^\\\*\{0,2\}\\\[VISUAL:\/\.test\s*\(\s*line\s*\)/);
  });

  it("detects ## headers with regex /^##\\s+/", () => {
    expect(sourceCode).toMatch(/\/\^##\\s\+\/\.test\s*\(\s*line\s*\)/);
  });

  it("assigns type 'narrator' for NARRATOR: lines", () => {
    expect(sourceCode).toMatch(/type\s*:\s*['"]narrator['"]/);
  });

  it("assigns type 'visual' for [VISUAL: lines", () => {
    expect(sourceCode).toMatch(/type\s*:\s*['"]visual['"]/);
  });

  it("assigns type 'header' for ## lines", () => {
    expect(sourceCode).toMatch(/type\s*:\s*['"]header['"]/);
  });

  it("assigns type 'text' for other non-empty lines", () => {
    expect(sourceCode).toMatch(/type\s*:\s*['"]text['"]/);
  });
});

// ---------------------------------------------------------------------------
// 10. Preview block types definition
// ---------------------------------------------------------------------------

describe("PreviewBlock type", () => {
  it("defines PreviewBlock type with narrator variant", () => {
    expect(sourceCode).toMatch(/type\s+PreviewBlock\s*=\s*\{/);
    expect(sourceCode).toMatch(/'narrator'/);
  });

  it("defines PreviewBlock with visual variant", () => {
    expect(sourceCode).toMatch(/'visual'/);
  });

  it("defines PreviewBlock with header variant", () => {
    expect(sourceCode).toMatch(/'header'/);
  });

  it("defines PreviewBlock with text variant", () => {
    expect(sourceCode).toMatch(/'text'/);
  });

  it("PreviewBlock has text: string property", () => {
    expect(sourceCode).toMatch(/text\s*:\s*string/);
  });
});

// ---------------------------------------------------------------------------
// 11. Debounced preview update (200ms)
// ---------------------------------------------------------------------------

describe("debounced preview update", () => {
  it("uses setTimeout with 200ms delay for preview", () => {
    expect(sourceCode).toMatch(/setTimeout\s*\(\s*\(\)\s*=>\s*\{[\s\S]*?setPreviewBlocks[\s\S]*?\}\s*,\s*200\s*\)/);
  });

  it("calls parsePreview on content changes", () => {
    expect(sourceCode).toMatch(/parsePreview\s*\(\s*content\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 12. Structured preview rendering — blue ■, teal ▣, gray headers
// ---------------------------------------------------------------------------

describe("structured preview rendering", () => {
  it("renders blue ■ prefix for narrator blocks", () => {
    expect(sourceCode).toMatch(/text-blue-500/);
    expect(sourceCode).toMatch(/■/);
  });

  it("renders teal ▣ prefix for visual blocks", () => {
    expect(sourceCode).toMatch(/text-teal-500/);
    expect(sourceCode).toMatch(/▣/);
  });

  it("renders gray styling for header blocks", () => {
    expect(sourceCode).toMatch(/text-slate-500/);
    expect(sourceCode).toMatch(/uppercase/);
  });

  it("maps previewBlocks to rendered elements", () => {
    expect(sourceCode).toMatch(/previewBlocks\.map/);
  });

  it("renders header blocks with tracking-wider style", () => {
    expect(sourceCode).toMatch(/tracking-wider/);
  });
});

// ---------------------------------------------------------------------------
// 13. Resizable split pane
// ---------------------------------------------------------------------------

describe("resizable split pane", () => {
  it("tracks splitRatio state with default 0.5", () => {
    expect(sourceCode).toMatch(/useState\s*\(\s*0\.5\s*\)/);
  });

  it("uses containerRef for the split pane container", () => {
    expect(sourceCode).toMatch(/ref=\{containerRef\}/);
  });

  it("left pane width is set from splitRatio", () => {
    expect(sourceCode).toMatch(/width:\s*`\$\{splitRatio\s*\*\s*100\}%`/);
  });

  it("right pane width is set from (1 - splitRatio)", () => {
    expect(sourceCode).toMatch(/width:\s*`\$\{\(1\s*-\s*splitRatio\)\s*\*\s*100\}%`/);
  });

  it("divider has onMouseDown handler", () => {
    expect(sourceCode).toMatch(/onMouseDown=\{handleMouseDown\}/);
  });

  it("divider has cursor-col-resize class", () => {
    expect(sourceCode).toMatch(/cursor-col-resize/);
  });

  it("handleMouseDown uses getBoundingClientRect", () => {
    expect(sourceCode).toMatch(/getBoundingClientRect\s*\(\s*\)/);
  });

  it("handleMouseDown tracks mouse movement", () => {
    expect(sourceCode).toMatch(/window\.addEventListener\s*\(\s*['"]mousemove['"]/);
    expect(sourceCode).toMatch(/window\.addEventListener\s*\(\s*['"]mouseup['"]/);
  });

  it("cleans up mouse listeners on mouseup", () => {
    expect(sourceCode).toMatch(/window\.removeEventListener\s*\(\s*['"]mousemove['"]/);
    expect(sourceCode).toMatch(/window\.removeEventListener\s*\(\s*['"]mouseup['"]/);
  });

  it("clamps split ratio between 0.15 and 0.85", () => {
    expect(sourceCode).toMatch(/Math\.min\s*\(\s*0\.85\s*,\s*Math\.max\s*\(\s*0\.15/);
  });

  it("prevents default on mousedown to avoid text selection", () => {
    expect(sourceCode).toMatch(/e\.preventDefault\s*\(\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 14. localStorage persistence for split ratio
// ---------------------------------------------------------------------------

describe("localStorage persistence", () => {
  it("uses 'script-editor-split-ratio' as localStorage key", () => {
    expect(sourceCode).toMatch(/const\s+SPLIT_KEY\s*=\s*['"]script-editor-split-ratio['"]/);
  });

  it("reads split ratio from localStorage on mount", () => {
    expect(sourceCode).toMatch(/localStorage\.getItem\s*\(\s*SPLIT_KEY\s*\)/);
  });

  it("parses stored ratio with parseFloat", () => {
    expect(sourceCode).toMatch(/parseFloat\s*\(\s*stored\s*\)/);
  });

  it("validates parsed value with Number.isNaN check", () => {
    expect(sourceCode).toMatch(/Number\.isNaN\s*\(\s*parsed\s*\)/);
  });

  it("persists split ratio to localStorage on change", () => {
    expect(sourceCode).toMatch(/localStorage\.setItem\s*\(\s*SPLIT_KEY\s*,\s*splitRatio\.toString\s*\(\s*\)\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 15. NARRATOR detection for button state
// ---------------------------------------------------------------------------

describe("NARRATOR detection", () => {
  it("uses /NARRATOR:/m regex to detect narrator blocks", () => {
    expect(sourceCode).toMatch(/\/NARRATOR:\/m\.test\s*\(\s*content\s*\)/);
  });

  it("computes hasNarrator with useMemo", () => {
    expect(sourceCode).toMatch(/const\s+hasNarrator\s*=\s*useMemo/);
  });
});

// ---------------------------------------------------------------------------
// 16. Generate TTS Script button
// ---------------------------------------------------------------------------

describe("Generate TTS Script button", () => {
  it("renders the Generate TTS Script → button text", () => {
    expect(sourceCode).toMatch(/Generate TTS Script →/);
  });

  it("button is disabled when no NARRATOR blocks detected", () => {
    expect(sourceCode).toMatch(/disabled=\{!hasNarrator\s*\|\|\s*isGenerating\}/);
  });

  it("button shows 'Generating…' text while generating", () => {
    expect(sourceCode).toMatch(/isGenerating\s*\?\s*['"]Generating…['"]/);
  });

  it("button has enabled styling when hasNarrator and not generating", () => {
    expect(sourceCode).toMatch(/bg-blue-600\s+hover:bg-blue-700\s+text-white/);
  });

  it("button has disabled styling when no narrator or generating", () => {
    expect(sourceCode).toMatch(/bg-slate-700\s+text-slate-400\s+cursor-not-allowed/);
  });
});

// ---------------------------------------------------------------------------
// 17. TTS generation trigger — POST /api/pipeline/tts-script/run
// ---------------------------------------------------------------------------

describe("TTS generation trigger", () => {
  it("POSTs to /api/pipeline/tts-script/run", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/tts-script\/run['"]\s*,\s*\{\s*method\s*:\s*['"]POST['"]\s*\}\s*\)/);
  });

  it("checks res.ok before proceeding", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!res\.ok\s*\)\s*throw/);
  });

  it("extracts jobId from response", () => {
    expect(sourceCode).toMatch(/data\?\.jobId/);
    expect(sourceCode).toMatch(/setJobId\s*\(\s*data\.jobId\s*\)/);
  });

  it("calls onAdvance() on success", () => {
    expect(sourceCode).toMatch(/onAdvance\s*\(\s*\)/);
  });

  it("tracks isGenerating state", () => {
    expect(sourceCode).toMatch(/\[\s*isGenerating\s*,\s*setIsGenerating\s*\]/);
  });

  it("sets isGenerating to true at start", () => {
    expect(sourceCode).toMatch(/setIsGenerating\s*\(\s*true\s*\)/);
  });

  it("sets isGenerating to false in finally block", () => {
    expect(sourceCode).toMatch(/finally\s*\{[\s\S]*?setIsGenerating\s*\(\s*false\s*\)/);
  });

  it("guards against double-click when already generating", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!hasNarrator\s*\|\|\s*isGenerating\s*\)\s*return/);
  });

  it("handles generation errors gracefully", () => {
    expect(sourceCode).toMatch(/catch\s*\(\s*err\s*\)\s*\{[\s\S]*?console\.error/);
  });
});

// ---------------------------------------------------------------------------
// 18. SseLogPanel integration
// ---------------------------------------------------------------------------

describe("SseLogPanel integration", () => {
  it("tracks jobId state as string | null", () => {
    expect(sourceCode).toMatch(/useState\s*<\s*string\s*\|\s*null\s*>\s*\(\s*null\s*\)/);
  });

  it("conditionally renders SseLogPanel when jobId is present", () => {
    expect(sourceCode).toMatch(/\{jobId\s*&&/);
  });

  it("passes jobId prop to SseLogPanel", () => {
    expect(sourceCode).toMatch(/<SseLogPanel\s+jobId=\{jobId\}/);
  });

  it("wraps SseLogPanel in a bordered container", () => {
    expect(sourceCode).toMatch(/border-t\s+border-slate-700/);
  });
});

// ---------------------------------------------------------------------------
// 19. Content state management
// ---------------------------------------------------------------------------

describe("content state management", () => {
  it("tracks content state with useState", () => {
    expect(sourceCode).toMatch(/\[\s*content\s*,\s*setContent\s*\]/);
  });

  it("uses contentRef to prevent unnecessary re-renders", () => {
    expect(sourceCode).toMatch(/const\s+contentRef\s*=\s*useRef/);
  });

  it("tracks loading state", () => {
    expect(sourceCode).toMatch(/\[\s*loading\s*,\s*setLoading\s*\]\s*=\s*useState\s*\(\s*true\s*\)/);
  });

  it("tracks previewBlocks state", () => {
    expect(sourceCode).toMatch(/\[\s*previewBlocks\s*,\s*setPreviewBlocks\s*\]/);
  });
});

// ---------------------------------------------------------------------------
// 20. Layout and structure
// ---------------------------------------------------------------------------

describe("layout and structure", () => {
  it("has a Stage 2 — Script Editor heading", () => {
    expect(sourceCode).toMatch(/Stage 2\s*—\s*Script Editor/);
  });

  it("uses flex-col layout for the main container", () => {
    expect(sourceCode).toMatch(/w-full\s+h-full\s+flex\s+flex-col/);
  });

  it("header has border-b and dark background", () => {
    expect(sourceCode).toMatch(/border-b\s+border-slate-700\s+bg-slate-900/);
  });

  it("split pane container has flex-1 and overflow-hidden", () => {
    expect(sourceCode).toMatch(/flex-1\s+flex\s+overflow-hidden/);
  });

  it("right pane has overflow-y-auto for scrollable preview", () => {
    expect(sourceCode).toMatch(/overflow-y-auto/);
  });
});

// ---------------------------------------------------------------------------
// 21. ScriptResponse type
// ---------------------------------------------------------------------------

describe("ScriptResponse type", () => {
  it("defines ScriptResponse type with content: string", () => {
    expect(sourceCode).toMatch(/type\s+ScriptResponse\s*=\s*\{/);
    expect(sourceCode).toMatch(/content\s*:\s*string/);
  });
});

// ---------------------------------------------------------------------------
// 22. Dark theme compliance
// ---------------------------------------------------------------------------

describe("Dark theme compliance", () => {
  it("header uses dark background instead of bg-white", () => {
    expect(sourceCode).not.toMatch(/className="[^"]*bg-white[^"]*".*Stage 2/);
    expect(sourceCode).toMatch(/bg-slate-900/);
  });

  it("header text uses light color", () => {
    expect(sourceCode).toMatch(/text-slate-100/);
  });

  it("footer/SSE panel uses dark background", () => {
    expect(sourceCode).not.toMatch(/border-t border-slate-200 bg-white/);
  });

  it("disabled button uses dark theme colors", () => {
    expect(sourceCode).not.toMatch(/bg-slate-200 text-slate-500/);
    expect(sourceCode).toMatch(/bg-slate-700 text-slate-400/);
  });

  it("split pane uses dark background", () => {
    expect(sourceCode).not.toMatch(/bg-slate-50/);
  });

  it("preview blocks use content-based keys instead of index", () => {
    // Should not have bare key={idx} without prefix
    const previewSection = sourceCode.slice(sourceCode.indexOf('previewBlocks.map'));
    expect(previewSection).not.toMatch(/key=\{idx\}/);
  });

  it("preview blocks use dark-friendly text color (not text-slate-700)", () => {
    // Preview narrator, visual, and text blocks should use text-slate-300 instead of text-slate-700
    expect(sourceCode).not.toMatch(/text-slate-700/);
    expect(sourceCode).toMatch(/text-slate-300/);
  });
});

/**
 * Tests for components/stages/Stage3TtsScriptGen.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/stage3_tts_script_gen_typescriptreact.prompt.
 *
 * Spec requirements verified:
 *   1. Props: onAdvance: () => void.
 *   2. Header: [Generate TTS Script ↺] button + last run timestamp.
 *   3. SSE log panel (SseLogPanel) shown below the button, with jobId from the latest run.
 *   4. Diff view below log: split display of main_script.md (left) and tts_script.md (right) with line coloring: added=green, removed=red, unchanged=gray.
 *   5. Inline CodeMirror editor for tts_script.md. Auto-saves on blur + 1s debounce.
 *   6. [Continue →] button enabled when tts_script.md exists. Calls onAdvance().
 *   7. 'use client' directive.
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "components", "stages", "Stage3TtsScriptGen.tsx");
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

  it("exports Stage3TtsScriptGen as default export", () => {
    expect(sourceCode).toMatch(/export\s+default\s+function\s+Stage3TtsScriptGen/);
  });
});

// ---------------------------------------------------------------------------
// 3. Props interface (Req 1)
// ---------------------------------------------------------------------------

describe("Stage3TtsScriptGen props", () => {
  it("declares onAdvance: () => void prop", () => {
    expect(sourceCode).toMatch(/onAdvance\s*:\s*\(\)\s*=>\s*void/);
  });

  it("defines Stage3TtsScriptGenProps interface", () => {
    expect(sourceCode).toMatch(/interface\s+Stage3TtsScriptGenProps/);
  });

  it("destructures onAdvance from props", () => {
    expect(sourceCode).toMatch(/\{\s*onAdvance\s*\}\s*:\s*Stage3TtsScriptGenProps/);
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

  it("imports useCallback from react", () => {
    expect(sourceCode).toMatch(/useCallback/);
  });

  it("imports useMemo from react", () => {
    expect(sourceCode).toMatch(/useMemo/);
  });

  it("imports useRef from react", () => {
    expect(sourceCode).toMatch(/useRef/);
  });

  it("imports diffLines from diff", () => {
    expect(sourceCode).toMatch(/import\s*\{.*diffLines.*\}\s*from\s+['"]diff['"]/);
  });

  it("imports CodeMirror from @uiw/react-codemirror", () => {
    expect(sourceCode).toMatch(/import\s+CodeMirror\s+from\s+['"]@uiw\/react-codemirror['"]/);
  });

  it("imports markdown from @codemirror/lang-markdown", () => {
    expect(sourceCode).toMatch(/import\s*\{.*markdown.*\}\s*from\s+['"]@codemirror\/lang-markdown['"]/);
  });

  it("imports SseLogPanel", () => {
    expect(sourceCode).toMatch(/import\s+SseLogPanel\s+from/);
  });
});

// ---------------------------------------------------------------------------
// 5. DiffLine types (Req 4)
// ---------------------------------------------------------------------------

describe("DiffLine types", () => {
  it("defines DiffLineType as union of added | removed | unchanged | empty", () => {
    expect(sourceCode).toMatch(/type\s+DiffLineType\s*=\s*['"]added['"]\s*\|\s*['"]removed['"]\s*\|\s*['"]unchanged['"]\s*\|\s*['"]empty['"]/);
  });

  it("defines DiffLine interface with type and text properties", () => {
    expect(sourceCode).toMatch(/interface\s+DiffLine/);
  });

  it("DiffLine has type: DiffLineType property", () => {
    expect(sourceCode).toMatch(/type\s*:\s*DiffLineType/);
  });

  it("DiffLine has text: string property", () => {
    expect(sourceCode).toMatch(/text\s*:\s*string/);
  });
});

// ---------------------------------------------------------------------------
// 6. State management
// ---------------------------------------------------------------------------

describe("state management", () => {
  it("tracks mainScript state", () => {
    expect(sourceCode).toMatch(/\[\s*mainScript\s*,\s*setMainScript\s*\]/);
  });

  it("tracks ttsScript state", () => {
    expect(sourceCode).toMatch(/\[\s*ttsScript\s*,\s*setTtsScript\s*\]/);
  });

  it("tracks ttsExists state as boolean", () => {
    expect(sourceCode).toMatch(/\[\s*ttsExists\s*,\s*setTtsExists\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*boolean\s*>\s*\(\s*false\s*\)/);
  });

  it("tracks jobId state as string | null", () => {
    expect(sourceCode).toMatch(/\[\s*jobId\s*,\s*setJobId\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*string\s*\|\s*null\s*>\s*\(\s*null\s*\)/);
  });

  it("tracks lastRunTime state as string | null", () => {
    expect(sourceCode).toMatch(/\[\s*lastRunTime\s*,\s*setLastRunTime\s*\]/);
  });

  it("tracks loading state", () => {
    expect(sourceCode).toMatch(/\[\s*loading\s*,\s*setLoading\s*\]/);
  });

  it("tracks saving state", () => {
    expect(sourceCode).toMatch(/\[\s*saving\s*,\s*setSaving\s*\]/);
  });

  it("uses debounceRef for timeout tracking", () => {
    expect(sourceCode).toMatch(/useRef\s*<\s*NodeJS\.Timeout\s*\|\s*null\s*>\s*\(\s*null\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 7. Script fetching on mount (Req 5)
// ---------------------------------------------------------------------------

describe("script fetching on mount", () => {
  it("fetches main script from /api/project/script?file=main", () => {
    expect(sourceCode).toMatch(/\/api\/project\/script\?file=\$\{file\}/);
  });

  it("fetches tts script from /api/project/script?file=tts", () => {
    expect(sourceCode).toMatch(/fetchScript\s*\(\s*['"]tts['"]\s*\)/);
  });

  it("uses Promise.all to fetch both scripts concurrently", () => {
    expect(sourceCode).toMatch(/Promise\.all\s*\(\s*\[\s*fetchScript\s*\(\s*['"]main['"]\s*\)\s*,\s*fetchScript\s*\(\s*['"]tts['"]\s*\)\s*\]\s*\)/);
  });

  it("parses response as JSON and extracts content", () => {
    expect(sourceCode).toMatch(/res\.json\s*\(\s*\)/);
    expect(sourceCode).toMatch(/data\?\.content\s*\?\?\s*null/);
  });

  it("returns null on fetch failure", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!res\.ok\s*\)\s*return\s+null/);
  });

  it("returns null on catch", () => {
    expect(sourceCode).toMatch(/catch\s*\{[\s\S]*?return\s+null/);
  });

  it("sets ttsExists based on whether tts script was fetched", () => {
    expect(sourceCode).toMatch(/setTtsExists\s*\(\s*Boolean\s*\(\s*tts\s*\)\s*\)/);
  });

  it("sets loading to true at start and false when done", () => {
    expect(sourceCode).toMatch(/setLoading\s*\(\s*true\s*\)/);
    expect(sourceCode).toMatch(/setLoading\s*\(\s*false\s*\)/);
  });

  it("uses useCallback for fetchScript", () => {
    expect(sourceCode).toMatch(/const\s+fetchScript\s*=\s*useCallback/);
  });

  it("uses useCallback for loadScripts", () => {
    expect(sourceCode).toMatch(/const\s+loadScripts\s*=\s*useCallback/);
  });

  it("calls loadScripts in useEffect on mount", () => {
    expect(sourceCode).toMatch(/useEffect\s*\(\s*\(\)\s*=>\s*\{[\s\S]*?loadScripts\s*\(\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 8. localStorage persistence for lastRunTime (Req 2)
// ---------------------------------------------------------------------------

describe("localStorage persistence", () => {
  it("defines LAST_RUN_KEY constant as 'tts-script-last-run'", () => {
    expect(sourceCode).toMatch(/const\s+LAST_RUN_KEY\s*=\s*['"]tts-script-last-run['"]/);
  });

  it("reads lastRunTime from localStorage on mount", () => {
    expect(sourceCode).toMatch(/localStorage\.getItem\s*\(\s*LAST_RUN_KEY\s*\)/);
  });

  it("stores lastRunTime to localStorage on generate", () => {
    expect(sourceCode).toMatch(/localStorage\.setItem\s*\(\s*LAST_RUN_KEY\s*,\s*ts\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 9. Save TTS script — POST /api/project/script?file=tts (Req 5)
// ---------------------------------------------------------------------------

describe("save TTS script", () => {
  it("POSTs to /api/project/script?file=tts", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/project\/script\?file=tts['"]/);
  });

  it("uses POST method", () => {
    expect(sourceCode).toMatch(/method\s*:\s*['"]POST['"]/);
  });

  it("sends Content-Type: text/plain header", () => {
    expect(sourceCode).toMatch(/['"]Content-Type['"]\s*:\s*['"]text\/plain['"]/);
  });

  it("sends content as body", () => {
    expect(sourceCode).toMatch(/body\s*:\s*content/);
  });

  it("guards against double save with savingRef", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*savingRef\.current\s*\)/);
  });

  it("sets saving to true at start", () => {
    expect(sourceCode).toMatch(/setSaving\s*\(\s*true\s*\)/);
  });

  it("sets saving to false in finally block", () => {
    expect(sourceCode).toMatch(/finally\s*\{[\s\S]*?setSaving\s*\(\s*false\s*\)/);
  });

  it("updates ttsExists based on trimmed content", () => {
    expect(sourceCode).toMatch(/setTtsExists\s*\(\s*Boolean\s*\(\s*content\.trim\s*\(\s*\)\s*\)\s*\)/);
  });

  it("uses useCallback for saveTtsScript", () => {
    expect(sourceCode).toMatch(/const\s+saveTtsScript\s*=\s*useCallback/);
  });
});

// ---------------------------------------------------------------------------
// 10. Editor change with debounce (Req 5)
// ---------------------------------------------------------------------------

describe("editor change with debounce", () => {
  it("defines handleEditorChange function", () => {
    expect(sourceCode).toMatch(/const\s+handleEditorChange\s*=/);
  });

  it("updates ttsScript state on change", () => {
    expect(sourceCode).toMatch(/setTtsScript\s*\(\s*value\s*\)/);
  });

  it("clears existing debounce timeout", () => {
    expect(sourceCode).toMatch(/clearTimeout\s*\(\s*debounceRef\.current\s*\)/);
  });

  it("sets 1 second debounce timeout for auto-save", () => {
    expect(sourceCode).toMatch(/setTimeout\s*\(\s*\(\)\s*=>\s*\{[\s\S]*?saveTtsScript[\s\S]*?\}\s*,\s*1000\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 11. Editor blur handler (Req 5)
// ---------------------------------------------------------------------------

describe("editor blur handler", () => {
  it("defines handleEditorBlur function", () => {
    expect(sourceCode).toMatch(/const\s+handleEditorBlur\s*=/);
  });

  it("clears debounce on blur", () => {
    expect(sourceCode).toMatch(/handleEditorBlur[\s\S]*?clearTimeout\s*\(\s*debounceRef\.current\s*\)/);
  });

  it("immediately saves ttsScript on blur", () => {
    expect(sourceCode).toMatch(/handleEditorBlur[\s\S]*?saveTtsScript\s*\(\s*ttsScript\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 12. Generate TTS Script handler (Req 2)
// ---------------------------------------------------------------------------

describe("generate TTS script handler", () => {
  it("defines handleGenerate as async function", () => {
    expect(sourceCode).toMatch(/const\s+handleGenerate\s*=\s*async/);
  });

  it("POSTs to /api/pipeline/tts-script/run", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/tts-script\/run['"]\s*,\s*\{\s*method\s*:\s*['"]POST['"]\s*\}\s*\)/);
  });

  it("checks res.ok before proceeding", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!res\.ok\s*\)\s*return/);
  });

  it("extracts jobId from response JSON", () => {
    expect(sourceCode).toMatch(/data\?\.jobId/);
    expect(sourceCode).toMatch(/setJobId\s*\(\s*data\.jobId\s*\)/);
  });

  it("stores timestamp via new Date().toISOString()", () => {
    expect(sourceCode).toMatch(/new\s+Date\s*\(\s*\)\.toISOString\s*\(\s*\)/);
  });

  it("updates lastRunTime in state", () => {
    expect(sourceCode).toMatch(/setLastRunTime\s*\(\s*ts\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 13. Diff computation with useMemo (Req 4)
// ---------------------------------------------------------------------------

describe("diff computation", () => {
  it("uses useMemo for diffLinesComputed", () => {
    expect(sourceCode).toMatch(/const\s+diffLinesComputed\s*=\s*useMemo/);
  });

  it("calls diffLines from the diff library", () => {
    expect(sourceCode).toMatch(/diffLines\s*\(\s*mainScript/);
  });

  it("initializes left and right DiffLine arrays", () => {
    expect(sourceCode).toMatch(/const\s+left\s*:\s*DiffLine\[\]\s*=\s*\[\]/);
    expect(sourceCode).toMatch(/const\s+right\s*:\s*DiffLine\[\]\s*=\s*\[\]/);
  });

  it("splits diff parts by newline", () => {
    expect(sourceCode).toMatch(/part\.value\.split\s*\(\s*'\\n'\s*\)/);
  });

  it("pops trailing empty string from split", () => {
    expect(sourceCode).toMatch(/lines\.pop\s*\(\s*\)/);
  });

  it("marks added lines with type 'added' on right, 'empty' on left", () => {
    expect(sourceCode).toMatch(/part\.added/);
    expect(sourceCode).toMatch(/left\.push\s*\(\s*\{\s*type\s*:\s*['"]empty['"]/);
    expect(sourceCode).toMatch(/right\.push\s*\(\s*\{\s*type\s*:\s*['"]added['"]/);
  });

  it("marks removed lines with type 'removed' on left, 'empty' on right", () => {
    expect(sourceCode).toMatch(/part\.removed/);
    expect(sourceCode).toMatch(/left\.push\s*\(\s*\{\s*type\s*:\s*['"]removed['"]/);
    expect(sourceCode).toMatch(/right\.push\s*\(\s*\{\s*type\s*:\s*['"]empty['"]/);
  });

  it("marks unchanged lines with type 'unchanged' on both sides", () => {
    expect(sourceCode).toMatch(/left\.push\s*\(\s*\{\s*type\s*:\s*['"]unchanged['"]\s*,\s*text\s*:\s*line\s*\}\s*\)/);
    expect(sourceCode).toMatch(/right\.push\s*\(\s*\{\s*type\s*:\s*['"]unchanged['"]\s*,\s*text\s*:\s*line\s*\}\s*\)/);
  });

  it("returns object with left and right arrays", () => {
    expect(sourceCode).toMatch(/return\s*\{\s*left\s*,\s*right\s*\}/);
  });

  it("depends on mainScript and ttsScript", () => {
    expect(sourceCode).toMatch(/\[\s*mainScript\s*,\s*ttsScript\s*\]/);
  });
});

// ---------------------------------------------------------------------------
// 14. Line class helper (Req 4)
// ---------------------------------------------------------------------------

describe("lineClass helper", () => {
  it("defines lineClass function", () => {
    expect(sourceCode).toMatch(/const\s+lineClass\s*=/);
  });

  it("returns text-green-400 for added lines", () => {
    expect(sourceCode).toMatch(/case\s+['"]added['"]\s*:\s*\n\s*return\s+['"]text-green-400['"]/);
  });

  it("returns text-red-400 for removed lines", () => {
    expect(sourceCode).toMatch(/case\s+['"]removed['"]\s*:\s*\n\s*return\s+['"]text-red-400['"]/);
  });

  it("returns text-gray-400 for unchanged lines", () => {
    expect(sourceCode).toMatch(/case\s+['"]unchanged['"]\s*:\s*\n\s*return\s+['"]text-gray-400['"]/);
  });

  it("returns text-transparent for empty/default lines", () => {
    expect(sourceCode).toMatch(/return\s+['"]text-transparent['"]/);
  });
});

// ---------------------------------------------------------------------------
// 15. Header — Generate button + timestamp (Req 2)
// ---------------------------------------------------------------------------

describe("header section", () => {
  it("renders Generate TTS Script ↺ button text", () => {
    expect(sourceCode).toMatch(/Generate TTS Script ↺/);
  });

  it("button has onClick={handleGenerate}", () => {
    expect(sourceCode).toMatch(/onClick=\{handleGenerate\}/);
  });

  it("button uses blue styling", () => {
    expect(sourceCode).toMatch(/bg-blue-600\s+text-white/);
  });

  it("displays last run timestamp when available", () => {
    expect(sourceCode).toMatch(/Last run:/);
    expect(sourceCode).toMatch(/new\s+Date\s*\(\s*lastRunTime\s*\)\.toLocaleString\s*\(\s*\)/);
  });

  it("shows dash when no lastRunTime", () => {
    expect(sourceCode).toMatch(/lastRunTime\s*\?\s*new\s+Date\s*\(\s*lastRunTime\s*\)\.toLocaleString\s*\(\s*\)\s*:\s*['"]—['"]/);
  });
});

// ---------------------------------------------------------------------------
// 16. SSE Log Panel integration (Req 3)
// ---------------------------------------------------------------------------

describe("SseLogPanel integration", () => {
  it("renders SseLogPanel component", () => {
    expect(sourceCode).toMatch(/<SseLogPanel/);
  });

  it("passes jobId prop to SseLogPanel", () => {
    expect(sourceCode).toMatch(/<SseLogPanel\s+jobId=\{jobId\}/);
  });
});

// ---------------------------------------------------------------------------
// 17. Diff view layout (Req 4)
// ---------------------------------------------------------------------------

describe("diff view layout", () => {
  it("uses a two-column grid for diff display", () => {
    expect(sourceCode).toMatch(/grid\s+grid-cols-2\s+gap-4/);
  });

  it("labels left column as main_script.md", () => {
    expect(sourceCode).toMatch(/main_script\.md/);
  });

  it("labels right column as tts_script.md", () => {
    expect(sourceCode).toMatch(/tts_script\.md/);
  });

  it("uses <pre> for diff display with overflow-x-auto", () => {
    expect(sourceCode).toMatch(/<pre\s+className="overflow-x-auto/);
  });

  it("maps left diff lines to rendered elements", () => {
    expect(sourceCode).toMatch(/diffLinesComputed\.left\.map/);
  });

  it("maps right diff lines to rendered elements", () => {
    expect(sourceCode).toMatch(/diffLinesComputed\.right\.map/);
  });

  it("uses lineClass for diff line styling", () => {
    expect(sourceCode).toMatch(/className=\{lineClass\(line\.type\)\}/);
  });

  it("uses unique keys for left diff lines", () => {
    expect(sourceCode).toMatch(/key=\{`left-\$\{idx\}`\}/);
  });

  it("uses unique keys for right diff lines", () => {
    expect(sourceCode).toMatch(/key=\{`right-\$\{idx\}`\}/);
  });
});

// ---------------------------------------------------------------------------
// 18. CodeMirror editor (Req 5)
// ---------------------------------------------------------------------------

describe("CodeMirror editor", () => {
  it("renders CodeMirror component", () => {
    expect(sourceCode).toMatch(/<CodeMirror/);
  });

  it("binds editor value to ttsScript state", () => {
    expect(sourceCode).toMatch(/value=\{ttsScript\}/);
  });

  it("sets editor height to 300px", () => {
    expect(sourceCode).toMatch(/height="300px"/);
  });

  it("uses markdown extension", () => {
    expect(sourceCode).toMatch(/extensions=\{\[markdown\(\)\]\}/);
  });

  it("handles onChange with handleEditorChange", () => {
    expect(sourceCode).toMatch(/onChange=\{handleEditorChange\}/);
  });

  it("handles onBlur with handleEditorBlur", () => {
    expect(sourceCode).toMatch(/onBlur=\{handleEditorBlur\}/);
  });

  it("uses dark theme", () => {
    expect(sourceCode).toMatch(/theme="dark"/);
  });

  it("labels the editor section as Edit tts_script.md", () => {
    expect(sourceCode).toMatch(/Edit tts_script\.md/);
  });

  it("shows Saving… indicator when saving", () => {
    expect(sourceCode).toMatch(/saving\s*&&/);
    expect(sourceCode).toMatch(/Saving…/);
  });
});

// ---------------------------------------------------------------------------
// 19. Continue button (Req 6)
// ---------------------------------------------------------------------------

describe("Continue button", () => {
  it("renders Continue → button text", () => {
    expect(sourceCode).toMatch(/Continue →/);
  });

  it("button calls onAdvance on click", () => {
    expect(sourceCode).toMatch(/onClick=\{onAdvance\}/);
  });

  it("button is disabled when ttsExists is false", () => {
    expect(sourceCode).toMatch(/disabled=\{!ttsExists\}/);
  });

  it("uses the shared PipelineAdvanceButton component", () => {
    expect(sourceCode).toMatch(/PipelineAdvanceButton/);
  });

  it("button uses shared disabled styling when ttsExists is false", () => {
    expect(sourceCode).toMatch(/disabled=\{!ttsExists\}/);
    expect(sourceCode).toMatch(/PipelineAdvanceButton/);
  });

  it("does not hardcode a separate render-audio label anymore", () => {
    expect(sourceCode).not.toMatch(/Render Audio →/);
  });
});

// ---------------------------------------------------------------------------
// 20. Layout and structure
// ---------------------------------------------------------------------------

describe("layout and structure", () => {
  it("uses space-y-6 for main layout spacing", () => {
    expect(sourceCode).toMatch(/className="w-full\s+space-y-6"/);
  });

  it("uses flex items-center justify-between for header", () => {
    expect(sourceCode).toMatch(/flex\s+items-center\s+justify-between/);
  });

  it("uses flex justify-end for advance button container", () => {
    expect(sourceCode).toMatch(/flex\s+justify-end/);
  });
});

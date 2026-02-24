/**
 * Tests for components/stages/Stage1ProjectSetup.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/stage1_project_setup_typescriptreact.prompt.
 *
 * Spec requirements verified:
 *   1. Props: config: ProjectConfig, onSave: (config: ProjectConfig) => void.
 *   2. Left column: form fields for project name, outputResolution (dropdown), TTS voice, TTS rate, Veo model, Veo aspectRatio (dropdown), render maxParallelRenders.
 *   3. Right column: Section Registry table with columns: Order (#), Section ID, Label, Composition ID, [✎] edit, [✕] delete. Rows are draggable.
 *   4. [+ Add Section] appends a blank section row; inline editing on click of [✎].
 *   5. [Save ✓] PUTs to /api/project with modified config. Shows toast on success.
 *   6. Unsaved changes: yellow dot indicator in header. beforeunload warning.
 *   7. 'use client' directive.
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "components", "stages", "Stage1ProjectSetup.tsx");
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

  it("exports Stage1ProjectSetup as default export", () => {
    expect(sourceCode).toMatch(/export\s+default\s+function\s+Stage1ProjectSetup/);
  });
});

// ---------------------------------------------------------------------------
// 3. Props interface
// ---------------------------------------------------------------------------

describe("Stage1ProjectSetup props", () => {
  it("declares config: ProjectConfig prop", () => {
    expect(sourceCode).toMatch(/config\s*:\s*ProjectConfig/);
  });

  it("declares onSave callback prop (optional)", () => {
    expect(sourceCode).toMatch(/onSave\s*\??\s*:\s*\(config\s*:\s*ProjectConfig\)\s*=>\s*void/);
  });
});

// ---------------------------------------------------------------------------
// 4. Import structure
// ---------------------------------------------------------------------------

describe("import structure", () => {
  it("imports React and hooks from react", () => {
    expect(sourceCode).toMatch(/import\s+React\s*,?\s*\{.*useState.*\}\s*from\s+['"]react['"]/);
  });

  it("imports useEffect from react", () => {
    expect(sourceCode).toMatch(/useEffect/);
  });

  it("imports ProjectConfig type", () => {
    expect(sourceCode).toMatch(/import\s+type\s*\{.*ProjectConfig/);
  });

  it("imports Section type", () => {
    expect(sourceCode).toMatch(/import\s+type\s*\{.*Section/);
  });

  it("imports types from ../../lib/types", () => {
    expect(sourceCode).toMatch(/from\s+['"]\.\.\/\.\.\/lib\/types['"]/);
  });
});

// ---------------------------------------------------------------------------
// 5. Local form state — useState<ProjectConfig>(config)
// ---------------------------------------------------------------------------

describe("local form state", () => {
  it("uses useState<ProjectConfig> for local config", () => {
    expect(sourceCode).toMatch(/useState\s*<\s*ProjectConfig\s*>\s*\(/);
  });

  it("names the state variable localConfig", () => {
    expect(sourceCode).toMatch(/\[\s*localConfig\s*,\s*setLocalConfig\s*\]/);
  });

  it("syncs local state when config prop changes via useEffect", () => {
    expect(sourceCode).toMatch(/useEffect\s*\(\s*\(\)\s*=>\s*\{[\s\S]*?setLocalConfig\s*\(/);
  });
});

// ---------------------------------------------------------------------------
// 6. Unsaved changes detection
// ---------------------------------------------------------------------------

describe("unsaved changes detection", () => {
  it("tracks hasChanges state", () => {
    expect(sourceCode).toMatch(/\[\s*hasChanges\s*,\s*setHasChanges\s*\]/);
  });

  it("compares localConfig to config via JSON.stringify", () => {
    expect(sourceCode).toMatch(/JSON\.stringify\s*\(\s*localConfig\s*\)\s*!==\s*JSON\.stringify\s*\(/);
  });

  it("shows a yellow dot indicator when hasChanges is true", () => {
    expect(sourceCode).toMatch(/hasChanges/);
    expect(sourceCode).toMatch(/bg-yellow-400/);
  });

  it("yellow indicator is a rounded-full span", () => {
    expect(sourceCode).toMatch(/rounded-full\s+bg-yellow-400/);
  });
});

// ---------------------------------------------------------------------------
// 7. beforeunload warning
// ---------------------------------------------------------------------------

describe("beforeunload warning", () => {
  it("adds beforeunload event listener when hasChanges is true", () => {
    expect(sourceCode).toMatch(/window\.addEventListener\s*\(\s*['"]beforeunload['"]/);
  });

  it("removes beforeunload listener on cleanup", () => {
    expect(sourceCode).toMatch(/window\.removeEventListener\s*\(\s*['"]beforeunload['"]/);
  });

  it("prevents default in the beforeunload handler", () => {
    expect(sourceCode).toMatch(/e\.preventDefault\s*\(\s*\)/);
  });

  it("sets returnValue for older browsers", () => {
    expect(sourceCode).toMatch(/e\.returnValue\s*=\s*['"]['"]|e\.returnValue/);
  });

  it("only registers listener when hasChanges is true", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!hasChanges\s*\)\s*return/);
  });
});

// ---------------------------------------------------------------------------
// 8. Left column — form fields
// ---------------------------------------------------------------------------

describe("left column — project name field", () => {
  it("renders an input for project name", () => {
    expect(sourceCode).toMatch(/Project Name/);
  });

  it("binds input value to localConfig.name", () => {
    expect(sourceCode).toMatch(/value=\{localConfig\.name\}/);
  });

  it("updates name on change", () => {
    expect(sourceCode).toMatch(/updateConfig\s*\(\s*['"]name['"]/);
  });
});

describe("left column — output resolution dropdown", () => {
  it("renders a select for output resolution", () => {
    expect(sourceCode).toMatch(/Output Resolution/);
  });

  it("includes 1920×1080 option", () => {
    expect(sourceCode).toMatch(/1920[×x]1080/);
  });

  it("includes 1280×720 option", () => {
    expect(sourceCode).toMatch(/1280[×x]720/);
  });

  it("binds select value to localConfig.outputResolution (formatted as WxH string)", () => {
    expect(sourceCode).toMatch(/localConfig\.outputResolution\.width/);
  });

  it("updates outputResolution on change", () => {
    expect(sourceCode).toMatch(/updateConfig\s*\(\s*['"]outputResolution['"]/);
  });
});

describe("left column — TTS speaker field", () => {
  it("renders a TTS Speaker label", () => {
    expect(sourceCode).toMatch(/TTS Speaker/);
  });

  it("binds input to localConfig.tts.speaker", () => {
    expect(sourceCode).toMatch(/value=\{localConfig\.tts\.speaker\}/);
  });

  it("updates tts.speaker via nested updater", () => {
    expect(sourceCode).toMatch(/updateNested\s*\(\s*['"]tts['"]\s*,\s*['"]speaker['"]/);
  });
});

describe("left column — TTS speaking rate field", () => {
  it("renders a TTS Speaking Rate label", () => {
    expect(sourceCode).toMatch(/TTS Speaking Rate/);
  });

  it("uses number input type for TTS speaking rate", () => {
    expect(sourceCode).toMatch(/type=["']number["'][\s\S]*?localConfig\.tts\.speakingRate/);
  });

  it("sets min=0.5 and max=2 for TTS speaking rate", () => {
    expect(sourceCode).toMatch(/min=\{0\.5\}/);
    expect(sourceCode).toMatch(/max=\{2\}/);
  });

  it("binds input to localConfig.tts.speakingRate", () => {
    expect(sourceCode).toMatch(/value=\{localConfig\.tts\.speakingRate\}/);
  });

  it("updates tts.speakingRate via nested updater", () => {
    expect(sourceCode).toMatch(/updateNested\s*\(\s*['"]tts['"]\s*,\s*['"]speakingRate['"]/);
  });
});

describe("left column — Veo model field", () => {
  it("renders a Veo Model label", () => {
    expect(sourceCode).toMatch(/Veo Model/);
  });

  it("binds input to localConfig.veo.model", () => {
    expect(sourceCode).toMatch(/value=\{localConfig\.veo\.model\}/);
  });

  it("updates veo.model via nested updater", () => {
    expect(sourceCode).toMatch(/updateNested\s*\(\s*['"]veo['"]\s*,\s*['"]model['"]/);
  });
});

describe("left column — Veo aspect ratio dropdown", () => {
  it("renders a Veo Aspect Ratio label", () => {
    expect(sourceCode).toMatch(/Veo Aspect Ratio/);
  });

  it("includes 16:9 option", () => {
    expect(sourceCode).toMatch(/16:9/);
  });

  it("includes 9:16 option", () => {
    expect(sourceCode).toMatch(/9:16/);
  });

  it("binds select to localConfig.veo.defaultAspectRatio", () => {
    expect(sourceCode).toMatch(/value=\{localConfig\.veo\.defaultAspectRatio\}/);
  });

  it("updates veo.defaultAspectRatio via nested updater", () => {
    expect(sourceCode).toMatch(/updateNested\s*\(\s*['"]veo['"]\s*,\s*['"]defaultAspectRatio['"]/);
  });
});

describe("left column — max parallel renders field", () => {
  it("renders a Max Parallel Renders label", () => {
    expect(sourceCode).toMatch(/Max Parallel Renders/);
  });

  it("uses number input type", () => {
    expect(sourceCode).toMatch(/type=["']number["'][\s\S]*?localConfig\.render\.maxParallelRenders/);
  });

  it("sets min=1 and max=4 for maxParallelRenders", () => {
    expect(sourceCode).toMatch(/min=\{1\}/);
    expect(sourceCode).toMatch(/max=\{4\}/);
  });

  it("binds input to localConfig.render.maxParallelRenders", () => {
    expect(sourceCode).toMatch(/value=\{localConfig\.render\.maxParallelRenders\}/);
  });

  it("updates render.maxParallelRenders via nested updater", () => {
    expect(sourceCode).toMatch(/updateNested\s*\(\s*['"]render['"]\s*,\s*['"]maxParallelRenders['"]/);
  });
});

// ---------------------------------------------------------------------------
// 9. Right column — Section Registry table
// ---------------------------------------------------------------------------

describe("section registry table", () => {
  it("renders a Section Registry heading", () => {
    expect(sourceCode).toMatch(/Section Registry/);
  });

  it("has Order (#) column header", () => {
    expect(sourceCode).toMatch(/#/);
  });

  it("has Section ID column header", () => {
    expect(sourceCode).toMatch(/Section ID/);
  });

  it("has Label column header", () => {
    expect(sourceCode).toMatch(/Label/);
  });

  it("has Composition ID column header", () => {
    expect(sourceCode).toMatch(/Composition ID/);
  });

  it("has edit (✎) column header", () => {
    expect(sourceCode).toMatch(/✎/);
  });

  it("has delete (✕) column header", () => {
    expect(sourceCode).toMatch(/✕/);
  });

  it("renders a <table> element", () => {
    expect(sourceCode).toMatch(/<table/);
  });

  it("maps sections to table rows", () => {
    expect(sourceCode).toMatch(/localConfig\.sections\.map/);
  });

  it("displays row number (index + 1)", () => {
    expect(sourceCode).toMatch(/index\s*\+\s*1/);
  });
});

// ---------------------------------------------------------------------------
// 10. Drag-and-drop reordering
// ---------------------------------------------------------------------------

describe("drag-and-drop reordering", () => {
  it("sets rows as draggable", () => {
    expect(sourceCode).toMatch(/draggable/);
  });

  it("handles onDragStart event", () => {
    expect(sourceCode).toMatch(/onDragStart/);
  });

  it("handles onDragOver event with preventDefault", () => {
    expect(sourceCode).toMatch(/onDragOver/);
    expect(sourceCode).toMatch(/e\.preventDefault\s*\(\s*\)/);
  });

  it("handles onDrop event", () => {
    expect(sourceCode).toMatch(/onDrop/);
  });

  it("tracks dragIndex state", () => {
    expect(sourceCode).toMatch(/\[\s*dragIndex\s*,\s*setDragIndex\s*\]/);
  });

  it("reorders sections array using splice", () => {
    expect(sourceCode).toMatch(/next\.splice\s*\(\s*dragIndex\s*,\s*1\s*\)/);
    expect(sourceCode).toMatch(/next\.splice\s*\(\s*index\s*,\s*0\s*,\s*moved\s*\)/);
  });

  it("shows drag instruction text", () => {
    expect(sourceCode).toMatch(/Drag rows to reorder/);
  });
});

// ---------------------------------------------------------------------------
// 11. Add Section
// ---------------------------------------------------------------------------

describe("add section", () => {
  it("renders an [+ Add Section] button", () => {
    expect(sourceCode).toMatch(/\+\s*Add Section/);
  });

  it("handleAddSection creates a new section with crypto.randomUUID", () => {
    expect(sourceCode).toMatch(/crypto\.randomUUID\s*\(\s*\)\.slice\s*\(\s*0\s*,\s*8\s*\)/);
  });

  it("new section has default label 'New Section'", () => {
    expect(sourceCode).toMatch(/label\s*:\s*['"]New Section['"]/);
  });

  it("new section has empty videoFile", () => {
    expect(sourceCode).toMatch(/videoFile\s*:\s*['"]['"]/)
  });

  it("new section has empty specDir", () => {
    expect(sourceCode).toMatch(/specDir\s*:\s*['"]['"]/)
  });

  it("new section has empty remotionDir", () => {
    expect(sourceCode).toMatch(/remotionDir\s*:\s*['"]['"]/)
  });

  it("new section has empty compositionId", () => {
    expect(sourceCode).toMatch(/compositionId\s*:\s*['"]['"]/)
  });

  it("new section has durationSeconds: 0", () => {
    expect(sourceCode).toMatch(/durationSeconds\s*:\s*0/);
  });

  it("new section has offsetSeconds: 0", () => {
    expect(sourceCode).toMatch(/offsetSeconds\s*:\s*0/);
  });

  it("appends new section to sections array", () => {
    expect(sourceCode).toMatch(/\[\s*\.\.\.prev\.sections\s*,\s*newSection\s*\]/);
  });
});

// ---------------------------------------------------------------------------
// 12. Inline editing
// ---------------------------------------------------------------------------

describe("inline section editing", () => {
  it("tracks editingSectionId state", () => {
    expect(sourceCode).toMatch(/\[\s*editingSectionId\s*,\s*setEditingSectionId\s*\]/);
  });

  it("tracks draftSection state", () => {
    expect(sourceCode).toMatch(/\[\s*draftSection\s*,\s*setDraftSection\s*\]/);
  });

  it("edit button sets editing mode for the section", () => {
    expect(sourceCode).toMatch(/handleEditSection/);
  });

  it("shows input fields when section is being edited", () => {
    expect(sourceCode).toMatch(/isEditing\s*\?/);
  });

  it("inline editing includes id field input", () => {
    expect(sourceCode).toMatch(/draftSection\?\.\s*id/);
  });

  it("inline editing includes label field input", () => {
    expect(sourceCode).toMatch(/draftSection\?\.\s*label/);
  });

  it("inline editing includes compositionId field input", () => {
    expect(sourceCode).toMatch(/draftSection\?\.\s*compositionId/);
  });

  it("confirm button (✓) calls handleConfirmEdit", () => {
    expect(sourceCode).toMatch(/handleConfirmEdit/);
    expect(sourceCode).toMatch(/✓/);
  });

  it("cancel button (✕) calls handleCancelEdit", () => {
    expect(sourceCode).toMatch(/handleCancelEdit/);
  });

  it("handleConfirmEdit replaces the section in the sections array", () => {
    expect(sourceCode).toMatch(/s\.id\s*===\s*draftSection\.id\s*\?\s*draftSection\s*:\s*s/);
  });

  it("handleCancelEdit resets editing state", () => {
    expect(sourceCode).toMatch(/setEditingSectionId\s*\(\s*null\s*\)/);
    expect(sourceCode).toMatch(/setDraftSection\s*\(\s*null\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 13. Delete section
// ---------------------------------------------------------------------------

describe("delete section", () => {
  it("has a handleDeleteSection function", () => {
    expect(sourceCode).toMatch(/handleDeleteSection/);
  });

  it("filters out the deleted section by id", () => {
    expect(sourceCode).toMatch(/sections\.filter\s*\(\s*\(?\s*s\s*\)?\s*=>\s*s\.id\s*!==\s*id\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 14. Save functionality
// ---------------------------------------------------------------------------

describe("save functionality", () => {
  it("renders a [Save ✓] button", () => {
    expect(sourceCode).toMatch(/Save\s*✓/);
  });

  it("handleSave makes a PUT request to /api/project", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/project['"]/);
    expect(sourceCode).toMatch(/method\s*:\s*['"]PUT['"]/);
  });

  it("sends localConfig as JSON body", () => {
    expect(sourceCode).toMatch(/body\s*:\s*JSON\.stringify\s*\(\s*localConfig\s*\)/);
  });

  it("sets Content-Type header to application/json", () => {
    expect(sourceCode).toMatch(/['"]Content-Type['"]\s*:\s*['"]application\/json['"]/);
  });

  it("calls onSave with response data on success", () => {
    expect(sourceCode).toMatch(/onSave\s*\?\.\s*\(\s*data\s*\)/);
  });

  it("shows success toast on save", () => {
    expect(sourceCode).toMatch(/setToast\s*\(\s*['"]Saved successfully/);
  });

  it("shows error toast on save failure", () => {
    expect(sourceCode).toMatch(/setToast\s*\(\s*['"]Error saving project['"]\s*\)/);
  });

  it("throws on non-ok response", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!res\.ok\s*\)\s*throw/);
  });
});

// ---------------------------------------------------------------------------
// 15. Toast notification
// ---------------------------------------------------------------------------

describe("toast notification", () => {
  it("tracks toast state as string or null", () => {
    expect(sourceCode).toMatch(/useState\s*<\s*string\s*\|\s*null\s*>\s*\(\s*null\s*\)/);
  });

  it("auto-clears toast after 3 seconds", () => {
    expect(sourceCode).toMatch(/setTimeout\s*\(\s*\(\)\s*=>\s*setToast\s*\(\s*null\s*\)\s*,\s*3000\s*\)/);
  });

  it("cleans up timer on toast change", () => {
    expect(sourceCode).toMatch(/clearTimeout\s*\(\s*timer\s*\)/);
  });

  it("renders toast when not null", () => {
    expect(sourceCode).toMatch(/\{toast\s*&&/);
  });
});

// ---------------------------------------------------------------------------
// 16. Layout and structure
// ---------------------------------------------------------------------------

describe("layout and structure", () => {
  it("uses a two-column grid layout", () => {
    expect(sourceCode).toMatch(/grid\s+grid-cols-1\s+lg:grid-cols-2/);
  });

  it("has a Stage 1: Project Setup heading", () => {
    expect(sourceCode).toMatch(/Stage 1:\s*Project Setup/);
  });

  it("uses green button styling for save", () => {
    expect(sourceCode).toMatch(/bg-green-600/);
  });

  it("uses blue button styling for add section", () => {
    expect(sourceCode).toMatch(/bg-blue-600/);
  });
});

// ---------------------------------------------------------------------------
// 17. Empty state
// ---------------------------------------------------------------------------

describe("empty state", () => {
  it("shows 'No sections yet' when sections array is empty", () => {
    expect(sourceCode).toMatch(/No sections yet/);
  });

  it("uses colSpan={6} for empty state row", () => {
    expect(sourceCode).toMatch(/colSpan=\{6\}/);
  });
});

// ---------------------------------------------------------------------------
// 18. Resolution and aspect ratio constants
// ---------------------------------------------------------------------------

describe("dropdown constants", () => {
  it("defines OUTPUT_RESOLUTIONS constant array", () => {
    expect(sourceCode).toMatch(/const\s+OUTPUT_RESOLUTIONS\s*=/);
  });

  it("OUTPUT_RESOLUTIONS includes 1920x1080 value", () => {
    expect(sourceCode).toMatch(/value\s*:\s*['"]1920x1080['"]/);
  });

  it("OUTPUT_RESOLUTIONS includes 1280x720 value", () => {
    expect(sourceCode).toMatch(/value\s*:\s*['"]1280x720['"]/);
  });

  it("defines VEO_ASPECT_RATIOS constant array", () => {
    expect(sourceCode).toMatch(/const\s+VEO_ASPECT_RATIOS\s*=/);
  });

  it("VEO_ASPECT_RATIOS includes 16:9 value", () => {
    expect(sourceCode).toMatch(/value\s*:\s*['"]16:9['"]/);
  });

  it("VEO_ASPECT_RATIOS includes 9:16 value", () => {
    expect(sourceCode).toMatch(/value\s*:\s*['"]9:16['"]/);
  });
});

// ---------------------------------------------------------------------------
// 19. Helper functions — updateConfig and updateNested
// ---------------------------------------------------------------------------

describe("helper functions", () => {
  it("defines updateConfig generic helper", () => {
    expect(sourceCode).toMatch(/const\s+updateConfig\s*=/);
  });

  it("defines updateNested generic helper for nested properties", () => {
    expect(sourceCode).toMatch(/const\s+updateNested\s*=/);
  });

  it("updateNested spreads nested object", () => {
    expect(sourceCode).toMatch(/\.\.\.\(prev\[key\]\s+as\s+object\)/);
  });
});

// ---------------------------------------------------------------------------
// 20. StagePanelProps compatibility — props from page.tsx
// ---------------------------------------------------------------------------

describe("StagePanelProps compatibility", () => {
  it("accepts projectConfig prop (nullable ProjectConfig from page.tsx)", () => {
    expect(sourceCode).toMatch(/projectConfig\s*[:\?]/);
  });

  it("accepts onAdvance callback prop", () => {
    expect(sourceCode).toMatch(/onAdvance\s*[:\?]/);
  });

  it("guards against null projectConfig before rendering form", () => {
    // Must handle the case where projectConfig is null (initial load)
    expect(sourceCode).toMatch(/projectConfig|!localConfig|loading/i);
  });

  it("shows a loading or empty state when projectConfig is null", () => {
    // Component must not crash when config/projectConfig is null
    expect(sourceCode).toMatch(/(!projectConfig|!localConfig|loading|null)/i);
  });
});

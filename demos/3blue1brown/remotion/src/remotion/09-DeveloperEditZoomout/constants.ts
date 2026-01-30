import { z } from "zod";

// Video specs
export const ZOOM_OUT_FPS = 30;
export const ZOOM_OUT_DURATION_SECONDS = 10;
export const ZOOM_OUT_DURATION_FRAMES =
  ZOOM_OUT_FPS * ZOOM_OUT_DURATION_SECONDS;
export const ZOOM_OUT_WIDTH = 1920;
export const ZOOM_OUT_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Frame 0-90:   Transition — IDE view becomes stylized
// Frame 90-180: Zoom out — code → file → folder → project
// Frame 180-240: Patch accumulation — yellow markers appear
// Frame 240-300: New bug — red pulse + connection line
export const BEATS = {
  TRANSITION_START: 0,
  TRANSITION_END: 90,
  ZOOM_START: 90,
  ZOOM_END: 180,
  PATCHES_START: 180,
  PATCHES_END: 240,
  BUG_START: 240,
  BUG_END: 300,
  NARRATION_START: 250,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1e1e1e",
  BACKGROUND_GRADIENT: "#161622",
  // Code / IDE
  CODE_BG: "#1e1e1e",
  CODE_LINE_NUMBER: "#858585",
  CODE_KEYWORD: "#569cd6",
  CODE_STRING: "#ce9178",
  CODE_FUNCTION: "#dcdcaa",
  CODE_VARIABLE: "#9cdcfe",
  CODE_COMMENT: "#6a9955",
  CODE_PLAIN: "#d4d4d4",
  // File grid
  FILE_DEFAULT: "#2d2d3a",
  FILE_BORDER: "#3e3e4e",
  FILE_ACTIVE: "#264f78",
  FILE_ACTIVE_BORDER: "#569cd6",
  // Patches
  PATCH_YELLOW: "#d9944a",
  PATCH_ORANGE: "#cc6633",
  // TODO markers
  TODO_TEXT: "#6a9955",
  TODO_BG: "rgba(106, 153, 85, 0.15)",
  // Bug
  BUG_RED: "#f44747",
  BUG_GLOW: "rgba(244, 71, 71, 0.6)",
  CONNECTION_LINE: "rgba(244, 71, 71, 0.35)",
  // Labels
  LABEL_WHITE: "rgba(255, 255, 255, 0.9)",
};

// The "world" dimensions for the full codebase view.
// At full zoom we see a small portion; zoomed out we see it all.
export const WORLD = {
  width: 6000,
  height: 3375, // 16:9 ratio
};

// The code editor region (where the developer's edit is) in world-space
export const EDITOR_REGION = {
  x: 2800,
  y: 1500,
  width: 500,
  height: 300,
};

// File grid: deterministic layout of ~180 files in folder-like clusters
export interface FileRect {
  x: number;
  y: number;
  w: number;
  h: number;
  hasPatch: boolean;
  isActive: boolean;
  folder: number;
}

/**
 * Seeded pseudo-random number generator for deterministic layouts.
 */
function seededRandom(seed: number): () => number {
  let s = seed;
  return () => {
    s = (s * 16807 + 0) % 2147483647;
    return (s - 1) / 2147483646;
  };
}

/**
 * Generate the deterministic file grid layout.
 */
export function generateFileGrid(): FileRect[] {
  const rand = seededRandom(42);
  const files: FileRect[] = [];

  // 12 folder clusters spread across the world
  const folders = [
    { cx: 600, cy: 400, count: 18 },
    { cx: 1500, cy: 350, count: 14 },
    { cx: 2600, cy: 300, count: 12 },
    { cx: 3800, cy: 500, count: 16 },
    { cx: 5000, cy: 400, count: 10 },
    { cx: 800, cy: 1200, count: 15 },
    { cx: 1800, cy: 1100, count: 11 },
    { cx: 3050, cy: 1600, count: 20 }, // cluster containing the active file
    { cx: 4200, cy: 1300, count: 13 },
    { cx: 5200, cy: 1100, count: 9 },
    { cx: 1200, cy: 2200, count: 16 },
    { cx: 2400, cy: 2400, count: 12 },
    { cx: 3600, cy: 2300, count: 14 },
    { cx: 4800, cy: 2100, count: 8 },
    { cx: 700, cy: 2900, count: 10 },
    { cx: 2000, cy: 3000, count: 7 },
  ];

  let fileIndex = 0;
  folders.forEach((folder, fi) => {
    for (let i = 0; i < folder.count; i++) {
      const col = i % 6;
      const row = Math.floor(i / 6);
      const w = 60 + rand() * 40;
      const h = 35 + rand() * 20;
      const x = folder.cx + col * (w + 14) - ((Math.min(folder.count, 6) * (w + 14)) / 2);
      const y = folder.cy + row * (h + 10);
      const hasPatch = rand() < 0.3;
      // The file in the "active editor" cluster closest to center is the active one
      const isActive = fi === 7 && i === 0;
      files.push({ x, y, w, h, hasPatch, isActive, folder: fi });
      fileIndex++;
    }
  });

  return files;
}

// Precompute the file grid
export const FILE_GRID = generateFileGrid();

// Active file position (the one the developer just edited)
export const ACTIVE_FILE = FILE_GRID.find((f) => f.isActive)!;

// Bug location — in a distant cluster
export const BUG_FILE = FILE_GRID.find(
  (f) => f.folder === 4 && !f.isActive
)!;

// TODO comment labels with positions near specific clusters
export const TODO_COMMENTS = [
  { text: "// don't touch this", x: 550, y: 1150, folder: 5 },
  { text: "// legacy", x: 1450, y: 300, folder: 1 },
  { text: '// temporary fix (2019)', x: 3750, y: 450, folder: 3 },
  { text: "// TODO: refactor", x: 1150, y: 2150, folder: 10 },
  { text: "// HACK", x: 4750, y: 2050, folder: 13 },
  { text: "// nobody knows why", x: 2350, y: 2350, folder: 11 },
];

// Fake code lines for the initial IDE view
export const CODE_LINES = [
  { type: "comment", text: "// Apply the patch to the pricing module" },
  { type: "keyword", text: "function " },
  { type: "function", text: "applyDiscount" },
  { type: "plain", text: "(price: number, code: string) {" },
  { type: "keyword", text: "  if " },
  { type: "plain", text: "(code === " },
  { type: "string", text: '"LEGACY_FIX"' },
  { type: "plain", text: ") {" },
  { type: "keyword", text: "    return " },
  { type: "variable", text: "price" },
  { type: "plain", text: " * 0.85;  " },
  { type: "comment", text: "// patched" },
  { type: "plain", text: "  }" },
  { type: "keyword", text: "  return " },
  { type: "variable", text: "price" },
  { type: "plain", text: ";" },
  { type: "plain", text: "}" },
];

// Props schema
export const DeveloperEditZoomoutProps = z.object({
  showNarration: z.boolean().default(true),
});

export const defaultDeveloperEditZoomoutProps: z.infer<
  typeof DeveloperEditZoomoutProps
> = {
  showNarration: true,
};

export type DeveloperEditZoomoutPropsType = z.infer<
  typeof DeveloperEditZoomoutProps
>;

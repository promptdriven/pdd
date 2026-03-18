// ─── Colors ─────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.03;

export const AMBER = "#D9944A";
export const BLUE = "#4A90D9";
export const GREEN = "#5AAA6E";

export const TEXT_PRIMARY = "#E2E8F0";
export const TEXT_SECONDARY = "#94A3B8";
export const TABLE_BG = "#1E293B";
export const TABLE_HEADER_BG = "#0F172A";
export const DIVIDER_COLOR = "#334155";

// ─── Dimensions ─────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const GRID_SPACING = 40;
export const FPS = 30;
export const TOTAL_FRAMES = 480;

// Table layout
export const TABLE_X = 650;
export const TABLE_Y = 250;
export const TABLE_WIDTH = 1100;
export const TABLE_ROW_HEIGHT = 80;
export const COL_WIDTHS = [300, 350, 250];
export const TABLE_BORDER_RADIUS = 12;

// ─── Table Data ─────────────────────────────────────────
export const TABLE_ROWS = [
  {
    component: "Prompt",
    encodes: "WHAT (intent)",
    owner: "Developer",
    color: BLUE,
    accentWidth: 3,
    bold: false,
  },
  {
    component: "Grounding",
    encodes: "HOW (style)",
    owner: "Automatic",
    color: GREEN,
    accentWidth: 3,
    bold: false,
  },
  {
    component: "Tests",
    encodes: "CORRECTNESS",
    owner: "Accumulated",
    color: AMBER,
    accentWidth: 4,
    bold: true,
  },
] as const;

// ─── Animation Timing (frames) ─────────────────────────
export const TIMING = {
  // Phase 1: Full mold with flow
  moldFullStart: 0,
  moldFullEnd: 60,
  // Phase 2: Mold slides left, table appears
  moldSlideStart: 60,
  moldSlideEnd: 100,
  // Phase 3: Table header
  tableHeaderStart: 120,
  tableHeaderEnd: 180,
  // Phase 4-6: Row appearances
  row1Start: 180,
  row2Start: 220,
  row3Start: 260,
  // Phase 7: Conflict line
  conflictStart: 310,
  conflictEnd: 370,
  // Phase 8: Code output
  codeStart: 370,
  codeGlowEnd: 420,
  // Phase 9: Code fades
  codeDimStart: 420,
  codeDimEnd: 450,
  // Phase 10: Final caption
  captionStart: 450,
} as const;

// ─── Code Snippet ───────────────────────────────────────
export const CODE_SNIPPET = `function createWidget(config) {
  const widget = new Widget(config);
  widget.validate();
  return widget.render();
}`;

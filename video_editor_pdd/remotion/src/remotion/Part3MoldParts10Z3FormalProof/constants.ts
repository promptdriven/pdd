// ── Colors ──────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const PANEL_BG = "#0F172A";
export const PANEL_BORDER = "#334155";
export const TEXT_PRIMARY = "#CDD6F4";
export const TEXT_EMPHASIS = "#E2E8F0";
export const PURPLE_ACCENT = "#A78BFA";
export const PURPLE_DEEP = "#7C3AED";
export const MOLD_BLUE = "#4A90D9";
export const MOLD_WALL_COLOR = "#334155";
export const MOLD_CAVITY_COLOR = "#1E293B";

// ── Dimensions ─────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

export const PANEL_X = 1000;
export const PANEL_Y = 200;
export const PANEL_WIDTH = 840;
export const PANEL_HEIGHT = 580;
export const PANEL_RADIUS = 12;
export const PANEL_PADDING = 32;

export const BADGE_SIZE = 48;
export const BADGE_RADIUS = 8;
export const BADGE_GAP = 24;

// ── Animation Timing (frames) ──────────────────────────────
export const FPS = 30;
export const TOTAL_FRAMES = 780;

export const PANEL_SLIDE_IN_START = 0;
export const PANEL_SLIDE_IN_END = 30;

export const TEXT_TYPE_START = 30;
export const TEXT_TYPE_END = 90;

export const EMPHASIS_START = 90;
export const EMPHASIS_END = 110;

export const ITALIC_START = 150;
export const ITALIC_END = 170;

export const BADGES_START = 210;
export const BADGES_END = 230;

export const CONNECTORS_START = 270;
export const CONNECTORS_END = 300;

export const WALL_TRANSITION_START = 270;
export const WALL_TRANSITION_END = 360;

export const HOLD_START = 360;
export const HOLD_END = 720;

export const PANEL_SLIDE_OUT_START = 720;
export const PANEL_SLIDE_OUT_END = 750;

export const MOLD_RESTORE_START = 720;
export const MOLD_RESTORE_END = 780;

// ── Text Content ───────────────────────────────────────────
export const MAIN_TEXT_WORDS = [
  "PDD", "also", "uses", "Z3", "—", "the", "same", "class", "of",
  "SMT", "solver", "used", "in", "chip", "verification", "—", "to",
  "formally", "prove", "properties", "hold", "for", "every", "possible", "input.",
];

export const HIGHLIGHT_RANGES: Array<{
  startIndex: number;
  endIndex: number;
  label: string;
}> = [
  { startIndex: 3, endIndex: 3, label: "Z3" },
  { startIndex: 9, endIndex: 10, label: "SMT solver" },
  { startIndex: 17, endIndex: 18, label: "formally prove" },
];

export const EMPHASIS_TEXT = "Same math as billion-dollar tapeouts.";
export const ITALIC_TEXT = "Not sampling. Mathematical proof.";

// ── Mold Wall Geometry ─────────────────────────────────────
export interface WallSegment {
  x1: number;
  y1: number;
  x2: number;
  y2: number;
}

export const MOLD_WALLS: WallSegment[] = [
  { x1: 200, y1: 300, x2: 200, y2: 700 },  // wall 0 - left outer
  { x1: 350, y1: 350, x2: 350, y2: 650 },  // wall 1 - proven
  { x1: 500, y1: 300, x2: 500, y2: 700 },  // wall 2 - center
  { x1: 650, y1: 350, x2: 650, y2: 650 },  // wall 3 - proven
  { x1: 800, y1: 300, x2: 800, y2: 700 },  // wall 4 - right outer
];

export const PROVEN_WALL_INDICES = [1, 3];

export const CONNECTOR_ORIGIN_X = PANEL_X;
export const CONNECTOR_ORIGIN_Y = 500;

// ── Canvas ──
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BG_COLOR = "#0A0F1A";

// ── Grid geometry ──
export const GRID_SIZE = 600;
export const CELL_SIZE = 300;
export const GRID_CENTER_X = 960;
export const GRID_CENTER_Y = 480;
export const GRID_LEFT = GRID_CENTER_X - GRID_SIZE / 2;   // 660
export const GRID_TOP = GRID_CENTER_Y - GRID_SIZE / 2;    // 180
export const GRID_RIGHT = GRID_LEFT + GRID_SIZE;           // 1260
export const GRID_BOTTOM = GRID_TOP + GRID_SIZE;           // 780

// ── Grid appearance ──
export const DIVIDER_COLOR = "#334155";
export const DIVIDER_WIDTH = 2;

// ── Quadrant colors ──
export const GREEN_QUADRANT = "#5AAA6E";
export const GREEN_FILL_OPACITY = 0.15;
export const GREEN_GLOW_OPACITY = 0.3;

export const RED_QUADRANT = "#EF4444";
export const RED_FILL_OPACITY = 0.15;
export const RED_GLOW_OPACITY = 0.3;

export const NEUTRAL_FILL = "#64748B";
export const NEUTRAL_FILL_OPACITY = 0.06;

// ── Typography colors ──
export const AXIS_LABEL_COLOR = "#94A3B8";
export const INSIGHT_TEXT_COLOR = "#E2E8F0";

// ── Typography sizes ──
export const AXIS_LABEL_SIZE = 16;
export const QUADRANT_LABEL_SIZE = 20;
export const INSIGHT_TEXT_SIZE = 16;

// ── Axis labels ──
export const X_LABELS = ["Greenfield", "Brownfield"] as const;
export const Y_LABELS = ["In-Distribution", "Out-of-Distribution"] as const;

// ── Quadrant data ──
export const GREEN_LABEL = "GitHub study: +55%";
export const RED_LABEL = "METR study: \u221219%";

// ── Insight text ──
export const INSIGHT_TEXT =
  "Every study is correct. They just measured different quadrants.";
export const INSIGHT_Y = 830;

// ── Animation timing (frames) ──
export const TOTAL_FRAMES = 630;

// Phase 1: Grid draws + axis labels
export const GRID_DRAW_START = 0;
export const GRID_DRAW_END = 45;

// Phase 2: Green quadrant illuminates + label types in
export const GREEN_START = 45;
export const GREEN_END = 90;

// Phase 3: Hold on green
// (90–150, no new animations)

// Phase 4: Red quadrant illuminates + label types in
export const RED_START = 150;
export const RED_END = 210;

// Phase 5: Both glowing hold (210–390)

// Phase 6: Insight label fades in
export const INSIGHT_START = 390;
export const INSIGHT_END = 420; // 30 frames fade

// Phase 7: Hold to end (450–630)

// ── Easing durations ──
export const DRAW_DURATION = 30;
export const FILL_DURATION = 30;
export const LABEL_CHARS_PER_FRAME = 0.5; // 2 frames per character
export const INSIGHT_FADE_DURATION = 30;

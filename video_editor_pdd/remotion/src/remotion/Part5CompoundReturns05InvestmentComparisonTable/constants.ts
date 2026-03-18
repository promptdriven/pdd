// Colors
export const BG_COLOR = "#0F172A";
export const TABLE_BG = "#0F172A";
export const HEADER_BG = "#1E293B";
export const BORDER_COLOR = "#334155";
export const ALT_ROW_BG = "#111827";

export const TEXT_COLOR = "#E2E8F0";
export const LABEL_COLOR = "#94A3B8";
export const PATCHING_COLOR = "#D9944A";
export const PDD_COLOR = "#4A90D9";

// Dimensions
export const TABLE_WIDTH = 900;
export const COL_WIDTH = 300;
export const HEADER_HEIGHT = 50;
export const ROW_HEIGHT = 70;
export const TABLE_BORDER_RADIUS = 8;
export const CELL_PADDING = 24;

// Table position (centered)
export const TABLE_X = (1920 - TABLE_WIDTH) / 2;
export const TABLE_Y = 260;

// Summary
export const SUMMARY_Y = 700;
export const PILL_PADDING = 16;
export const PILL_RADIUS = 10;

// Animation timing (frames)
export const TOTAL_FRAMES = 420;

// Phase 1: Table container fade-in
export const TABLE_FADE_START = 0;
export const TABLE_FADE_DURATION = 20;

// Phase 2: Row 1
export const ROW1_START = 30;
export const ROW_SLIDE_DURATION = 20;
export const CELL_STAGGER = 10;
export const GLOW_DURATION = 15;

// Phase 3: Row 2
export const ROW2_START = 90;

// Phase 4: Row 3
export const ROW3_START = 150;

// Phase 5: PDD pulse
export const PULSE_START = 210;
export const PULSE_DURATION = 30;

// Phase 6: Summary
export const SUMMARY_START = 270;
export const SUMMARY_SLIDE_DURATION = 25;

// Row data
export const TABLE_ROWS = [
  {
    investment: "Fix a bug",
    icon: "bug",
    patching: "One place, once",
    pdd: "Impossible forever",
    pddGlow: 0.04,
    pddOpacity: 0.8,
    alternate: false,
  },
  {
    investment: "Improve code",
    icon: "code",
    patching: "One version",
    pdd: "All future versions",
    pddGlow: 0.06,
    pddOpacity: 0.9,
    alternate: true,
  },
  {
    investment: "Document intent",
    icon: "doc",
    patching: "One snapshot",
    pdd: "Living specification",
    pddGlow: 0.08,
    pddOpacity: 1.0,
    alternate: false,
  },
] as const;

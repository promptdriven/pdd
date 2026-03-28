// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const DURATION_IN_FRAMES = 150;
export const FPS = 30;

// Background
export const BG_COLOR = "#0A0F1A";

// Module grid
export const GRID_COLS = 12;
export const GRID_ROWS = 6;
export const GRID_CELL_SIZE = 28;
export const GRID_GAP = 6;
export const GRID_BASE_OPACITY = 0.08;
export const GRID_CELL_COLOR = "#1E293B";
export const GRID_GREEN_COLOR = "#5AAA6E";

// Green-glowing module indices (arbitrary subset for visual anchor)
export const GRID_GREEN_INDICES = [
  14, 17, 22, 25, 33, 38, 41, 45, 50, 55, 58, 62, 67,
];

// Text stack
export const TEXT_CONTAINER_WIDTH = 600;
export const TEXT_FONT_SIZE = 40;
export const LINE_SPACING = 70;
export const TEXT_COLOR_PRIMARY = "#E2E8F0";
export const TEXT_COLOR_ACCENT = "#5AAA6E";

// Horizontal rules
export const RULE_COLOR_SLATE = "#334155";
export const RULE_COLOR_GREEN = "#5AAA6E";
export const RULE_OPACITY_SLATE = 0.4;
export const RULE_OPACITY_GREEN = 0.5;
export const RULE_THICKNESS = 1.5;
export const RULE_WIDTH_SHORT = 250;
export const RULE_WIDTH_LONG = 350;
export const RULE_OFFSET_TOP = 10;

// Animation timing (frames)
export const LINE1_START = 30;
export const LINE2_START = 55;
export const LINE3_START = 80;
export const TEXT_SLIDE_DISTANCE = 15;
export const TEXT_ANIM_DURATION = 20;
export const RULE_DRAW_DELAY = 20; // delay after text starts
export const RULE_DRAW_DURATION = 15;
export const PULSE_START = 110;
export const PULSE_DURATION = 30;

// Statements data
export const STATEMENTS = [
  { text: "No big bang.", color: TEXT_COLOR_PRIMARY, weight: 700 as const },
  { text: "No rewrite.", color: TEXT_COLOR_PRIMARY, weight: 700 as const },
  {
    text: "Just gradual migration.",
    color: TEXT_COLOR_ACCENT,
    weight: 600 as const,
  },
] as const;

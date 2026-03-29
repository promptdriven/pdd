// ─── Colors ───────────────────────────────────────────────────────
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.05;

export const BUG_RED = '#EF4444';
export const WALL_BLUE = '#4A90D9';
export const WALL_EXISTING_COLOR = '#4A90D9';
export const LIQUID_FROM = '#38BDF8';
export const LIQUID_TO = '#0D9488';

export const TERMINAL_BG = '#1E1E2E';
export const TERMINAL_BORDER = '#334155';
export const TERMINAL_TEXT = '#A6E3A1';
export const TERMINAL_PROMPT = '#94A3B8';
export const WALL_LABEL_TEXT = '#CDD6F4';

export const MOLD_OUTER_COLOR = '#334155';
export const MOLD_CAVITY_COLOR = '#0D1117';
export const NOZZLE_COLOR = '#64748B';

// ─── Dimensions ───────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const GRID_SPACING = 60;

// ─── Mold cross-section layout ───────────────────────────────────
export const MOLD_X = 300;
export const MOLD_Y = 180;
export const MOLD_WIDTH = 1000;
export const MOLD_HEIGHT = 600;
export const MOLD_WALL_THICKNESS = 40;

// Cavity interior (inside the mold walls)
export const CAVITY_X = MOLD_X + MOLD_WALL_THICKNESS;
export const CAVITY_Y = MOLD_Y + MOLD_WALL_THICKNESS;
export const CAVITY_WIDTH = MOLD_WIDTH - 2 * MOLD_WALL_THICKNESS;
export const CAVITY_HEIGHT = MOLD_HEIGHT - 2 * MOLD_WALL_THICKNESS;

// Internal walls inside the cavity
export const EXISTING_WALLS = [
  { x: CAVITY_X + 180, y: CAVITY_Y, width: 16, height: 200, label: 'validates schema' },
  { x: CAVITY_X + 380, y: CAVITY_Y + CAVITY_HEIGHT - 240, width: 16, height: 240, label: 'sanitizes input' },
  { x: CAVITY_X + 560, y: CAVITY_Y, width: 16, height: 320, label: 'checks auth' },
];

// New wall that slides in when the bug is found
export const NEW_WALL = {
  x: CAVITY_X + 460,
  y: CAVITY_Y + 160,
  width: 16,
  height: 200,
  label: 'rejects negative IDs',
};

// Bug location — gap between existing walls
export const BUG_X = CAVITY_X + 460;
export const BUG_Y = CAVITY_Y + 260;

// Nozzle (injection point at the top)
export const NOZZLE_X = MOLD_X + MOLD_WIDTH / 2 - 30;
export const NOZZLE_Y = MOLD_Y - 60;
export const NOZZLE_WIDTH = 60;
export const NOZZLE_HEIGHT = 70;

// ─── Terminal ─────────────────────────────────────────────────────
export const TERMINAL_X = 1450;
export const TERMINAL_Y = 850;
export const TERMINAL_WIDTH = 400;
export const TERMINAL_HEIGHT = 160;

// ─── Animation frames ────────────────────────────────────────────
export const FPS = 30;
export const TOTAL_FRAMES = 480;

// Phase boundaries
export const BUG_DISCOVER_START = 0;
export const BUG_DISCOVER_END = 30;
export const BUG_HOLD_END = 60;
export const WALL_SLIDE_START = 60;
export const WALL_SLIDE_END = 100;
export const WALL_ARRIVE_END = 120;
export const WALL_LABEL_END = 150;
export const WALL_HOLD_END = 180;
export const LIQUID_DRAIN_START = 180;
export const LIQUID_DRAIN_END = 200;
export const LIQUID_FILL_START = 210;
export const LIQUID_FILL_END = 250;
export const TERMINAL_FIX_START = 210;
export const TESTS_PASS_FRAME = 300;
export const HOLD_START = 360;
export const TERMINAL_FADE_START = 420;

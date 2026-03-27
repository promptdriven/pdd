// ── Canvas ──────────────────────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 480;

// ── Colors ─────────────────────────────────────────────────────────
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.05;

export const BUG_RED = '#EF4444';
export const WALL_BLUE = '#4A90D9';
export const LIQUID_CYAN = '#38BDF8';
export const LIQUID_TEAL = '#0D9488';

export const TEXT_PRIMARY = '#CDD6F4';
export const TERMINAL_BG = '#1E1E2E';
export const TERMINAL_BORDER = '#334155';
export const TERMINAL_GREEN = '#A6E3A1';
export const TERMINAL_GRAY = '#94A3B8';

export const WALL_EXISTING_COLOR = '#4A90D9';
export const WALL_LABEL_BG_OPACITY = 0.15;

// ── Grid ───────────────────────────────────────────────────────────
export const GRID_SPACING = 60;

// ── Mold layout (cross-section) ────────────────────────────────────
export const MOLD_X = 200;
export const MOLD_Y = 180;
export const MOLD_WIDTH = 1100;
export const MOLD_HEIGHT = 600;
export const MOLD_WALL_THICKNESS = 12;
export const NOZZLE_X = MOLD_X + MOLD_WIDTH / 2;
export const NOZZLE_Y = MOLD_Y - 40;

// Existing internal walls (vertical dividers inside the mold)
export const EXISTING_WALLS = [
  { x: MOLD_X + 280, y: MOLD_Y + 80, width: MOLD_WALL_THICKNESS, height: 300, label: 'validates email' },
  { x: MOLD_X + 560, y: MOLD_Y + 120, width: MOLD_WALL_THICKNESS, height: 340, label: 'sanitizes input' },
  { x: MOLD_X + 800, y: MOLD_Y + 60, width: MOLD_WALL_THICKNESS, height: 380, label: 'checks auth' },
];

// Where the bug appears — gap between walls
export const BUG_LOCATION_X = MOLD_X + 680;
export const BUG_LOCATION_Y = MOLD_Y + 300;

// New wall that slides in
export const NEW_WALL = {
  x: MOLD_X + 680,
  y: MOLD_Y + 100,
  width: MOLD_WALL_THICKNESS,
  height: 340,
  label: 'rejects negative IDs',
};

// ── Terminal ───────────────────────────────────────────────────────
export const TERMINAL_X = 1450;
export const TERMINAL_Y = 850;
export const TERMINAL_WIDTH = 400;
export const TERMINAL_HEIGHT = 160;

// ── Animation timing (frames) ──────────────────────────────────────
export const BUG_PULSE_START = 0;
export const BUG_PULSE_END = 60;
export const BUG_TEXT_FADE_IN_START = 10;
export const BUG_TEXT_FADE_IN_DURATION = 15;

export const TERMINAL_FADE_IN_START = 30;
export const TERMINAL_FADE_IN_DURATION = 15;

export const BUG_TEXT_FADE_OUT_START = 60;
export const BUG_TEXT_FADE_OUT_DURATION = 15;

export const WALL_SLIDE_START = 60;
export const WALL_SLIDE_DURATION = 40;
export const WALL_GLOW_START = 100;
export const WALL_LABEL_FADE_START = 120;
export const WALL_LABEL_FADE_DURATION = 20;

export const LIQUID_DRAIN_START = 180;
export const LIQUID_DRAIN_DURATION = 20;
export const LIQUID_REFILL_START = 210;
export const LIQUID_REFILL_DURATION = 40;

export const TERMINAL_CMD2_FRAME = 60; // "Creating failing test..."
export const TERMINAL_CMD3_FRAME = 210; // "$ pdd fix user_parser"
export const TERMINAL_CMD4_FRAME = 300; // "All tests passing ✓"

export const TERMINAL_FADE_OUT_START = 400;
export const TERMINAL_FADE_OUT_DURATION = 60;

// ── Pulse ring config ──────────────────────────────────────────────
export const PULSE_RING_COUNT = 3;
export const PULSE_RING_DELAY = 8; // frames between each ring
export const PULSE_RING_EXPAND_DURATION = 15;
export const PULSE_RING_MAX_RADIUS = 60;

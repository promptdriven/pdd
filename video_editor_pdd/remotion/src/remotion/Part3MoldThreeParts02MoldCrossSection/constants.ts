// ── Colors ──────────────────────────────────────────
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.04;
export const GRID_SPACING = 40;

export const SHELL_COLOR = '#334155';
export const SHELL_OPACITY = 0.6;
export const SHELL_STROKE = 3;

export const CAVITY_BG_COLOR = '#1E293B';
export const CAVITY_BG_OPACITY = 0.2;

// Region colors
export const AMBER = '#D9944A';
export const BLUE = '#4A90D9';
export const GREEN = '#5AAA6E';

export const LABEL_SLATE = '#94A3B8';

// ── Layout (center at 960, 500) ─────────────────────
export const CENTER_X = 960;
export const CENTER_Y = 500;
export const MOLD_WIDTH = 600;
export const MOLD_HEIGHT = 700;
export const CAVITY_WIDTH = 450;
export const CAVITY_HEIGHT = 550;

// Nozzle dimensions
export const NOZZLE_TOP_WIDTH = 80;
export const NOZZLE_BOTTOM_WIDTH = 30;
export const NOZZLE_HEIGHT = 120;

// ── Animation frames ────────────────────────────────
export const DRAW_START = 0;
export const DRAW_END = 40;
export const TITLE_START = 40;
export const TITLE_END = 60;
export const WALLS_START = 60;
export const WALLS_END = 120;
export const NOZZLE_START = 120;
export const NOZZLE_END = 180;
export const CAVITY_START = 180;
export const CAVITY_END = 240;
export const FINALE_START = 240;
export const FINALE_END = 300;
export const TOTAL_FRAMES = 300;

// ── Region label data ───────────────────────────────
export const WALL_LABELS = [
  { text: 'null → None', side: 'left' as const, yOffset: -100 },
  { text: "empty string → ''", side: 'left' as const, yOffset: 0 },
  { text: 'handles unicode', side: 'bottom' as const, yOffset: 0 },
  { text: 'latency < 100ms', side: 'right' as const, yOffset: -50 },
];

export const NOZZLE_LABELS = ['intent', 'requirements', 'constraints'];

export const CAVITY_LABELS = [
  { text: 'style', position: 'upper-left' as const },
  { text: 'patterns', position: 'center' as const },
  { text: 'conventions', position: 'lower-right' as const },
];

// ── Colors ──────────────────────────────────────────────────
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.04;
export const GRID_SPACING = 40;

export const SHELL_COLOR = '#334155';
export const SHELL_OPACITY = 0.6;
export const SHELL_STROKE = 3;

export const CAVITY_BG = '#1E293B';
export const CAVITY_BG_OPACITY = 0.2;

// Region colors
export const AMBER = '#D9944A';
export const BLUE = '#4A90D9';
export const GREEN = '#5AAA6E';

export const LABEL_SLATE = '#94A3B8';

// ── Dimensions ─────────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;

// Mold centred at (960, 500)
export const MOLD_CX = 960;
export const MOLD_CY = 500;
export const MOLD_W = 600;
export const MOLD_H = 700;

export const CAVITY_W = 450;
export const CAVITY_H = 550;

// Nozzle
export const NOZZLE_TOP_W = 80;
export const NOZZLE_BOT_W = 30;
export const NOZZLE_H = 120;

// ── Animation frames ───────────────────────────────────────
export const TOTAL_FRAMES = 300;

// Phase boundaries
export const DRAW_END = 40;
export const TITLE_START = 40;
export const TITLE_DUR = 20;

export const WALLS_START = 60;
export const WALLS_ILLUM_DUR = 20;
export const WALL_LABEL_STAGGER = 15;

export const NOZZLE_START = 120;
export const NOZZLE_ILLUM_DUR = 20;
export const NOZZLE_LABEL_STAGGER = 12;

export const CAVITY_START = 180;
export const CAVITY_FILL_DUR = 40;
export const CAVITY_LABEL_STAGGER = 12;

export const ALL_BRIGHT_START = 240;
export const ALL_BRIGHT_DUR = 20;

// ── Region label data ──────────────────────────────────────
export interface WallLabel {
  text: string;
  side: 'left' | 'right' | 'bottom';
  yOffset: number; // relative to mold top
}

export const WALL_LABELS: WallLabel[] = [
  { text: 'null → None', side: 'left', yOffset: -150 },
  { text: "empty string → ''", side: 'left', yOffset: -50 },
  { text: 'handles unicode', side: 'bottom', yOffset: 250 },
  { text: 'latency < 100ms', side: 'right', yOffset: -100 },
];

export const NOZZLE_LABELS = ['intent', 'requirements', 'constraints'];

export interface CavityLabel {
  text: string;
  position: 'upper-left' | 'center' | 'lower-right';
}

export const CAVITY_LABELS: CavityLabel[] = [
  { text: 'style', position: 'upper-left' },
  { text: 'patterns', position: 'center' },
  { text: 'conventions', position: 'lower-right' },
];

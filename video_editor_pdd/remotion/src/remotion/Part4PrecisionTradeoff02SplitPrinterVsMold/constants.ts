// === Layout ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const DIVIDER_WIDTH_PX = 40;
export const PANEL_WIDTH = 940;
export const TOTAL_FRAMES = 480;
export const FPS = 30;

// === Divider ===
export const DIVIDER_COLOR = '#FFFFFF';
export const DIVIDER_LINE_WIDTH = 2;
export const DIVIDER_OPACITY = 0.7;
export const DIVIDER_BG = '#0A0F1A';

// === Backgrounds ===
export const BG_OUTER = '#0A1628';
export const BG_PANEL = '#0D1117';
export const BG_CAVITY = '#0F172A';

// === Left Panel (3D Printer) ===
export const GRID_SPACING = 40;
export const GRID_LINE_COLOR = '#1E293B';
export const GRID_LINE_OPACITY = 0.12;
export const NOZZLE_COLOR = '#E2E8F0';
export const NOZZLE_WIDTH = 20;
export const NOZZLE_HEIGHT = 12;
export const DOT_COLOR = '#4A90D9';
export const DOT_OPACITY = 0.6;
export const DOT_SIZE = 6;
export const TRAIL_COLOR = '#4A90D9';
export const TRAIL_OPACITY = 0.15;
export const GRID_LABEL_COLOR = '#64748B';
export const GRID_LABEL_OPACITY = 0.2;
export const GRID_LABEL_SIZE = 10;
export const PRINTER_HEADER_COLOR = '#94A3B8';

// === Right Panel (Injection Mold) ===
export const MOLD_WALL_COLOR = '#D9944A';
export const MOLD_WALL_OPACITY = 0.7;
export const MOLD_WALL_STROKE = 4;
export const LIQUID_COLOR = '#4A90D9';
export const LIQUID_OPACITY = 0.4;
export const WALL_GLOW_COLOR = '#D9944A';
export const WALL_GLOW_RADIUS = 8;
export const MOLD_HEADER_COLOR = '#D9944A';

// === Typography ===
export const HEADER_FONT_SIZE = 18;
export const HEADER_FONT_WEIGHT = 600;
export const HEADER_FONT_FAMILY = 'Inter, sans-serif';

// === Animation Phases ===
export const PHASE_ESTABLISH_START = 0;
export const PHASE_ESTABLISH_END = 30;
export const PHASE_ANIMATE_START = 30;
export const PHASE_ANIMATE_MID = 150;
export const PHASE_FILL_END = 300;
export const PHASE_COMPLETE = 420;
export const PHASE_FADEOUT_START = 420;
export const PHASE_FADEOUT_END = 480;

// === Nozzle path: grid points the nozzle visits (in panel-local coords) ===
// The nozzle traverses a serpentine path across the grid, filling a rectangular region.
// Panel usable area: ~60px from left, ~60px from top (below header), leaving ~820x900 area.
// We'll fill a 15-column x 16-row grid (each cell 40px) starting from (80, 100).
export const GRID_ORIGIN_X = 80;
export const GRID_ORIGIN_Y = 100;
export const GRID_COLS = 15;
export const GRID_ROWS = 16;

/** Generate serpentine nozzle path through the grid */
export function generateNozzlePath(): Array<{ x: number; y: number }> {
  const points: Array<{ x: number; y: number }> = [];
  for (let row = 0; row < GRID_ROWS; row++) {
    if (row % 2 === 0) {
      for (let col = 0; col < GRID_COLS; col++) {
        points.push({
          x: GRID_ORIGIN_X + col * GRID_SPACING,
          y: GRID_ORIGIN_Y + row * GRID_SPACING,
        });
      }
    } else {
      for (let col = GRID_COLS - 1; col >= 0; col--) {
        points.push({
          x: GRID_ORIGIN_X + col * GRID_SPACING,
          y: GRID_ORIGIN_Y + row * GRID_SPACING,
        });
      }
    }
  }
  return points;
}

// === Mold cavity shape (in panel-local coords) ===
// A rounded rectangle with internal channels, centered in the right panel
export const MOLD_OUTER_X = 120;
export const MOLD_OUTER_Y = 140;
export const MOLD_OUTER_W = 700;
export const MOLD_OUTER_H = 800;
export const MOLD_CORNER_RADIUS = 40;
export const MOLD_INJECTION_X = 470;
export const MOLD_INJECTION_Y = 100;

// Internal channel waypoints (relative to panel)
export const MOLD_CHANNELS: Array<{ x1: number; y1: number; x2: number; y2: number }> = [
  // Vertical entry channel from injection point
  { x1: 470, y1: 140, x2: 470, y2: 300 },
  // Horizontal distribution
  { x1: 250, y1: 300, x2: 690, y2: 300 },
  // Left vertical fill
  { x1: 250, y1: 300, x2: 250, y2: 750 },
  // Right vertical fill
  { x1: 690, y1: 300, x2: 690, y2: 750 },
  // Bottom horizontal
  { x1: 250, y1: 750, x2: 690, y2: 750 },
  // Center cross-fill
  { x1: 470, y1: 300, x2: 470, y2: 750 },
];

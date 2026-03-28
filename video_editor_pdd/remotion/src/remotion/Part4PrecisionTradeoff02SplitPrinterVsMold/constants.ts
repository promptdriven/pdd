// Layout
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const PANEL_WIDTH = 940;
export const DIVIDER_GAP = 40;
export const DIVIDER_WIDTH = 2;
export const DIVIDER_COLOR = '#FFFFFF';
export const DIVIDER_OPACITY = 0.4;

// Backgrounds
export const SCENE_BG = '#0A0F1A';
export const PANEL_BG = '#0D1117';
export const CAVITY_BG = '#0F172A';

// Left panel — 3D Printer
export const PRINTER_ACCENT = '#4A90D9';
export const NOZZLE_COLOR = '#E2E8F0';
export const GRID_LINE_COLOR = '#1E293B';
export const GRID_LINE_OPACITY = 0.12;
export const GRID_SPACING = 40;
export const DOT_SIZE = 6;
export const TRAIL_OPACITY = 0.15;
export const GRID_LABEL_COLOR = '#64748B';
export const GRID_LABEL_OPACITY = 0.2;
export const PRINTER_HEADER_COLOR = '#94A3B8';

// Right panel — Injection Mold
export const MOLD_ACCENT = '#D9944A';
export const MOLD_WALL_OPACITY = 0.7;
export const MOLD_WALL_STROKE = 4;
export const LIQUID_COLOR = '#4A90D9';
export const LIQUID_OPACITY = 0.4;
export const GLOW_RADIUS = 8;

// Typography
export const HEADER_FONT_SIZE = 16;
export const HEADER_FONT_WEIGHT = 600;
export const LABEL_FONT_SIZE = 10;

// Animation timing (frames @ 30fps)
export const TOTAL_FRAMES = 480;
export const PHASE_ESTABLISH_END = 30;
export const PHASE_ANIMATE_START = 30;
export const PHASE_FLOW_START = 150;
export const PHASE_COMPLETE_START = 300;
export const PHASE_HOLD_START = 420;
export const FADE_OUT_START = 420;
export const FADE_OUT_DURATION = 60;

// Nozzle path — grid points the nozzle visits (in panel-local coords)
// Panel area for grid: roughly x 60..880, y 80..520 (leaving margins)
const GRID_ORIGIN_X = 80;
const GRID_ORIGIN_Y = 80;
const GRID_COLS = 20;
const GRID_ROWS = 10;

export interface GridPoint {
  x: number;
  y: number;
  col: number;
  row: number;
}

// Generate a serpentine (boustrophedon) path across the grid
export const NOZZLE_PATH: GridPoint[] = (() => {
  const points: GridPoint[] = [];
  for (let row = 0; row < GRID_ROWS; row++) {
    if (row % 2 === 0) {
      for (let col = 0; col < GRID_COLS; col++) {
        points.push({
          x: GRID_ORIGIN_X + col * GRID_SPACING,
          y: GRID_ORIGIN_Y + row * GRID_SPACING,
          col,
          row,
        });
      }
    } else {
      for (let col = GRID_COLS - 1; col >= 0; col--) {
        points.push({
          x: GRID_ORIGIN_X + col * GRID_SPACING,
          y: GRID_ORIGIN_Y + row * GRID_SPACING,
          col,
          row,
        });
      }
    }
  }
  return points;
})();

// Mold cavity shape — defined as wall segments
export interface WallSegment {
  x1: number;
  y1: number;
  x2: number;
  y2: number;
}

// Mold cavity: a rounded-ish shape with internal channels
const CX = 470; // center of right panel
const CY = 310;
const W = 340;
const H = 260;

export const MOLD_WALLS: WallSegment[] = [
  // Outer rectangle
  { x1: CX - W / 2, y1: CY - H / 2, x2: CX + W / 2, y2: CY - H / 2 }, // top
  { x1: CX + W / 2, y1: CY - H / 2, x2: CX + W / 2, y2: CY + H / 2 }, // right
  { x1: CX + W / 2, y1: CY + H / 2, x2: CX - W / 2, y2: CY + H / 2 }, // bottom
  { x1: CX - W / 2, y1: CY + H / 2, x2: CX - W / 2, y2: CY - H / 2 }, // left
  // Internal channel walls
  { x1: CX - W / 4, y1: CY - H / 2, x2: CX - W / 4, y2: CY + H / 4 }, // left divider
  { x1: CX + W / 4, y1: CY - H / 4, x2: CX + W / 4, y2: CY + H / 2 }, // right divider
  // Horizontal internal
  { x1: CX - W / 4, y1: CY, x2: CX + W / 4, y2: CY }, // middle horizontal
];

// Injection point (top center of mold)
export const INJECTION_POINT = { x: CX, y: CY - H / 2 - 30 };

// Mold cavity center and bounds for particle containment
export const MOLD_BOUNDS = {
  left: CX - W / 2 + MOLD_WALL_STROKE,
  right: CX + W / 2 - MOLD_WALL_STROKE,
  top: CY - H / 2 + MOLD_WALL_STROKE,
  bottom: CY + H / 2 - MOLD_WALL_STROKE,
  centerX: CX,
  centerY: CY,
  width: W,
  height: H,
};

// === Canvas ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = '#0A0F1A';
export const TOTAL_FRAMES = 300;
export const FPS = 30;

// === Blueprint Grid ===
export const GRID_SPACING = 60;
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.05;

// === Mold Structure ===
export const MOLD_OUTER_STROKE = '#334155';
export const MOLD_OUTER_STROKE_WIDTH = 3;
export const WALL_COLOR = '#4A90D9';
export const DIMMED_OPACITY = 0.05;

// === Mold Geometry (centered on canvas) ===
export const MOLD_X = 660;
export const MOLD_Y = 190;
export const MOLD_WIDTH = 600;
export const MOLD_HEIGHT = 700;
export const MOLD_WALL_THICKNESS = 40;
export const NOZZLE_WIDTH = 80;
export const NOZZLE_HEIGHT = 100;

// === Wall Segments ===
export const WALL_SEGMENT_THICKNESS = 3;
export const WALL_GLOW_MIN = 0.2;
export const WALL_GLOW_MAX = 0.5;
export const WALL_GLOW_DURATION = 15;

// === Labels ===
export const LABEL_FONT_FAMILY = "'JetBrains Mono', 'Fira Code', 'Courier New', monospace";
export const LABEL_FONT_SIZE = 18;
export const LABEL_FONT_WEIGHT = 400;
export const LABEL_TEXT_COLOR = '#CDD6F4';
export const LABEL_PILL_COLOR = '#4A90D9';
export const LABEL_PILL_OPACITY = 0.15;
export const LABEL_PILL_RADIUS = 4;
export const LABEL_PILL_PADDING_H = 8;
export const LABEL_CONNECTOR_COLOR = '#4A90D9';
export const LABEL_CONNECTOR_OPACITY = 0.3;
export const LABEL_FADE_DURATION = 20;
export const CONNECTOR_DRAW_DURATION = 15;

// === Animation Timing ===
export const ZOOM_START = 0;
export const ZOOM_END = 30;
export const ZOOM_FROM = 1.0;
export const ZOOM_TO = 1.15;

// === Wall Data ===
export interface WallEntry {
  label: string;
  side: 'left' | 'right';
  frameIn: number;
}

export const WALL_DATA: WallEntry[] = [
  { label: 'null → None', side: 'left', frameIn: 30 },
  { label: "empty string → ''", side: 'right', frameIn: 75 },
  { label: 'handles unicode', side: 'left', frameIn: 120 },
  { label: 'latency < 100ms', side: 'right', frameIn: 165 },
];

// === Wall Segment Positions (relative to mold) ===
// Segments are distributed along the left and right interior walls
export interface WallSegmentPosition {
  x: number;
  y: number;
  width: number;
  height: number;
  labelAnchorX: number;
  labelAnchorY: number;
}

const segmentHeight = 100;
const wallLeftX = MOLD_X + MOLD_WALL_THICKNESS;
const wallRightX = MOLD_X + MOLD_WIDTH - MOLD_WALL_THICKNESS;

export const WALL_SEGMENT_POSITIONS: WallSegmentPosition[] = [
  // Segment 0 — left wall, upper
  {
    x: MOLD_X,
    y: MOLD_Y + 140,
    width: MOLD_WALL_THICKNESS,
    height: segmentHeight,
    labelAnchorX: wallLeftX - 20,
    labelAnchorY: MOLD_Y + 140 + segmentHeight / 2,
  },
  // Segment 1 — right wall, upper
  {
    x: wallRightX,
    y: MOLD_Y + 260,
    width: MOLD_WALL_THICKNESS,
    height: segmentHeight,
    labelAnchorX: wallRightX + 20,
    labelAnchorY: MOLD_Y + 260 + segmentHeight / 2,
  },
  // Segment 2 — left wall, lower
  {
    x: MOLD_X,
    y: MOLD_Y + 380,
    width: MOLD_WALL_THICKNESS,
    height: segmentHeight,
    labelAnchorX: wallLeftX - 20,
    labelAnchorY: MOLD_Y + 380 + segmentHeight / 2,
  },
  // Segment 3 — right wall, lower
  {
    x: wallRightX,
    y: MOLD_Y + 500,
    width: MOLD_WALL_THICKNESS,
    height: segmentHeight,
    labelAnchorX: wallRightX + 20,
    labelAnchorY: MOLD_Y + 500 + segmentHeight / 2,
  },
];

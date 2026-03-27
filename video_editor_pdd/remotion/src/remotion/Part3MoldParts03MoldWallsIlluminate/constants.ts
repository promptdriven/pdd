// constants.ts — Component-level constants for Part3MoldParts03MoldWallsIlluminate

// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = '#0A0F1A';
export const TOTAL_FRAMES = 300;
export const FPS = 30;

// Blueprint grid
export const GRID_SPACING = 60;
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.05;

// Mold structure
export const MOLD_STROKE_COLOR = '#334155';
export const MOLD_STROKE_WIDTH = 3;
export const WALL_COLOR = '#4A90D9';
export const WALL_GLOW_MIN = 0.2;
export const WALL_GLOW_MAX = 0.5;
export const DIMMED_OPACITY = 0.05;
export const WALL_SEGMENT_WIDTH = 3;

// Mold dimensions (centered on canvas)
export const MOLD_CENTER_X = CANVAS_WIDTH / 2;
export const MOLD_CENTER_Y = CANVAS_HEIGHT / 2;
export const MOLD_OUTER_WIDTH = 600;
export const MOLD_OUTER_HEIGHT = 700;
export const MOLD_INNER_WIDTH = 360;
export const MOLD_INNER_HEIGHT = 500;
export const NOZZLE_WIDTH = 80;
export const NOZZLE_HEIGHT = 60;

// Wall labels
export const LABEL_FONT_FAMILY = "'JetBrains Mono', 'Fira Code', 'Courier New', monospace";
export const LABEL_FONT_SIZE = 14;
export const LABEL_FONT_WEIGHT = 400;
export const LABEL_TEXT_COLOR = '#CDD6F4';
export const LABEL_PILL_COLOR = '#4A90D9';
export const LABEL_PILL_OPACITY = 0.15;
export const LABEL_PILL_RADIUS = 4;
export const LABEL_PILL_PADDING_H = 8;
export const LABEL_PILL_PADDING_V = 4;
export const CONNECTOR_COLOR = '#4A90D9';
export const CONNECTOR_OPACITY = 0.3;
export const CONNECTOR_WIDTH = 1;

// Animation timing
export const ZOOM_START = 0;
export const ZOOM_END = 30;
export const ZOOM_FROM = 1.0;
export const ZOOM_TO = 1.15;

// Wall data
export interface WallLabelData {
  label: string;
  side: 'left' | 'right';
  frameIn: number;
}

export const WALL_LABELS: WallLabelData[] = [
  { label: 'null → None', side: 'left', frameIn: 30 },
  { label: "empty string → ''", side: 'right', frameIn: 75 },
  { label: 'handles unicode', side: 'left', frameIn: 120 },
  { label: 'latency < 100ms', side: 'right', frameIn: 165 },
];

// Segment animation durations
export const SEGMENT_BRIGHTEN_DURATION = 15;
export const LABEL_FADE_DURATION = 20;
export const CONNECTOR_DRAW_DURATION = 15;
export const LABEL_DELAY_AFTER_SEGMENT = 5;

// Wall segment positions (Y offsets from mold center, evenly spaced along inner wall)
export const WALL_SEGMENT_POSITIONS = [
  { y: -180, side: 'left' as const },
  { y: -60, side: 'right' as const },
  { y: 60, side: 'left' as const },
  { y: 180, side: 'right' as const },
];

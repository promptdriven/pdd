// ─── Canvas ──────────────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 870;
export const FPS = 30;

// ─── Background & Grid ──────────────────────────────────────────────────────
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.05;
export const GRID_SPACING = 60;

// ─── Mold Shell ─────────────────────────────────────────────────────────────
export const MOLD_STROKE_COLOR = '#334155';
export const MOLD_STROKE_WIDTH = 3;
export const NOZZLE_COLOR = '#D9944A';
export const NOZZLE_OPACITY = 0.2;

// ─── Walls ──────────────────────────────────────────────────────────────────
export const WALL_GLOW_COLOR = '#4A90D9';
export const WALL_GLOW_INITIAL = 0.4;
export const WALL_GLOW_PEAK = 0.7;
export const WALL_LABEL_FONT = 'JetBrains Mono, monospace';
export const WALL_LABEL_SIZE = 14;

// ─── Liquid ─────────────────────────────────────────────────────────────────
export const LIQUID_LEADING_EDGE = '#FFFFFF';
export const LIQUID_GRADIENT_FROM = '#38BDF8';
export const LIQUID_GRADIENT_TO = '#0D9488';
export const LIQUID_LEADING_OPACITY = 0.9;
export const LIQUID_LEADING_BLUR = 4;

// ─── Ripple ─────────────────────────────────────────────────────────────────
export const RIPPLE_COLOR = '#4A90D9';
export const RIPPLE_OPACITY = 0.2;
export const RIPPLE_DURATION = 10;

// ─── Annotation colors ─────────────────────────────────────────────────────
export const ANNOTATION_RED = '#F87171';
export const ANNOTATION_GREEN = '#4ADE80';
export const ANNOTATION_SOURCE_COLOR = '#94A3B8';
export const ANNOTATION_FONT_SIZE = 16;
export const ANNOTATION_SOURCE_SIZE = 12;

// ─── Wall definitions ───────────────────────────────────────────────────────
export interface WallDef {
  id: string;
  label: string;
  /** X position of the wall within the mold cavity */
  x: number;
  /** Y position (top of wall) */
  y: number;
  /** Height of the wall */
  height: number;
  /** Frame at which liquid reaches this wall */
  hitFrame: number;
}

export const WALLS: WallDef[] = [
  { id: 'type-hints', label: 'Type Hints', x: 420, y: 300, height: 120, hitFrame: 90 },
  { id: 'max-length', label: 'max_length=50', x: 560, y: 260, height: 160, hitFrame: 130 },
  { id: 'null-none', label: 'null → None', x: 700, y: 280, height: 140, hitFrame: 200 },
  { id: 'auth-check', label: 'auth_required', x: 840, y: 300, height: 120, hitFrame: 240 },
];

// Focus wall (null → None)
export const FOCUS_WALL_ID = 'null-none';
export const FOCUS_WALL_INDEX = 2;

// ─── Mold geometry ──────────────────────────────────────────────────────────
export const MOLD_LEFT = 200;
export const MOLD_TOP = 200;
export const MOLD_WIDTH = 800;
export const MOLD_HEIGHT = 500;
export const NOZZLE_X = 280;
export const NOZZLE_Y = 200;
export const NOZZLE_WIDTH = 40;
export const NOZZLE_HEIGHT = 60;

// ─── Cavity path (the area liquid fills) ────────────────────────────────────
export const CAVITY_TOP = 260;
export const CAVITY_BOTTOM = 440;
export const CAVITY_LEFT = 260;
export const CAVITY_RIGHT = 920;

// ─── Annotation positions ───────────────────────────────────────────────────
export const ANNOTATION_1_POS = { x: 1100, y: 320 };
export const ANNOTATION_2_POS = { x: 1100, y: 430 };

// ─── Frame ranges ───────────────────────────────────────────────────────────
export const PHASE_LIQUID_START = 0;
export const PHASE_FIRST_WALL_HIT = 90;
export const PHASE_ZOOM_START = 180;
export const PHASE_ZOOM_DURATION = 30;
export const PHASE_ZOOM_END = 270;
export const PHASE_PULLBACK_DURATION = 30;
export const PHASE_ANNOTATION_1_IN = 330;
export const PHASE_ANNOTATION_2_IN = 510;
export const PHASE_GLOW_INCREASE_START = 510;
export const PHASE_GLOW_INCREASE_DURATION = 60;

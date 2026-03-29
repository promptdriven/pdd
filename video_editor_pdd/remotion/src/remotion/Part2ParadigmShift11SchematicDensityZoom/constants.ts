// ─── Canvas ───
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 420;

// ─── Colors ───
export const BG_COLOR = '#F5F0E8';
export const GRID_COLOR = '#E0D8C8';
export const GRID_OPACITY = 0.15;
export const STROKE_COLOR = '#2D3748';
export const WIRE_COLOR = '#4A5568';
export const HAND_COLOR = '#78909C';
export const HAND_OPACITY = 0.5;
export const COUNTER_COLOR = '#4A5568';
export const COUNTER_LABEL_COLOR = '#94A3B8';

// ─── Grid ───
export const GRID_SPACING = 40;

// ─── Transistor symbol dimensions (at scale=1) ───
export const TRANSISTOR_WIDTH = 28;
export const TRANSISTOR_HEIGHT = 36;
export const TRANSISTOR_STROKE_WIDTH = 1.5;
export const WIRE_STROKE_WIDTH = 1;

// ─── Zoom ───
export const ZOOM_START_SCALE = 8;
export const ZOOM_END_SCALE = 0.1;

// ─── Counter ───
export const COUNTER_START = 20;
export const COUNTER_END = 50000;
export const COUNTER_FONT_SIZE = 36;
export const COUNTER_LABEL_FONT_SIZE = 18;
export const COUNTER_X = 1660;
export const COUNTER_Y = 960;

// ─── Animation phases (frame ranges) ───
export const PHASE_1_END = 60;    // Close-up, ~20 transistors
export const PHASE_2_END = 150;   // Zoom starts, 100→500
export const PHASE_3_END = 240;   // 500→5000, hand slows
export const PHASE_4_END = 330;   // 5000→25000, hand fades
export const PHASE_5_END = 420;   // 25000→50000, dense mass

// ─── Hand animation ───
export const HAND_FADE_START = 240;
export const HAND_FADE_DURATION = 30;
export const HAND_VISIBLE_END = 300; // Sequence durationInFrames

// ─── Schematic layout ───
export const SCHEMATIC_CENTER_X = 960;
export const SCHEMATIC_CENTER_Y = 540;
export const SCHEMATIC_SPREAD = 6000; // total area for transistor placement at full density

// ============================================================
// constants.ts – Schematic Density Zoom-Out
// ============================================================

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 420;

// Background & grid
export const BG_COLOR = '#F5F0E8'; // warm cream/paper
export const GRID_COLOR = '#E0D8C8';
export const GRID_OPACITY = 0.15;
export const GRID_SPACING = 40;

// Schematic line colors
export const STROKE_COLOR = '#2D3748'; // transistor symbols
export const WIRE_COLOR = '#4A5568'; // connection wires
export const STROKE_WIDTH = 1.5;
export const WIRE_WIDTH = 1;

// Drawing hand
export const HAND_COLOR = '#78909C';
export const HAND_OPACITY = 0.5;
export const HAND_FADE_START = 240; // frame where hand starts fading
export const HAND_FADE_DURATION = 30;
export const HAND_VISIBLE_END = 300; // hand gone by frame 300

// Counter
export const COUNTER_COLOR = '#4A5568';
export const COUNTER_LABEL_COLOR = '#94A3B8';
export const COUNTER_FONT_SIZE = 36;
export const COUNTER_LABEL_SIZE = 14;
export const COUNTER_X = 1660;
export const COUNTER_Y = 940;

// Zoom
export const ZOOM_START_SCALE = 8;
export const ZOOM_END_SCALE = 0.1;

// Animation phases (frame ranges)
export const PHASE_1_END = 60; // close-up, ~20 transistors
export const PHASE_2_END = 150; // 100-500 transistors
export const PHASE_3_END = 240; // 500-5000 transistors
export const PHASE_4_END = 330; // 5000-25000 transistors
export const PHASE_5_END = 420; // 25000-50000 transistors

// Counter milestones
export const COUNTER_START = 20;
export const COUNTER_END = 50000;

// Transistor symbol dimensions (in local schematic space)
export const TRANSISTOR_SIZE = 24;
export const TRANSISTOR_SPACING = 36;

// Schematic canvas dimensions (virtual, before zoom)
export const SCHEMATIC_WIDTH = 12000;
export const SCHEMATIC_HEIGHT = 8000;

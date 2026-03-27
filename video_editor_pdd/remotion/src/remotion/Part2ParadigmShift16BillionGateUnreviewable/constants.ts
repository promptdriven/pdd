// constants.ts — Part2ParadigmShift16BillionGateUnreviewable

export const DURATION_FRAMES = 360;
export const FPS = 30;

// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BG_COLOR = '#0A0F1A';

// Chip layout colors
export const GATE_COLORS = ['#4A90D9', '#5AAA6E', '#D9944A'] as const;
export const GATE_OPACITY = 0.6;
export const WIRE_COLOR = '#64748B';
export const WIRE_OPACITY = 0.3;
export const WIRE_WIDTH = 0.5;

// Gate dimensions at base zoom
export const GATE_WIDTH = 4;
export const GATE_HEIGHT = 2;
export const GATE_GAP_X = 2;
export const GATE_GAP_Y = 2;

// Zoom animation
export const ZOOM_START = 1;
export const ZOOM_END = 8;

// Chip phase timing
export const CHIP_START = 0;
export const CHIP_END = 150;
export const ZOOM_PHASE_1_END = 60;
export const ZOOM_PHASE_2_END = 120;
export const ZOOM_PHASE_3_END = 150;

// Diff phase timing
export const DIFF_START = 150;
export const DIFF_FAST_END = 300;
export const DIFF_SLOW_END = 360;
export const DIFF_LABEL_FADE_START = 165; // 15 frames after diff starts

// Code diff colors
export const DIFF_BG_COLOR = '#1E293B';
export const DIFF_ADD_BG = '#5AAA6E';
export const DIFF_DELETE_BG = '#EF4444';
export const DIFF_ADD_BG_OPACITY = 0.15;
export const DIFF_DELETE_BG_OPACITY = 0.15;
export const DIFF_TEXT_COLOR = '#E2E8F0';
export const LINE_NUMBER_COLOR = '#64748B';

// Typography
export const LABEL_FONT = 'Inter, sans-serif';
export const CODE_FONT = 'JetBrains Mono, monospace';
export const LABEL_SIZE = 18;
export const CODE_SIZE = 14;
export const LINE_NUMBER_SIZE = 12;
export const LABEL_COLOR = '#94A3B8';

// Label positions (lower-right)
export const LABEL_X = 1650;
export const LABEL_Y = 980;
export const LABEL_FADE_DURATION = 15;

// Data
export const GATE_COUNT_LABEL = '2.1 billion gates';
export const LINES_CHANGED_LABEL = '47,382 lines changed';
export const TOTAL_DIFF_LINES = 47382;

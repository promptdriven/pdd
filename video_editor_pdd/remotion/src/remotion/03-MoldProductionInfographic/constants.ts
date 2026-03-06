// Part2ParadigmShift03MoldProductionInfographic constants

// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 600;

// Infographic region / backing panel
export const PANEL_X = 260;
export const PANEL_Y = 290;
export const PANEL_W = 1400;
export const PANEL_H = 500;
export const PANEL_BORDER_RADIUS = 16;
export const PANEL_BG = "rgba(15, 23, 42, 0.75)";
export const PANEL_BLUR = 8;

// Mold shape
export const MOLD_X = 320;
export const MOLD_Y = 390;
export const MOLD_W = 200;
export const MOLD_H = 300;
export const MOLD_FILL = "#334155";
export const MOLD_GLOW_COLOR = "#F97316";
export const MOLD_CAVITY_W = 120;
export const MOLD_CAVITY_H = 80;
export const MOLD_CAVITY_FILL = "#1E293B";
export const MOLD_LABEL_TEXT = "MOLD";

// Conveyor belt
export const CONVEYOR_X_START = 520;
export const CONVEYOR_X_END = 1580;
export const CONVEYOR_Y = 540;
export const CONVEYOR_STROKE = "#475569";
export const CONVEYOR_STROKE_WIDTH = 4;

// Parts
export const PART_W = 60;
export const PART_H = 40;
export const PART_FILL = "#E2E8F0";
export const PART_BORDER = "#CBD5E1";
export const PART_Y = 510;
export const NORMAL_INTERVAL = 15;
export const FAST_INTERVAL = 5;
// How many frames a part takes to traverse the full conveyor
export const PART_TRAVEL_FRAMES = 120;

// Counter
export const COUNTER_X = 1500;
export const COUNTER_Y = 320;

// Defect / fix colors
export const DEFECT_COLOR = "#EF4444";
export const FIX_COLOR = "#22C55E";

// Colors
export const BG_COLOR = "#0A1628";
export const ACCENT_ORANGE = "#F97316";
export const TEXT_WHITE = "#FFFFFF";
export const TEXT_MUTED = "#94A3B8";

// ── Animation timing (frames at 30fps) ──

// Phase 1: Panel + mold fade in (0-1s)
export const PANEL_FADE_START = 0;
export const PANEL_FADE_END = 30;
export const MOLD_FADE_START = 0;
export const MOLD_FADE_END = 30;

// Phase 2: Label + conveyor draw (0.67-1.33s)
export const LABEL_FADE_START = 20;
export const LABEL_FADE_END = 40;
export const CONVEYOR_DRAW_START = 20;
export const CONVEYOR_DRAW_END = 40;

// Phase 3: Parts stream at normal rate (1.33-6s)
export const STREAM_START = 40;

// Phase 4: Parts stream at fast rate (6-8s)
export const STREAM_FAST_START = 180;

// Phase 5: Counter hits 1000+, stream pauses (8-9s)
export const STREAM_PAUSE = 240;

// Phase 6: Defect appears (9-9.67s)
export const DEFECT_APPEAR = 270;

// Phase 7: Traceback line (9.67-11s)
export const TRACEBACK_START = 290;
export const TRACEBACK_END = 330;

// Phase 8: Wrench fix (11-12s)
export const WRENCH_APPEAR = 330;
export const WRENCH_FLASH_DURATION = 30;

// Phase 9: Defect dissolves, corrected stream resumes (12-13s)
export const DEFECT_DISSOLVE_START = 360;
export const DEFECT_DISSOLVE_END = 390;
export const CORRECTED_STREAM_START = 390;

// Phase 10: Fade out (19-20s)
export const FADEOUT_START = 570;
export const FADEOUT_END = 600;

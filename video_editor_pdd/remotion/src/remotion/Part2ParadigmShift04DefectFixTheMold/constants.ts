// Part2ParadigmShift04DefectFixTheMold constants

// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 420;
export const FPS = 30;

// Background
export const BG_COLOR = "#0A0F1A";
export const GRID_SPACING = 40;
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.04;

// Mold diagram
export const MOLD_CENTER_X = 960;
export const MOLD_CENTER_Y = 400;
export const MOLD_WIDTH = 400;
export const MOLD_HEIGHT = 500;
export const MOLD_STROKE_COLOR = "#475569";
export const MOLD_STROKE_OPACITY = 0.6;
export const MOLD_STROKE_WIDTH = 2;
export const MOLD_WALL_FILL = "#D9944A";
export const MOLD_WALL_FILL_OPACITY = 0.1;
export const MOLD_CAVITY_COLOR = "#1E293B";
export const MOLD_CAVITY_OPACITY = 0.3;

// Ejected parts
export const PART_WIDTH = 80;
export const PART_HEIGHT = 50;
export const PART_COLOR = "#94A3B8";
export const PART_OPACITY = 0.5;
export const PART_EJECT_FROM_Y = 650;
export const PART_EJECT_TO_Y = 780;

// Defect colors
export const DEFECT_COLOR = "#EF4444";
export const DEFECT_PULSE_RADIUS = 16;
export const DEFECT_OPACITY = 0.4;
export const DEFECT_LABEL_OPACITY = 0.7;
export const MAGNIFY_SIZE = 40;
export const MAGNIFY_COLOR = "#E2E8F0";
export const MAGNIFY_OPACITY = 0.5;

// Fixed parts
export const FIXED_COLOR = "#5AAA6E";
export const FIXED_OPACITY = 0.5;
export const CHECKMARK_COLOR = "#5AAA6E";

// Mold adjustment
export const ADJUSTMENT_COLOR = "#D9944A";
export const ADJUSTMENT_WALL_OPACITY_START = 0.3;
export const ADJUSTMENT_WALL_OPACITY_END = 0.6;
export const ADJUSTMENT_PX = 4;
export const CURSOR_COLOR = "#E2E8F0";
export const CURSOR_OPACITY = 0.6;

// Red X (rejected patch)
export const RED_X_SIZE = 40;
export const RED_X_STROKE_WIDTH = 2;
export const GHOST_TOOL_OPACITY = 0.2;

// Typography
export const FONT_FAMILY = "'Inter', sans-serif";
export const DEFECT_LABEL_SIZE = 13;
export const FIX_MOLD_LABEL_SIZE = 14;
export const FIX_MOLD_LABEL_WEIGHT = 600;
export const COUNTER_LABEL_SIZE = 14;

// Label positions
export const DEFECT_LABEL_X = 1060;
export const DEFECT_LABEL_Y = 810;
export const FIX_MOLD_LABEL_X = 1200;
export const FIX_MOLD_LABEL_Y = 350;
export const COUNTER_LABEL_X = 1600;
export const COUNTER_LABEL_Y = 900;

// Animation timing (frames at 30fps)
// Act 0: Mold draws
export const MOLD_DRAW_START = 0;
export const MOLD_DRAW_END = 30;

// Act 1: Part ejects
export const PART_EJECT_START = 30;
export const PART_EJECT_END = 50;

// Act 1: Defect highlight
export const DEFECT_PULSE_START = 60;
export const DEFECT_LABEL_FADE_START = 70;
export const DEFECT_LABEL_FADE_END = 85;
export const MAGNIFY_APPEAR_START = 60;
export const MAGNIFY_APPEAR_END = 75;
export const DEFECT_PULSE_CYCLE = 20; // frames per pulse cycle

// Act 2: Rejected patch
export const GHOST_TOOL_START = 100;
export const GHOST_TOOL_END = 115;
export const RED_X_START = 110;
export const RED_X_END = 120;
export const REJECTED_FADE_START = 125;
export const REJECTED_FADE_END = 140;

// Act 2: Fix the mold
export const WALL_ADJUST_START = 140;
export const WALL_ADJUST_END = 170;
export const CURSOR_APPEAR_START = 140;
export const CURSOR_APPEAR_END = 155;
export const FIX_LABEL_FADE_START = 155;
export const FIX_LABEL_FADE_END = 175;

// Act 3: Fixed parts eject
export const FIXED_PARTS_START = 200;
export const FIXED_PART_INTERVAL = 25;
export const FIXED_PART_COUNT = 5;
export const CHECKMARK_POP_DURATION = 10;

// Act 3: Defective part dissolve
export const DISSOLVE_START = 280;
export const DISSOLVE_END = 310;

// Act 3: Counter label
export const COUNTER_FADE_START = 300;
export const COUNTER_FADE_END = 320;

// Act 3: Hold / ambient glow
export const AMBIENT_GLOW_START = 340;
export const AMBIENT_GLOW_CYCLE = 60; // frames per ambient pulse

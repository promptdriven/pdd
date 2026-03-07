// Part2ParadigmShift08SplitManualVsSpecification — constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 360;

// Layout region: 1600×600 at (160, 240)
export const LAYOUT_X = 160;
export const LAYOUT_Y = 240;
export const LAYOUT_W = 1600;
export const LAYOUT_H = 600;
export const PANEL_RADIUS = 20;
export const PANEL_BG = "rgba(15, 23, 42, 0.85)";

// Column definitions: three 480px columns with 40px gutters
export const COLUMN_WIDTH = 480;
export const GUTTER = 40;
export const COLUMNS = [
  { x: 200, industry: "TEXTILES" },
  { x: 720, industry: "PLASTICS" },
  { x: 1240, industry: "SEMICONDUCTORS" },
] as const;

// Row positions
export const BEFORE_ROW_Y = 340;
export const BEFORE_ROW_H = 180;
export const DIVIDER_Y = 530;
export const AFTER_ROW_Y = 540;
export const AFTER_ROW_H = 180;

// Row tints
export const BEFORE_TINT = "rgba(249, 115, 22, 0.06)";
export const AFTER_TINT = "rgba(59, 130, 246, 0.06)";

// Colors
export const BEFORE_COLOR = "#F97316";
export const AFTER_COLOR = "#3B82F6";
export const HEADER_COLOR = "#94A3B8";
export const DESCRIPTOR_COLOR = "#CBD5E1";
export const SHIFT_TEXT_COLOR = "#FFFFFF";
export const BANNER_COLOR = "#E2E8F0";

// Icon size
export const ICON_SIZE = 64;

// Column data
export const COLUMN_DATA = [
  {
    industry: "TEXTILES",
    beforeIcon: "needle_thread" as const,
    beforeText: "Hand-darning",
    afterIcon: "factory_loom" as const,
    afterText: "Automated weaving",
  },
  {
    industry: "PLASTICS",
    beforeIcon: "hands_sculpting" as const,
    beforeText: "Hand-sculpting",
    afterIcon: "injection_mold" as const,
    afterText: "Mold specification",
  },
  {
    industry: "SEMICONDUCTORS",
    beforeIcon: "pencil_ruler" as const,
    beforeText: "Hand-drawn gates",
    afterIcon: "code_terminal" as const,
    afterText: "HDL + synthesis",
  },
] as const;

// Animation keyframes (at 30fps)
export const PANEL_FADE_START = 0;
export const PANEL_FADE_END = 20;

export const COL1_SLIDE_START = 20;
export const COL1_SLIDE_END = 50;
export const COL2_SLIDE_START = 40;
export const COL2_SLIDE_END = 70;
export const COL3_SLIDE_START = 60;
export const COL3_SLIDE_END = 90;

export const DIVIDER_SWEEP_START = 90;
export const DIVIDER_SWEEP_END = 120;
export const SHIFT_LABEL_FADE_START = 90;
export const SHIFT_LABEL_FADE_END = 110;

export const AFTER_REVEAL_START = 120;

export const BEFORE_DIM_START = 150;
export const BEFORE_DIM_END = 240;

export const BANNER_FADE_START = 240;
export const BANNER_FADE_END = 280;

export const FADEOUT_START = 330;
export const FADEOUT_END = 360;

// Spring configs
export const COLUMN_SPRING = { damping: 18, stiffness: 140 };
export const AFTER_ICON_SPRING = { damping: 12, stiffness: 200 };

// Banner
export const BANNER_TEXT =
  "We\u2019ve seen this before \u2014 we just didn\u2019t recognize it.";
export const BANNER_Y = 800;

// Shift divider
export const SHIFT_LABEL = "THE SHIFT";

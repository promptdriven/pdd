// Part2ParadigmShift07HdlTimeline constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;

// Timeline region
export const PANEL_X = 260;
export const PANEL_Y = 700;
export const PANEL_W = 1400;
export const PANEL_H = 280;
export const PANEL_RADIUS = 16;
export const PANEL_BG = "rgb(15, 23, 42)";

// Timeline track
export const TRACK_Y = 810;
export const TRACK_X_START = 400;
export const TRACK_X_END = 1520;
export const TRACK_THICKNESS = 3;
export const TRACK_BASE_COLOR = "#1E293B";

// Node data
export const NODES = [
  {
    year: "1980s",
    descriptor: "Manual Layout",
    icon: "pencil" as const,
    color: "#F97316",
    x: 400,
    activateFrame: 25,
  },
  {
    year: "1985",
    descriptor: "Verilog HDL",
    icon: "code_brackets" as const,
    color: "#A855F7",
    x: 960,
    activateFrame: 90,
  },
  {
    year: "1990s+",
    descriptor: "Automated Synthesis",
    icon: "chip" as const,
    color: "#3B82F6",
    x: 1520,
    activateFrame: 180,
  },
] as const;

// Node dimensions
export const NODE_CIRCLE_SIZE = 56;
export const NODE_ICON_SIZE = 40;
export const NODE_BORDER_WIDTH = 3;
export const NODE_FILL = "#1E293B";

// Colors
export const DESCRIPTOR_COLOR = "#CBD5E1";
export const CONCLUSION_TEXT_COLOR = "#E2E8F0";
export const UNDERLINE_COLOR = "#3B82F6";
export const GRADIENT_START = "#F97316";
export const GRADIENT_END = "#3B82F6";

// Conclusion
export const CONCLUSION_TEXT = "Specification replaced manual construction";
export const CONCLUSION_Y = 940;

// Animation frames (30fps)
export const FPS = 30;
export const TOTAL_FRAMES = 750;

// Phase timings
export const PANEL_FADE_END = 25;
export const NODE1_ACTIVATE = 25;
export const NODE2_ACTIVATE = 90;
export const NODE1_DIM_START = 130;
export const NODE1_DIM_END = 180;
export const NODE2_DIM_START = 180;
export const NODE2_DIM_END = 220;
export const NODE3_ACTIVATE = 180;
export const CONCLUSION_START = 280;
export const CONCLUSION_FADE_END = 310; // 280 + 30
export const UNDERLINE_DRAW_START = 300; // 280 + 20
export const UNDERLINE_DRAW_END = 330; // 280 + 50
export const FADEOUT_START = 600;
export const FADEOUT_END = 750;

// Radial pulse
export const PULSE_DURATION = 20;

// Spring config
export const SPRING_CONFIG = { damping: 12, stiffness: 200 };

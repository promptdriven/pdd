// Part2ParadigmShift09AbstractionStaircase constants

// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = "#0A0F1A";
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.03;

// Total duration
export const TOTAL_FRAMES = 480;
export const FPS = 30;

// Step dimensions
export const STEP_WIDTH = 280;
export const STEP_HEIGHT = 120;
export const STEP_SURFACE_COLOR = "#1E293B";
export const STEP_SURFACE_OPACITY = 0.3;
export const STEP_STROKE_COLOR = "#334155";
export const STEP_STROKE_OPACITY = 0.4;
export const STEP_RISER_COLOR = "#0F172A";
export const STEP_RISER_STROKE_OPACITY = 0.3;

// Arrow colors
export const ARROW_COLOR = "#EF4444";
export const ARROW_OPACITY = 0.3;
export const ARROW_LABEL_OPACITY = 0.4;
export const TENSION_LINE_OPACITY = 0.15;

// Step 5 active color
export const ACTIVE_COLOR = "#D9944A";
export const ACTIVE_GLOW_OPACITY = 0.12;
export const PULSE_PERIOD = 40;

// Y-axis label
export const Y_AXIS_COLOR = "#475569";
export const Y_AXIS_OPACITY = 0.2;

// Step data
export interface StepData {
  level: number;
  label: string;
  decade: string;
  x: number;
  y: number;
  color: string;
  iconType: "transistor" | "schematic" | "verilog" | "hls" | "prompt";
  isActive?: boolean;
}

export const STEPS: StepData[] = [
  {
    level: 1,
    label: "Transistors",
    decade: "1970s",
    x: 120,
    y: 800,
    color: "#64748B",
    iconType: "transistor",
  },
  {
    level: 2,
    label: "Schematics",
    decade: "1980s",
    x: 400,
    y: 680,
    color: "#7A8FA3",
    iconType: "schematic",
  },
  {
    level: 3,
    label: "RTL / Verilog",
    decade: "1990s",
    x: 680,
    y: 560,
    color: "#94A3B8",
    iconType: "verilog",
  },
  {
    level: 4,
    label: "Behavioral / HLS",
    decade: "2010s",
    x: 960,
    y: 440,
    color: "#B0BEC5",
    iconType: "hls",
  },
  {
    level: 5,
    label: "Natural Language → Code",
    decade: "2020s",
    x: 1240,
    y: 320,
    color: "#D9944A",
    iconType: "prompt",
    isActive: true,
  },
];

// Animation timing (frame ranges)
export const ANIM = {
  // Phase 1: Background + grid + y-axis
  BG_START: 0,
  BG_END: 30,

  // Steps appear sequentially - each step gets ~50 frames
  STEP_BASE_FRAME: 30, // first step starts at frame 30
  STEP_INTERVAL: 50, // frames between each step start

  // Within each step's sequence
  ARROW_DRAW_DURATION: 15,
  TENSION_LINE_DURATION: 8,
  STEP_DRAW_DURATION: 20,
  ICON_POP_DELAY: 10,
  ICON_POP_DURATION: 12,
  LABEL_FADE_DURATION: 15,

  // Step 5 special: starts at frame 240 (30 + 4*50 = 230, but spec says 240)
  STEP5_GLOW_START: 240,

  // Hold phase
  HOLD_START: 320,
  PARTICLE_START: 400,
} as const;

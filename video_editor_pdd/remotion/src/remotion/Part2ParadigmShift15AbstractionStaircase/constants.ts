// constants.ts — Abstraction Staircase visual constants

export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 690;
export const FPS = 30;

// Colors
export const BG_COLOR = "#0A0F1A";
export const GRID_LINE_COLOR = "#1E293B";
export const GRID_LINE_OPACITY = 0.05;
export const STEP_LABEL_COLOR = "#E2E8F0";
export const AXIS_LABEL_COLOR = "#94A3B8";
export const ARROW_COLOR = "#EF4444";
export const ARROW_OPACITY = 0.6;
export const EMPHASIS_COLOR = "#5AAA6E";

// Step data
export interface StepDef {
  label: string;
  decade: string;
  x1: number;
  x2: number;
  y: number;
  stepHeight: number;
  fillColor: string;
  fillOpacity: number;
  emphasis: boolean;
}

export const STEPS: StepDef[] = [
  {
    label: "Transistors",
    decade: "1970s",
    x1: 120,
    x2: 400,
    y: 800,
    stepHeight: 60,
    fillColor: "#D9944A",
    fillOpacity: 0.3,
    emphasis: false,
  },
  {
    label: "Schematics",
    decade: "1980s",
    x1: 400,
    x2: 680,
    y: 650,
    stepHeight: 60,
    fillColor: "#D9944A",
    fillOpacity: 0.25,
    emphasis: false,
  },
  {
    label: "RTL / Verilog",
    decade: "1990s",
    x1: 680,
    x2: 960,
    y: 500,
    stepHeight: 60,
    fillColor: "#4A90D9",
    fillOpacity: 0.25,
    emphasis: false,
  },
  {
    label: "Behavioral / HLS",
    decade: "2010s",
    x1: 960,
    x2: 1240,
    y: 350,
    stepHeight: 60,
    fillColor: "#4A90D9",
    fillOpacity: 0.2,
    emphasis: false,
  },
  {
    label: "Natural language → Code",
    decade: "2020s",
    x1: 1240,
    x2: 1580,
    y: 200,
    stepHeight: 60,
    fillColor: "#5AAA6E",
    fillOpacity: 0.3,
    emphasis: true,
  },
];

// Animation timing (frame ranges)
export const STEP_FRAME_STARTS = [0, 60, 120, 180, 240];
export const STEP_DRAW_DURATION = 40; // frames for step to draw in
export const ARROW_DELAY = 40; // frames after step start before arrow draws
export const ARROW_DRAW_DURATION = 20;
export const STEP5_PULSE_START = 360;
export const STEP5_PULSE_CYCLE = 45;
export const FADE_OUT_START = 630;
export const FADE_OUT_DURATION = 60;

// Decade markers for x-axis
export const DECADE_MARKERS = [
  { label: "1970s", x: 260 },
  { label: "1980s", x: 540 },
  { label: "1990s", x: 820 },
  { label: "2010s", x: 1100 },
  { label: "2020s", x: 1410 },
];

// Grid line y-positions (at each step height)
export const GRID_Y_POSITIONS = [200, 350, 500, 650, 800];

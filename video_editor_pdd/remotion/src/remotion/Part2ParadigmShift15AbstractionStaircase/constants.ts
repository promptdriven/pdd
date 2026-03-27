// constants.ts — Abstraction Staircase visual constants

export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 690;
export const FPS = 30;

// Background
export const BG_COLOR = "#0A0F1A";

// Grid
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.05;

// Step colors
export const STEP_AMBER = "#D9944A";
export const STEP_BLUE = "#4A90D9";
export const STEP_GREEN = "#5AAA6E";

// Transition (arrow) colors
export const ARROW_COLOR = "#EF4444";
export const ARROW_OPACITY = 0.6;

// Text colors
export const LABEL_COLOR = "#E2E8F0";
export const AXIS_COLOR = "#94A3B8";

// Step data
export interface StepData {
  label: string;
  decade: string;
  x: number;
  width: number;
  y: number;
  stepHeight: number;
  fillColor: string;
  fillOpacity: number;
  borderColor: string;
  emphasis: boolean;
}

export const STEPS: StepData[] = [
  {
    label: "Transistors",
    decade: "1970s",
    x: 120,
    width: 280,
    y: 800,
    stepHeight: 60,
    fillColor: STEP_AMBER,
    fillOpacity: 0.3,
    borderColor: STEP_AMBER,
    emphasis: false,
  },
  {
    label: "Schematics",
    decade: "1980s",
    x: 400,
    width: 280,
    y: 650,
    stepHeight: 60,
    fillColor: STEP_AMBER,
    fillOpacity: 0.25,
    borderColor: STEP_AMBER,
    emphasis: false,
  },
  {
    label: "RTL / Verilog",
    decade: "1990s",
    x: 680,
    width: 280,
    y: 500,
    stepHeight: 60,
    fillColor: STEP_BLUE,
    fillOpacity: 0.25,
    borderColor: STEP_BLUE,
    emphasis: false,
  },
  {
    label: "Behavioral / HLS",
    decade: "2010s",
    x: 960,
    width: 280,
    y: 350,
    stepHeight: 60,
    fillColor: STEP_BLUE,
    fillOpacity: 0.2,
    borderColor: STEP_BLUE,
    emphasis: false,
  },
  {
    label: "Natural language → Code",
    decade: "2020s",
    x: 1240,
    width: 340,
    y: 200,
    stepHeight: 60,
    fillColor: STEP_GREEN,
    fillOpacity: 0.3,
    borderColor: STEP_GREEN,
    emphasis: true,
  },
];

// Animation timing (frame numbers)
export const STEP_ENTRANCE_FRAMES = [0, 60, 120, 180, 240];
export const STEP_DRAW_DURATION = 40; // frames to draw each step
export const ARROW_DELAY = 40; // frames after step start for arrow
export const ARROW_DRAW_DURATION = 20;
export const STEP5_PULSE_START = 360;
export const STEP5_PULSE_CYCLE = 45;
export const FADE_OUT_START = 630;
export const FADE_OUT_DURATION = 60;

// Decade markers for X axis
export const DECADE_MARKERS = [
  { label: "1970s", x: 260 },
  { label: "1980s", x: 540 },
  { label: "1990s", x: 820 },
  { label: "2010s", x: 1100 },
  { label: "2020s", x: 1410 },
];

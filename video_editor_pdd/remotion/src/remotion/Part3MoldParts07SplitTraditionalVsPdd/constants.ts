// constants.ts — colors, dimensions, step data for split-screen comparison

export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 240;

// Background
export const BG_COLOR = "#0A0F1A";

// Divider
export const DIVIDER_COLOR = "#FFFFFF";
export const DIVIDER_WIDTH = 2;
export const DIVIDER_OPACITY = 0.7; // meets minimum divider opacity contract

// Panel dimensions
export const PANEL_WIDTH = 920;
export const DIVIDER_ZONE = 80;

// Traditional (left) panel colors
export const TRAD_HEADER_COLOR = "#F87171";
export const TRAD_BORDER_COLOR = "#F87171";
export const TRAD_ARROW_COLOR = "#F87171";
export const TRAD_BANDAID_COLOR = "#F87171";
export const TRAD_ELLIPSIS_COLOR = "#F87171";

// PDD (right) panel colors
export const PDD_HEADER_COLOR = "#4ADE80";
export const PDD_BORDER_COLOR = "#4A90D9";
export const PDD_ARROW_COLOR = "#4A90D9";
export const PDD_GLOW_COLOR = "#4ADE80";
export const PDD_CODE_COLOR = "#A6E3A1";

// Step box shared
export const STEP_FILL = "#1E1E2E";
export const STEP_TEXT_COLOR = "#CDD6F4";
export const STEP_BORDER_OPACITY = 0.2;
export const STEP_BOX_RADIUS = 6;
export const STEP_HEIGHT = 40;
export const TRAD_STEP_WIDTH = 260;
export const PDD_STEP_WIDTH = 280;

// Typography
export const HEADER_SIZE = 20;
export const STEP_TEXT_SIZE = 14;
export const CODE_TEXT_SIZE = 13;
export const CHECKMARK_SIZE = 18;

// Arrows
export const ARROW_STROKE_WIDTH = 1.5;
export const ARROW_OPACITY = 0.3;
export const ARROW_LENGTH = 30;

// Layout positions
export const HEADER_Y = 120;
export const FLOW_START_Y = 200;
export const STEP_SPACING = 70; // step height (40) + arrow gap (30)

// Animation timing
export const FADE_DURATION = 15;
export const ARROW_DRAW_DURATION = 10;
export const GLOW_CYCLE = 30;
export const ELLIPSIS_CYCLE = 20;

// Step data
export interface StepData {
  text: string;
  hasBandaid: boolean;
  hasCode: boolean;
  codeText?: string;
  isFinal: boolean;
  startFrame: number;
}

export const TRADITIONAL_STEPS: StepData[] = [
  { text: "Bug found", hasBandaid: false, hasCode: false, isFinal: false, startFrame: 20 },
  { text: "Patch code", hasBandaid: true, hasCode: false, isFinal: false, startFrame: 50 },
  { text: "Similar bug elsewhere", hasBandaid: false, hasCode: false, isFinal: false, startFrame: 80 },
  { text: "Patch again", hasBandaid: true, hasCode: false, isFinal: false, startFrame: 110 },
  { text: "Different bug", hasBandaid: false, hasCode: false, isFinal: false, startFrame: 140 },
  { text: "Patch again...", hasBandaid: true, hasCode: false, isFinal: false, startFrame: 140 },
];

export const PDD_STEPS: StepData[] = [
  { text: "Bug found", hasBandaid: false, hasCode: false, isFinal: false, startFrame: 20 },
  { text: "Add test", hasBandaid: false, hasCode: true, codeText: "pdd bug", isFinal: false, startFrame: 50 },
  { text: "Regenerate", hasBandaid: false, hasCode: true, codeText: "pdd fix", isFinal: false, startFrame: 80 },
  { text: "Bug impossible forever ✓", hasBandaid: false, hasCode: false, isFinal: true, startFrame: 110 },
];

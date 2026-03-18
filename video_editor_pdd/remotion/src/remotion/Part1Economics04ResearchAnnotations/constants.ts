// === Colors ===
export const BG_COLOR = '#0D1117';
export const CHART_BG = '#1A2332';
export const BLUE = '#4A90D9';
export const AMBER = '#D9944A';
export const RED = '#E74C3C';
export const MUTED = '#94A3B8';
export const WHITE = '#E6EDF3';
export const GREEN = '#22C55E';

// === Layout ===
export const WIDTH = 1920;
export const HEIGHT = 1080;

// Chart area within the canvas
export const CHART_LEFT = 140;
export const CHART_RIGHT = 1380;
export const CHART_TOP = 120;
export const CHART_BOTTOM = 820;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// Annotation area (right panel)
export const ANNOTATION_X = 1420;
export const ANNOTATION_WIDTH = 460;

// === Chart Data ===
// X-axis years
export const YEARS = [2019, 2020, 2021, 2022, 2023, 2024, 2025];

// Normalized values (0-1 range, mapped to chart)
// Line 1: Immediate patch cost (solid green) — drops as AI speeds things up
export const IMMEDIATE_COST_DATA = [0.85, 0.82, 0.78, 0.55, 0.42, 0.35, 0.30];

// Line 2: Total cost with debt (dashed amber) — stays flat / rises
export const TOTAL_COST_DATA = [0.85, 0.83, 0.80, 0.78, 0.82, 0.87, 0.92];

// Line 3: Debt accumulation (shaded area between lines 1 and 2)
// The "debt" is the gap between total cost and immediate cost

// === Animation Timing (frames) ===
export const FPS = 30;
export const TOTAL_FRAMES = 900;

// Annotation appearances
export const ANNOTATION_1_START = 30;   // GitHub study
export const ANNOTATION_2_START = 120;  // Uplevel study
export const ANNOTATION_3_START = 240;  // GitClear study
export const DEBT_SPLIT_START = 540;    // Debt decomposition

// Durations
export const FADE_DURATION = 20;
export const SLIDE_DISTANCE = 8;
export const CONNECTION_LINE_DURATION = 15;
export const DEBT_SPLIT_DURATION = 30;

// === Chart axis labels ===
export const Y_AXIS_LABEL = 'Relative Cost per Feature';
export const X_AXIS_LABEL = 'Year';
export const CHART_TITLE = 'The AI Coding Productivity Paradox';

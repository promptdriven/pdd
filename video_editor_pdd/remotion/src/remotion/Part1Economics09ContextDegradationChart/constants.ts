// Part1Economics09ContextDegradationChart constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0A1628";
export const FPS = 30;
export const TOTAL_FRAMES = 900;

// Chart area: (300, 150) to (1620, 850) — 1320px x 700px
export const CHART_X = 300;
export const CHART_Y = 150;
export const CHART_W = 1320;
export const CHART_H = 700;

// Bar layout
export const BAR_WIDTH = 120;
export const BAR_GAP = 60;
export const NUM_BARS = 5;
export const TOTAL_BARS_WIDTH = NUM_BARS * BAR_WIDTH + (NUM_BARS - 1) * BAR_GAP;
export const BARS_START_X = CHART_X + (CHART_W - TOTAL_BARS_WIDTH) / 2;

// Colors
export const AXIS_COLOR = "#94A3B8";
export const AXIS_TITLE_COLOR = "#CBD5E1";
export const GRID_COLOR = "#334155";
export const CALLOUT_COLOR = "#EF4444";
export const CALLOUT_SOURCE_COLOR = "#94A3B8";
export const TREND_LINE_COLOR = "#FFFFFF";

// Bar data
export const BARS = [
  { fillLevel: "10%", capability: 95, color: "#22C55E" },
  { fillLevel: "25%", capability: 82, color: "#84CC16" },
  { fillLevel: "50%", capability: 58, color: "#F59E0B" },
  { fillLevel: "75%", capability: 32, color: "#F97316" },
  { fillLevel: "100%", capability: 15, color: "#EF4444" },
];

// Pre-computed bar x-positions and top-y coordinates
export const BAR_POSITIONS = BARS.map((_, i) => BARS_START_X + i * (BAR_WIDTH + BAR_GAP));
export const BAR_TOPS = BARS.map((bar, i) => ({
  x: BAR_POSITIONS[i] + BAR_WIDTH / 2,
  y: CHART_Y + CHART_H * (1 - bar.capability / 100),
}));

// Y-axis tick values
export const Y_TICKS = [0, 25, 50, 75, 100];

// Animation frames (at 30fps)
export const AXES_FADE_END = 30;
export const BAR_STAGGER_START = 30;
export const BAR_STAGGER_INTERVAL = 20;
export const BAR_GROW_DURATION = 30;
export const TREND_LINE_START = 140;
export const TREND_LINE_END = 180;
export const CALLOUT_START = 180;
export const CALLOUT_END = 210;
export const GLOW_PULSE_START = 210;

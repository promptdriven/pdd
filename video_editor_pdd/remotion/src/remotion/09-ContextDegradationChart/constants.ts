// Part1Economics09ContextDegradationChart constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0A1628";

// Chart region: (300, 150) to (1620, 850)
export const CHART_X = 300;
export const CHART_Y = 150;
export const CHART_W = 1320;
export const CHART_H = 700;

// Bar layout
export const BAR_WIDTH = 120;
export const BAR_GAP = 60;
export const BAR_COUNT = 5;

// Total bar block width: 5*120 + 4*60 = 840
// Center bars within chart: offset = (1320 - 840) / 2 = 240
export const BAR_BLOCK_OFFSET =
  (CHART_W - (BAR_COUNT * BAR_WIDTH + (BAR_COUNT - 1) * BAR_GAP)) / 2;

// Colors
export const AXIS_COLOR = "#94A3B8";
export const AXIS_TITLE_COLOR = "#CBD5E1";
export const GRID_COLOR = "#334155";
export const TREND_LINE_COLOR = "#FFFFFF";
export const CALLOUT_COLOR = "#EF4444";
export const CALLOUT_SOURCE_COLOR = "#94A3B8";

// Bar data
export interface BarData {
  fillLevel: string;
  capability: number;
  color: string;
}

export const BARS: BarData[] = [
  { fillLevel: "10%", capability: 95, color: "#22C55E" },
  { fillLevel: "25%", capability: 82, color: "#84CC16" },
  { fillLevel: "50%", capability: 58, color: "#F59E0B" },
  { fillLevel: "75%", capability: 32, color: "#F97316" },
  { fillLevel: "100%", capability: 15, color: "#EF4444" },
];

// Compute bar X positions (left edge of each bar)
export const BAR_POSITIONS = BARS.map((_, i) => {
  const blockStart = CHART_X + BAR_BLOCK_OFFSET;
  return blockStart + i * (BAR_WIDTH + BAR_GAP);
});

// Compute bar top Y positions (for trend line — using bar center X)
export const BAR_TOPS = BARS.map((bar, i) => ({
  x: BAR_POSITIONS[i] + BAR_WIDTH / 2,
  y: CHART_Y + CHART_H * (1 - bar.capability / 100),
}));

// Y-axis grid fractions
export const Y_GRID_FRACTIONS = [0.25, 0.5, 0.75, 1.0];

// Animation timing (30fps)
export const AXES_FADE_END = 30;

// Bar stagger: each bar starts 20 frames after the previous
export const BAR_STAGGER = 20;
export const BAR_FIRST_START = 30;

// Trend line
export const TREND_LINE_START = 140;
export const TREND_LINE_END = 180;

// Callout
export const CALLOUT_START = 180;
export const CALLOUT_ANIM_DURATION = 30;

// Glow pulse (subtle bar glow after hold)
export const GLOW_PULSE_START = 210;
export const GLOW_PULSE_PERIOD = 60;

export const TOTAL_FRAMES = 900;

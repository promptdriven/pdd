// Part3Mold10RatchetInfographic constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;

// Chart area (from spec)
export const CHART_X = 160;
export const CHART_Y = 200;
export const CHART_W = 1600;
export const CHART_H = 680;

// Timeline position
export const TIMELINE_Y = 780;
export const TIMELINE_X_START = 200;
export const TIMELINE_X_END = 1720;
export const TIMELINE_WIDTH = TIMELINE_X_END - TIMELINE_X_START;

// Bar configuration
export const TOTAL_BARS = 75;
export const BAR_WIDTH = 8;
export const BAR_SPACING = 20;
export const BAR_MIN_HEIGHT = 40;
export const BAR_MAX_HEIGHT = 200;

// Colors
export const TEST_GREEN = "#22C55E";
export const TEST_GREEN_70 = "rgba(34, 197, 94, 0.7)";
export const TEST_GREEN_50_GLOW = "rgba(34, 197, 94, 0.5)";
export const TEST_GREEN_10 = "rgba(34, 197, 94, 0.1)";
export const WHITE = "#FFFFFF";
export const SLATE_400 = "#94A3B8";
export const TIMELINE_COLOR = "rgba(255, 255, 255, 0.3)";
export const BG_COLOR = "#0A1628";

// Line style
export const RATCHET_LINE_WIDTH = 3;

// Animation frames (30fps, 360 total)
export const TOTAL_FRAMES = 360;

// Timeline axis draw-in
export const AXIS_DRAW_START = 0;
export const AXIS_DRAW_END = 15;

// Y-axis label fade
export const YLABEL_FADE_START = 10;
export const YLABEL_FADE_END = 20;

// Bars + ratchet line
export const BARS_START = 15;
export const BARS_END = 180;

// Milestone labels
export const GEN1_FADE_START = 40;
export const GEN1_FADE_END = 55;
export const GEN5_FADE_START = 90;
export const GEN5_FADE_END = 105;
export const GEN20_FADE_START = 160;
export const GEN20_FADE_END = 175;

// Hold + fade out
export const FADEOUT_START = 300;
export const FADEOUT_END = 360;

// Pulse timing (during hold)
export const PULSE_START = 180;
export const PULSE_PERIOD = 60; // frames per cycle

// Generate deterministic bar heights using a seeded approach
function seededRandom(seed: number): number {
  const x = Math.sin(seed * 127.1 + 311.7) * 43758.5453;
  return x - Math.floor(x);
}

export interface BarData {
  index: number;
  x: number;
  height: number;
  cumulativeMax: number;
}

// Pre-compute bar data so ratchet line is monotonically increasing
export const BAR_DATA: BarData[] = (() => {
  const bars: BarData[] = [];
  let cumulativeMax = 0;

  for (let i = 0; i < TOTAL_BARS; i++) {
    const t = i / (TOTAL_BARS - 1);
    const x = TIMELINE_X_START + t * TIMELINE_WIDTH;
    // Heights grow over time with randomness, simulating exponential test growth
    const baseHeight =
      BAR_MIN_HEIGHT + t * (BAR_MAX_HEIGHT - BAR_MIN_HEIGHT) * 0.7;
    const randomFactor = 0.5 + seededRandom(i) * 1.0;
    const height = Math.max(
      BAR_MIN_HEIGHT,
      Math.min(BAR_MAX_HEIGHT, baseHeight * randomFactor + 20)
    );

    // Ratchet line: cumulative max of bar tops (measured from timeline upward)
    cumulativeMax = Math.max(cumulativeMax, height);

    bars.push({ index: i, x, height, cumulativeMax });
  }

  return bars;
})();

// Milestone definitions
export interface Milestone {
  label: string;
  countLabel: string;
  barIndex: number;
  fadeStart: number;
  fadeEnd: number;
}

export const MILESTONES: Milestone[] = [
  {
    label: "Gen 1:",
    countLabel: "3 tests",
    barIndex: 3,
    fadeStart: GEN1_FADE_START,
    fadeEnd: GEN1_FADE_END,
  },
  {
    label: "Gen 5:",
    countLabel: "18 tests",
    barIndex: 18,
    fadeStart: GEN5_FADE_START,
    fadeEnd: GEN5_FADE_END,
  },
  {
    label: "Gen 20:",
    countLabel: "127 tests",
    barIndex: 72,
    fadeStart: GEN20_FADE_START,
    fadeEnd: GEN20_FADE_END,
  },
];

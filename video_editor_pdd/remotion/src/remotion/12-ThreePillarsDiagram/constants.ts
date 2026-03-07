// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;

// Colors
export const BG_COLOR = "#0A1628";
export const GOLD = "#F59E0B";
export const GREEN = "#22C55E";
export const PURPLE = "#A855F7";
export const CONNECTOR_GRAY = "#94A3B8";
export const WHITE = "#FFFFFF";

// Pillar layout — Row 1
export const ROW1_Y = 400;
export const ROW2_Y = 600;

export const PILLAR_WIDTH = 200;
export const PILLAR_HEIGHT = 100;
export const PILLAR_RADIUS = 16;
export const RESULT_WIDTH = 360;
export const RESULT_HEIGHT = 100;

// Horizontal positions (centered in 1920)
// Layout: [Pillar] + [Pillar] + [Pillar] = [Result]
// Total: 200 + 60 + 200 + 60 + 200 + 80 + 360 = 1160
// Start x: (1920 - 1160) / 2 = 380
export const EQUATION_START_X = 380;
export const GAP_CONNECTOR = 60;
export const GAP_EQUALS = 80;

export const PILLAR_1_X = EQUATION_START_X;
export const CONN_1_X = PILLAR_1_X + PILLAR_WIDTH + GAP_CONNECTOR / 2;
export const PILLAR_2_X = PILLAR_1_X + PILLAR_WIDTH + GAP_CONNECTOR;
export const CONN_2_X = PILLAR_2_X + PILLAR_WIDTH + GAP_CONNECTOR / 2;
export const PILLAR_3_X = PILLAR_2_X + PILLAR_WIDTH + GAP_CONNECTOR;
export const EQUALS_X = PILLAR_3_X + PILLAR_WIDTH + GAP_EQUALS / 2;
export const RESULT_X = PILLAR_3_X + PILLAR_WIDTH + GAP_EQUALS;

// Animation timing (frames at 30fps)
export const PILLAR1_IN_START = 0;
export const PILLAR1_IN_END = 20;

export const CONN1_FADE_START = 15;
export const CONN1_FADE_END = 25;

export const PILLAR2_IN_START = 20;
export const PILLAR2_IN_END = 40;

export const CONN2_FADE_START = 35;
export const CONN2_FADE_END = 45;

export const PILLAR3_IN_START = 40;
export const PILLAR3_IN_END = 60;

export const EQUALS_FADE_START = 55;
export const EQUALS_FADE_END = 70;

export const RESULT_FADE_START = 65;
export const RESULT_FADE_END = 85;

export const ROW2_START = 85;
export const ROW2_STAGGER = 5;

export const ARROWS_FADE_START = 115;
export const ARROWS_FADE_END = 130;

export const PULSE_START = 130;
export const PULSE_MID = 138;
export const PULSE_END = 145;

export const FADE_OUT_START = 250;
export const FADE_OUT_END = 300;

export const TOTAL_FRAMES = 300;

// Pillar data
export interface PillarData {
  label: string;
  color: string;
  icon: "document" | "checkmark" | "loop";
  x: number;
  inStart: number;
  inEnd: number;
  row2Label: string;
}

export const PILLARS: PillarData[] = [
  {
    label: "Prompt",
    color: GOLD,
    icon: "document",
    x: PILLAR_1_X,
    inStart: PILLAR1_IN_START,
    inEnd: PILLAR1_IN_END,
    row2Label: "Intent",
  },
  {
    label: "Tests",
    color: GREEN,
    icon: "checkmark",
    x: PILLAR_2_X,
    inStart: PILLAR2_IN_START,
    inEnd: PILLAR2_IN_END,
    row2Label: "Constraints",
  },
  {
    label: "Grounding",
    color: PURPLE,
    icon: "loop",
    x: PILLAR_3_X,
    inStart: PILLAR3_IN_START,
    inEnd: PILLAR3_IN_END,
    row2Label: "Style",
  },
];

// Row 2 items (for sequential fade-in)
export interface Row2Item {
  text: string;
  color: string;
}

export const ROW2_ITEMS: Row2Item[] = [
  { text: "Intent", color: GOLD },
  { text: "+", color: CONNECTOR_GRAY },
  { text: "Constraints", color: GREEN },
  { text: "+", color: CONNECTOR_GRAY },
  { text: "Style", color: PURPLE },
  { text: "=", color: WHITE },
  { text: "The Mold", color: WHITE },
];

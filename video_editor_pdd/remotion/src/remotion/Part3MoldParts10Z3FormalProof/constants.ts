// ─── Colors ───
export const BG_COLOR = '#0A0F1A';
export const PANEL_BG = '#0F172A';
export const PANEL_BORDER = '#334155';
export const TEXT_PRIMARY = '#CDD6F4';
export const TEXT_EMPHASIS = '#E2E8F0';
export const PURPLE_ACCENT = '#A78BFA';
export const PURPLE_DEEP = '#7C3AED';
export const MOLD_BLUE = '#4A90D9';

// ─── Canvas ───
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// ─── Annotation Panel Geometry ───
export const PANEL_X = 1000;
export const PANEL_Y = 200;
export const PANEL_WIDTH = 840;
export const PANEL_HEIGHT = 580;
export const PANEL_RADIUS = 12;
export const PANEL_PADDING = 32;

// ─── Badge Dimensions ───
export const BADGE_SIZE = 48;
export const BADGE_RADIUS = 8;
export const BADGE_GAP = 24;

// ─── Animation Frame Markers ───
export const TOTAL_FRAMES = 780;
export const PANEL_SLIDE_IN_END = 30;
export const TEXT_TYPE_START = 30;
export const TEXT_TYPE_END = 90;
export const EMPHASIS_START = 90;
export const EMPHASIS_END = 110;
export const ITALIC_START = 150;
export const ITALIC_END = 170;
export const LOGOS_START = 210;
export const LOGOS_END = 230;
export const CONNECTORS_START = 270;
export const CONNECTORS_END = 300;
export const WALL_TRANSITION_START = 270;
export const WALL_TRANSITION_END = 360;
export const HOLD_START = 360;
export const HOLD_END = 720;
export const PANEL_SLIDE_OUT_START = 720;
export const PANEL_SLIDE_OUT_END = 750;

// ─── Annotation Text ───
export const MAIN_TEXT_WORDS = [
  { text: 'PDD', highlight: false },
  { text: 'also', highlight: false },
  { text: 'uses', highlight: false },
  { text: 'Z3', highlight: true },
  { text: '—', highlight: false },
  { text: 'the', highlight: false },
  { text: 'same', highlight: false },
  { text: 'class', highlight: false },
  { text: 'of', highlight: false },
  { text: 'SMT', highlight: true },
  { text: 'solver', highlight: true },
  { text: 'used', highlight: false },
  { text: 'in', highlight: false },
  { text: 'chip', highlight: false },
  { text: 'verification', highlight: false },
  { text: '—', highlight: false },
  { text: 'to', highlight: false },
  { text: 'formally', highlight: true },
  { text: 'prove', highlight: true },
  { text: 'properties', highlight: false },
  { text: 'hold', highlight: false },
  { text: 'for', highlight: false },
  { text: 'every', highlight: false },
  { text: 'possible', highlight: false },
  { text: 'input.', highlight: false },
];

export const EMPHASIS_TEXT = 'Same math as billion-dollar tapeouts.';
export const ITALIC_TEXT = 'Not sampling. Mathematical proof.';

// ─── Mold Wall Definitions (simplified cross-section) ───
export interface MoldWall {
  x1: number;
  y1: number;
  x2: number;
  y2: number;
  proven: boolean;
}

export const MOLD_WALLS: MoldWall[] = [
  { x1: 120, y1: 200, x2: 120, y2: 600, proven: false },
  { x1: 120, y1: 600, x2: 500, y2: 600, proven: true },
  { x1: 500, y1: 200, x2: 500, y2: 600, proven: false },
  { x1: 120, y1: 200, x2: 500, y2: 200, proven: true },
  { x1: 250, y1: 350, x2: 250, y2: 550, proven: false },
  { x1: 370, y1: 300, x2: 370, y2: 500, proven: false },
];

// ─── Connector Line Endpoints ───
export const CONNECTOR_ORIGINS = { x: 1000, y: 490 };
export const PROVEN_WALL_TARGETS = [
  { x: 310, y: 600 }, // bottom wall midpoint
  { x: 310, y: 200 }, // top wall midpoint
];

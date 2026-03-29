// ─── Canvas ───
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const DURATION_FRAMES = 870;
export const FPS = 30;

// ─── Background & Grid ───
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.05;
export const GRID_SPACING = 60;

// ─── Mold ───
export const MOLD_STROKE = '#334155';
export const MOLD_STROKE_WIDTH = 3;
export const NOZZLE_COLOR = '#D9944A';
export const NOZZLE_OPACITY = 0.2;

// ─── Wall Colors ───
export const WALL_GLOW_COLOR = '#4A90D9';
export const WALL_BASE_OPACITY = 0.4;
export const WALL_PEAK_OPACITY = 0.7;

// ─── Liquid ───
export const LIQUID_LEADING_EDGE = '#FFFFFF';
export const LIQUID_LEADING_OPACITY = 0.9;
export const LIQUID_GRADIENT_FROM = '#38BDF8';
export const LIQUID_GRADIENT_TO = '#0D9488';
export const LIQUID_BLUR = 4;

// ─── Ripple ───
export const RIPPLE_COLOR = '#4A90D9';
export const RIPPLE_OPACITY = 0.2;
export const RIPPLE_FRAMES = 10;

// ─── Annotation Colors ───
export const ANNOTATION_RED = '#F87171';
export const ANNOTATION_GREEN = '#4ADE80';
export const ANNOTATION_SOURCE_COLOR = '#94A3B8';

// ─── Typography ───
export const FONT_MAIN = 'Inter, sans-serif';
export const FONT_MONO = 'JetBrains Mono, monospace';

// ─── Mold Geometry (centered on canvas) ───
export const MOLD_LEFT = 180;
export const MOLD_TOP = 140;
export const MOLD_WIDTH = 900;
export const MOLD_HEIGHT = 700;

// Nozzle position (top center of mold)
export const NOZZLE_X = MOLD_LEFT + MOLD_WIDTH / 2;
export const NOZZLE_Y = MOLD_TOP - 20;
export const NOZZLE_WIDTH = 60;
export const NOZZLE_HEIGHT = 50;

// ─── Wall definitions ───
export interface WallDef {
  id: string;
  label: string;
  x: number;
  y: number;
  width: number;
  height: number;
  hitFrame: number; // frame when liquid reaches this wall
  isFocusWall: boolean;
}

export const WALLS: WallDef[] = [
  {
    id: 'type-check',
    label: 'type: str → int',
    x: MOLD_LEFT + 120,
    y: MOLD_TOP + 200,
    width: 180,
    height: 8,
    hitFrame: 60,
    isFocusWall: false,
  },
  {
    id: 'bounds-check',
    label: 'assert len > 0',
    x: MOLD_LEFT + 500,
    y: MOLD_TOP + 300,
    width: 8,
    height: 140,
    hitFrame: 100,
    isFocusWall: false,
  },
  {
    id: 'null-none',
    label: 'null → None',
    x: MOLD_LEFT + 280,
    y: MOLD_TOP + 420,
    width: 200,
    height: 8,
    hitFrame: 150,
    isFocusWall: true,
  },
  {
    id: 'edge-case',
    label: 'edge: empty []',
    x: MOLD_LEFT + 650,
    y: MOLD_TOP + 500,
    width: 8,
    height: 120,
    hitFrame: 210,
    isFocusWall: false,
  },
];

// Focus wall (null → None)
export const FOCUS_WALL = WALLS.find((w) => w.isFocusWall)!;

// ─── Liquid path waypoints (from nozzle down through cavity) ───
export const LIQUID_PATH_POINTS: Array<{ x: number; y: number; frame: number }> = [
  { x: NOZZLE_X, y: NOZZLE_Y + NOZZLE_HEIGHT, frame: 0 },
  { x: NOZZLE_X, y: MOLD_TOP + 80, frame: 15 },
  { x: MOLD_LEFT + 200, y: MOLD_TOP + 190, frame: 50 },
  { x: MOLD_LEFT + 210, y: MOLD_TOP + 200, frame: 60 }, // hits wall 1
  { x: MOLD_LEFT + 400, y: MOLD_TOP + 280, frame: 85 },
  { x: MOLD_LEFT + 500, y: MOLD_TOP + 310, frame: 100 }, // hits wall 2
  { x: MOLD_LEFT + 380, y: MOLD_TOP + 410, frame: 140 },
  { x: MOLD_LEFT + 380, y: MOLD_TOP + 420, frame: 150 }, // hits wall 3 (focus)
  { x: MOLD_LEFT + 550, y: MOLD_TOP + 470, frame: 180 },
  { x: MOLD_LEFT + 650, y: MOLD_TOP + 510, frame: 210 }, // hits wall 4
  { x: MOLD_LEFT + 500, y: MOLD_TOP + 580, frame: 250 },
  { x: MOLD_LEFT + 350, y: MOLD_TOP + 620, frame: 270 }, // fully filled
];

// ─── Animation Keyframes ───
export const FRAME_LIQUID_START = 0;
export const FRAME_FIRST_WALL_HIT = 60;
export const FRAME_SECOND_WALL_HIT = 100;
export const FRAME_FOCUS_ZOOM_START = 180;
export const FRAME_FOCUS_ZOOM_END = 210;
export const FRAME_ZOOM_OUT_START = 270;
export const FRAME_ZOOM_OUT_END = 300;
export const FRAME_ANNOTATION1_IN = 330;
export const FRAME_ANNOTATION2_IN = 510;
export const FRAME_WALL_GLOW_START = 510;
export const FRAME_WALL_GLOW_END = 570;

// ─── Annotation data ───
export const ANNOTATIONS = [
  {
    text: 'AI code: 1.7× more issues',
    source: '(CodeRabbit, 2025)',
    color: ANNOTATION_RED,
    frameIn: 330,
    posX: 1250,
    posY: 340,
  },
  {
    text: 'AI + strong tests = amplified delivery',
    source: '(DORA, 2025)',
    color: ANNOTATION_GREEN,
    frameIn: 510,
    posX: 1250,
    posY: 440,
  },
];

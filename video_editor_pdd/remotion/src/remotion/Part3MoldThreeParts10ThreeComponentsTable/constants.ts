// ─── Colors ───
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.03;

export const AMBER = '#D9944A';
export const BLUE = '#4A90D9';
export const GREEN = '#5AAA6E';

export const TEXT_PRIMARY = '#E2E8F0';
export const TEXT_SECONDARY = '#94A3B8';
export const TABLE_BG = '#1E293B';
export const TABLE_HEADER_BG = '#0F172A';
export const DIVIDER_COLOR = '#334155';

// ─── Dimensions ───
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const GRID_SPACING = 40;
export const FPS = 30;
export const DURATION_FRAMES = 480;

// ─── Table Layout ───
export const TABLE_X = 650;
export const TABLE_Y = 250;
export const TABLE_WIDTH = 1100;
export const TABLE_ROW_HEIGHT = 80;
export const COL_WIDTHS = [300, 350, 250];
export const TABLE_BORDER_RADIUS = 12;

// ─── Table Data ───
export const TABLE_ROWS = [
  {
    component: 'Prompt',
    encodes: 'WHAT (intent)',
    owner: 'Developer',
    color: BLUE,
    accentWidth: 3,
    componentWeight: 600 as const,
    encodesWeight: 400 as const,
    emphasized: false,
  },
  {
    component: 'Grounding',
    encodes: 'HOW (style)',
    owner: 'Automatic',
    color: GREEN,
    accentWidth: 3,
    componentWeight: 600 as const,
    encodesWeight: 400 as const,
    emphasized: false,
  },
  {
    component: 'Tests',
    encodes: 'CORRECTNESS',
    owner: 'Accumulated',
    color: AMBER,
    accentWidth: 4,
    componentWeight: 700 as const,
    encodesWeight: 700 as const,
    emphasized: true,
  },
] as const;

// ─── Code Snippet ───
export const CODE_SNIPPET = `function processOrder(order: Order): Result {
  const validated = schema.parse(order);
  return pipeline.execute(validated);
}`;

// ─── Animation Timing ───
export const TIMING = {
  // Phase 1: Full mold with flow
  MOLD_FULL_START: 0,
  MOLD_FULL_END: 60,
  // Phase 2: Mold slides left, table fades in
  MOLD_SLIDE_START: 60,
  MOLD_SLIDE_END: 100,
  // Phase 3: Table header
  TABLE_HEADER_START: 120,
  TABLE_HEADER_END: 150,
  // Phase 4-6: Table rows
  ROW1_START: 180,
  ROW2_START: 220,
  ROW3_START: 260,
  ROW_DURATION: 20,
  ROW3_DURATION: 25,
  // Phase 7: Conflict line
  CONFLICT_START: 310,
  CONFLICT_DURATION: 20,
  UNDERLINE_DURATION: 15,
  // Phase 8: Code output
  CODE_START: 370,
  // Phase 9: Code glow fade
  CODE_GLOW_FADE_START: 420,
  CODE_GLOW_FADE_DURATION: 30,
  CODE_DIM_DURATION: 20,
  // Phase 10: Final caption
  CAPTION_START: 450,
  CAPTION_DURATION: 15,
} as const;

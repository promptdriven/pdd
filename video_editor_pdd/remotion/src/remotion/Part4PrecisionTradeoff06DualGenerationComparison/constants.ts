// === Colors ===
export const BG_COLOR = "#0A0F1A";
export const AMBER_ACCENT = "#D9944A";
export const BLUE_ACCENT = "#4A90D9";
export const CODE_BG = "#1E293B";
export const GLOW_GREEN = "#5AAA6E";
export const ARROW_COLOR = "#64748B";
export const CODE_TEXT_COLOR = "#CBD5E1";
export const LABEL_MUTED = "#94A3B8";

// === Layout ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const CENTER_GAP = 40;

// Left column
export const LEFT_COL_X = 80;
export const LEFT_PROMPT_X = 240;
export const LEFT_PROMPT_Y = 100;
export const LEFT_PROMPT_W = 320;
export const LEFT_PROMPT_H = 180;
export const LEFT_CODE_X = 240;
export const LEFT_CODE_Y = 380;

// Right column
export const RIGHT_COL_X = 1040;
export const RIGHT_PROMPT_X = 1360;
export const RIGHT_PROMPT_Y = 130;
export const RIGHT_PROMPT_W = 200;
export const RIGHT_PROMPT_H = 120;
export const RIGHT_CODE_X = 1300;
export const RIGHT_CODE_Y = 380;

// Code blocks
export const CODE_BLOCK_W = 320;
export const CODE_BLOCK_H = 260;

// Arrows
export const LEFT_ARROW_X = 400;
export const LEFT_ARROW_START_Y = 300;
export const LEFT_ARROW_END_Y = 360;
export const RIGHT_ARROW_X = 1460;
export const RIGHT_ARROW_START_Y = 270;
export const RIGHT_ARROW_END_Y = 360;

// Labels
export const LEFT_LABEL_X = 400;
export const RIGHT_LABEL_X = 1460;
export const LABEL_Y = 670;

// Comparison bar
export const BAR_Y = 950;
export const BAR_WIDTH = 800;
export const BAR_CENTER_X = 960;
export const BAR_LEFT_WIDTH = 500;
export const BAR_RIGHT_WIDTH = 100;

// Test indicators
export const TEST_DOT_SIZE = 5;
export const TEST_COUNT = 47;

// === Animation Frames ===
export const TOTAL_FRAMES = 240;

// Phase 1: Prompts appear (0-45)
export const PROMPT_APPEAR_START = 0;
export const PROMPT_APPEAR_END = 45;
export const PROMPT_FADE_DURATION = 30;

// Phase 2: Arrows draw (45-90)
export const ARROW_DRAW_START = 45;
export const ARROW_DRAW_END = 90;
export const ARROW_DRAW_DURATION = 20;

// Phase 3: Code blocks generate (90-150)
export const CODE_GEN_START = 90;
export const CODE_GEN_END = 150;
export const CODE_LINE_RATE = 4; // 1 line per 4 frames
export const GLOW_DURATION = 15;

// Phase 4: Labels appear (150-195)
export const LABELS_START = 150;
export const LABELS_END = 195;
export const LABELS_FADE_DURATION = 20;

// Phase 5: Comparison bar (195-210)
export const BAR_START = 195;
export const BAR_ANIM_DURATION = 20;

// Phase 6: Hold + Fade out (210-240)
export const FADE_OUT_START = 210;
export const FADE_OUT_DURATION = 30;

// === Generated code lines (shared between both blocks) ===
export const GENERATED_CODE_LINES = [
  "export function generateWidget(config) {",
  "  const { type, props, children } = config;",
  "  const validated = validateConfig(config);",
  "  if (!validated.ok) {",
  "    throw new ConfigError(validated.errors);",
  "  }",
  "",
  "  const widget = createElement(type, {",
  "    ...defaultProps[type],",
  "    ...props,",
  "    id: generateId(),",
  "  });",
  "",
  "  if (children?.length) {",
  "    widget.children = children.map(c =>",
  "      generateWidget(c)",
  "    );",
  "  }",
  "",
  "  return applyTheme(widget, config.theme);",
  "}",
];

// ── Canvas ────────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 150; // 5s at 30fps

// ── Background ────────────────────────────────────────────────────────
export const BG_COLOR = "#0D1117";

// ── Code Underlay ─────────────────────────────────────────────────────
export const CODE_UNDERLAY_OPACITY_START = 0.08;
export const CODE_UNDERLAY_OPACITY_END = 0.04;
export const CODE_DIM_END_FRAME = 20;
export const CODE_FONT_FAMILY = "'JetBrains Mono', monospace";
export const CODE_FONT_SIZE = 14;
export const CODE_COLOR = "#E2E8F0";

// ── Question Fade-Out ─────────────────────────────────────────────────
export const QUESTION_TEXT = "So why are we still patching?";
export const QUESTION_FONT_SIZE = 42;
export const QUESTION_FONT_WEIGHT = 300;
export const QUESTION_COLOR = "#E2E8F0";
export const QUESTION_Y = 540;
export const QUESTION_FADE_END_FRAME = 15; // easeIn(quad) over 15 frames

// ── Title ─────────────────────────────────────────────────────────────
export const TITLE_COLOR = "#4A90D9";
export const TITLE_OPACITY = 0.95;
export const TITLE_FONT_SIZE = 64;
export const TITLE_FONT_WEIGHT = 700;
export const TITLE_FONT_FAMILY = "'Inter', sans-serif";

export const TITLE_LINE1_TEXT = "Prompt-Driven";
export const TITLE_LINE1_Y = 480;
export const TITLE_LINE1_START_FRAME = 20;
export const TITLE_LINE1_ANIM_DURATION = 25; // frames

export const TITLE_LINE2_TEXT = "Development";
export const TITLE_LINE2_Y = 555;
export const TITLE_LINE2_START_FRAME = 60;
export const TITLE_LINE2_ANIM_DURATION = 25; // frames

export const TITLE_SLIDE_DISTANCE = 10; // px upward

// ── Glow ──────────────────────────────────────────────────────────────
export const GLOW_BLUR = 12;
export const GLOW_COLOR = "#4A90D9";
export const GLOW_OPACITY_MIN = 0.08;
export const GLOW_OPACITY_MAX = 0.12;
export const GLOW_PULSE_START = 100;
export const GLOW_PULSE_CYCLE = 50; // frames per cycle

// ── Horizontal Rule ───────────────────────────────────────────────────
export const RULE_Y = 590;
export const RULE_WIDTH = 160;
export const RULE_HEIGHT = 2;
export const RULE_COLOR = "#4A90D9";
export const RULE_OPACITY = 0.2;
export const RULE_START_FRAME = 50;
export const RULE_DRAW_DURATION = 10; // frames
export const RULE_CENTER_X = 960; // canvas center

// ── Subtitle ──────────────────────────────────────────────────────────
export const SUBTITLE_TEXT = "Writing the mold, not the plastic.";
export const SUBTITLE_FONT_SIZE = 18;
export const SUBTITLE_FONT_WEIGHT = 300;
export const SUBTITLE_COLOR = "#94A3B8";
export const SUBTITLE_OPACITY = 0.5;
export const SUBTITLE_Y = 620;
export const SUBTITLE_START_FRAME = 80;
export const SUBTITLE_FADE_DURATION = 20; // frames

// ── Terminal Breadcrumb ───────────────────────────────────────────────
export const TERMINAL_TEXT = "pdd generate";
export const TERMINAL_FONT_SIZE = 10;
export const TERMINAL_COLOR = "#4A90D9";
export const TERMINAL_OPACITY = 0.15;
export const TERMINAL_X = 1800;
export const TERMINAL_Y = 1040;
export const TERMINAL_START_FRAME = 80;
export const TERMINAL_FADE_DURATION = 20; // frames

// ── Code Lines (dimmed underlay) ──────────────────────────────────────
export const CODE_LINES = [
  'export function generateModule(spec: ModuleSpec) {',
  '  const config = loadConfig(spec.configPath);',
  '  const template = resolveTemplate(config.type);',
  '',
  '  const context = buildContext({',
  '    spec,',
  '    config,',
  '    dependencies: resolveDeps(spec.imports),',
  '  });',
  '',
  '  const output = template.render(context);',
  '  const formatted = applyFormatting(output, config.style);',
  '',
  '  writeModule(spec.outputPath, formatted);',
  '  updateManifest(spec.name, spec.outputPath);',
  '',
  '  return {',
  '    path: spec.outputPath,',
  '    checksum: computeHash(formatted),',
  '    generatedAt: Date.now(),',
  '  };',
  '}',
  '',
  'export function validateSpec(spec: ModuleSpec): Result {',
  '  const errors = checkSchema(spec, MODULE_SCHEMA);',
  '  if (errors.length > 0) {',
  '    return { ok: false, errors };',
  '  }',
  '  return { ok: true, errors: [] };',
  '}',
];

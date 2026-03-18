// ColdOpen06StillPatchingBeat – constants

export const DURATION_FRAMES = 150;
export const FPS = 30;

// Background
export const BG_COLOR = '#0D1117';

// Code underlay
export const CODE_UNDERLAY_TARGET_OPACITY = 0.08;
export const CODE_DIM_START = 0;
export const CODE_DIM_END = 30;

// Question text
export const TEXT_FADE_START = 30;
export const TEXT_FADE_END = 60; // 30-frame fade
export const TEXT_COLOR = '#E2E8F0';
export const TEXT_OPACITY = 0.9;
export const ACCENT_COLOR = '#D9944A';
export const ACCENT_OPACITY = 0.9;
export const TEXT_SIZE = 42;
export const TEXT_WEIGHT = 300;
export const LETTER_SPACING = 1;

// Accent line
export const LINE_DRAW_START = 75;
export const LINE_DRAW_END = 90; // 15-frame draw
export const LINE_COLOR = '#334155';
export const LINE_OPACITY = 0.3;
export const LINE_WIDTH_PX = 120;
export const LINE_Y = 580;

// Code lines — representative clean code block from previous shot
export const CODE_LINES = [
  'async function regenerateModule(spec: ModuleSpec) {',
  '  const context = await gatherContext(spec);',
  '  const prompt = buildPrompt(context, spec);',
  '',
  '  const result = await llm.generate({',
  '    model: "claude-sonnet-4-5-20250929",',
  '    prompt,',
  '    temperature: 0.2,',
  '  });',
  '',
  '  const code = extractCode(result);',
  '  await validate(code, spec.constraints);',
  '  await writeModule(spec.path, code);',
  '  return code;',
  '}',
];

// Code styling
export const CODE_FONT_SIZE = 14;
export const CODE_LINE_HEIGHT = 22;
export const CODE_X_OFFSET = 440;
export const CODE_Y_OFFSET = 240;
export const CODE_COLORS: Record<string, string> = {
  keyword: '#FF7B72',
  function: '#D2A8FF',
  string: '#A5D6FF',
  property: '#79C0FF',
  comment: '#8B949E',
  default: '#C9D1D9',
  punctuation: '#C9D1D9',
};

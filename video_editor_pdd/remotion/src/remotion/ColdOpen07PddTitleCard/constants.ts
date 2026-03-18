// ColdOpen07PddTitleCard – constants
// PDD Title Card: "Prompt-Driven Development" with subtitle

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
  FPS: 30,
  DURATION_FRAMES: 150,
} as const;

export const COLORS = {
  BACKGROUND: '#0D1117',
  TITLE: '#4A90D9',
  SUBTITLE: '#94A3B8',
  QUESTION_TEXT: '#E2E8F0',
} as const;

export const TITLE = {
  LINE1: 'Prompt-Driven',
  LINE2: 'Development',
  FONT_SIZE: 64,
  FONT_WEIGHT: 700,
  FONT_FAMILY: 'Inter, sans-serif',
  OPACITY: 0.95,
  Y_LINE1: 480,
  Y_LINE2: 555,
} as const;

export const SUBTITLE = {
  TEXT: 'Writing the mold, not the plastic.',
  FONT_SIZE: 18,
  FONT_WEIGHT: 300,
  FONT_FAMILY: 'Inter, sans-serif',
  OPACITY: 0.5,
  Y: 620,
} as const;

export const RULE = {
  WIDTH: 160,
  HEIGHT: 2,
  Y: 590,
  OPACITY: 0.2,
} as const;

export const TERMINAL = {
  TEXT: 'pdd generate',
  FONT_SIZE: 10,
  FONT_FAMILY: 'JetBrains Mono, monospace',
  OPACITY: 0.15,
  X: 1800,
  Y: 1040,
} as const;

export const GLOW = {
  BLUR: 12,
  OPACITY_MIN: 0.08,
  OPACITY_MAX: 0.12,
  PULSE_CYCLE: 50, // frames per full pulse cycle
} as const;

export const QUESTION = {
  TEXT: 'So why are we still patching?',
  FONT_SIZE: 42,
  FONT_WEIGHT: 300,
  FONT_FAMILY: 'Inter, sans-serif',
  Y: 540,
} as const;

export const CODE_UNDERLAY_OPACITY_START = 0.08;
export const CODE_UNDERLAY_OPACITY_END = 0.04;

// Animation frame ranges
export const TIMING = {
  // Phase 1: Question fades out, code dims
  QUESTION_FADE_START: 0,
  QUESTION_FADE_END: 20,
  QUESTION_FADE_DURATION: 15, // actual fade is 15 frames

  // Phase 2: "Prompt-Driven" appears
  TITLE_LINE1_START: 20,
  TITLE_LINE1_DURATION: 25,
  TITLE_SLIDE_DISTANCE: 10,

  // Phase 3: Horizontal rule draws
  RULE_START: 50,
  RULE_DURATION: 10,

  // Phase 4: "Development" appears
  TITLE_LINE2_START: 60,
  TITLE_LINE2_DURATION: 25,

  // Phase 5: Subtitle and terminal
  SUBTITLE_START: 80,
  SUBTITLE_DURATION: 20,
  TERMINAL_START: 80,
  TERMINAL_DURATION: 20,

  // Phase 6: Hold with glow pulse
  HOLD_START: 100,
} as const;

// Sample code lines for the dimmed underlay
export const CODE_LINES = [
  'export async function generateComponent(prompt: string) {',
  '  const schema = await parsePromptSchema(prompt);',
  '  const ast = buildComponentAST(schema);',
  '  const validated = runTypeCheck(ast);',
  '',
  '  if (!validated.success) {',
  '    return regenerate(schema, validated.errors);',
  '  }',
  '',
  '  const output = renderToSource(validated.ast);',
  '  await writeOutput(output, schema.outputPath);',
  '  return { success: true, path: schema.outputPath };',
  '}',
  '',
  'function parsePromptSchema(prompt: string): Schema {',
  '  const tokens = tokenize(prompt);',
  '  const structure = extractStructure(tokens);',
  '  return validateSchema(structure);',
  '}',
  '',
  'function buildComponentAST(schema: Schema): AST {',
  '  const imports = resolveImports(schema.dependencies);',
  '  const props = generatePropsInterface(schema.inputs);',
  '  const body = compileLogic(schema.behavior);',
  '  return assembleAST({ imports, props, body });',
  '}',
] as const;

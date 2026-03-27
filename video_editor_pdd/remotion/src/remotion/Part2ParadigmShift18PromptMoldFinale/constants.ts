// Part2ParadigmShift18PromptMoldFinale - Constants
// Colors, dimensions, code snippets, and timing

// ─── Colors ───────────────────────────────────────────
export const BG_COLOR = '#0A0F1A';
export const PROMPT_COLOR = '#D9944A';
export const CODE_TEXT_COLOR = '#E2E8F0';
export const TEST_WALL_COLOR = '#5AAA6E';

// ─── Dimensions ───────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// Prompt document
export const PROMPT_X = 960;
export const PROMPT_Y = 100;
export const PROMPT_WIDTH = 300;
export const PROMPT_HEIGHT = 80;

// Code cavity (mold)
export const CAVITY_X = 660;
export const CAVITY_Y = 200;
export const CAVITY_WIDTH = 600;
export const CAVITY_HEIGHT = 400;

// ─── Timing (frames) ─────────────────────────────────
export const FPS = 30;
export const TOTAL_FRAMES = 360;

export const PROMPT_FADE_IN_END = 30;
export const PROMPT_PULSE_CYCLE = 45;

export const WALLS_START = 45;
export const WALL_DRAW_DURATION = 20;

export const CODE_FLOW_START = 90;
export const CODE_FILL_DURATION = 60; // frames 90-150
export const REGEN_INTERVAL = 90;     // every 90 frames
export const DISSOLVE_DURATION = 15;
export const REFILL_DURATION = 20;
export const WALL_FLASH_DURATION = 10;

export const FADE_OUT_START = 300;
export const FADE_OUT_DURATION = 60;

// ─── Code snippets (3 generations) ────────────────────
export const CODE_GENERATIONS: string[][] = [
  [
    'function processInput(data: Input) {',
    '  const validated = schema.parse(data);',
    '  const result = transform(validated);',
    '  return normalize(result);',
    '}',
    '',
    'function transform(input: Validated) {',
    '  const mapped = input.fields.map(f =>',
    '    applyRule(f, config.rules)',
    '  );',
    '  return { ...input, fields: mapped };',
    '}',
    '',
    'export function normalize(data: any) {',
    '  return Object.keys(data).reduce(',
    '    (acc, key) => ({',
    '      ...acc, [key]: clean(data[key])',
    '    }), {}',
    '  );',
    '}',
  ],
  [
    'const handleRequest = async (req: Req) => {',
    '  const body = await parseBody(req);',
    '  validate(body, RequestSchema);',
    '  const output = compute(body);',
    '  return formatResponse(output);',
    '};',
    '',
    'function compute(payload: Body) {',
    '  const steps = payload.items.map(item =>',
    '    process(item, getConfig())',
    '  );',
    '  return { ...payload, items: steps };',
    '}',
    '',
    'export const formatResponse = (raw: any) => {',
    '  return Object.entries(raw).reduce(',
    '    (out, [k, v]) => ({',
    '      ...out, [k]: sanitize(v)',
    '    }), {}',
    '  );',
    '};',
  ],
  [
    'export default function run(input: Src) {',
    '  const checked = verify(input);',
    '  const transformed = apply(checked);',
    '  return serialize(transformed);',
    '}',
    '',
    'function apply(valid: Checked): Result {',
    '  const processed = valid.entries.map(e =>',
    '    execute(e, loadRules())',
    '  );',
    '  return { ...valid, entries: processed };',
    '}',
    '',
    'export function serialize(data: Result) {',
    '  return Object.keys(data).reduce(',
    '    (memo, prop) => ({',
    '      ...memo, [prop]: encode(data[prop])',
    '    }), {}',
    '  );',
    '}',
  ],
];

// Wall labels positioned around the cavity: top, right, bottom, left
export const WALL_LABELS = ['assert', 'expect', 'verify', 'test'] as const;

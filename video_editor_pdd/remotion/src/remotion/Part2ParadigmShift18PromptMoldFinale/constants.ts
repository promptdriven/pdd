// === Colors ===
export const BG_COLOR = "#0A0F1A";
export const PROMPT_COLOR = "#D9944A";
export const CODE_TEXT_COLOR = "#E2E8F0";
export const WALL_COLOR = "#5AAA6E";

// === Dimensions ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

export const PROMPT_X = 810; // centered: (1920 - 300) / 2
export const PROMPT_Y = 100;
export const PROMPT_WIDTH = 300;
export const PROMPT_HEIGHT = 80;

export const CAVITY_X = 660;
export const CAVITY_Y = 220;
export const CAVITY_WIDTH = 600;
export const CAVITY_HEIGHT = 400;

export const WALL_THICKNESS = 3;

// === Timing (frames) ===
export const TOTAL_FRAMES = 360;
export const PROMPT_FADE_DURATION = 30;
export const PULSE_CYCLE = 45;
export const WALLS_START = 45;
export const WALL_DRAW_DURATION = 20;
export const CODE_FLOW_START = 90;
export const REGEN_INTERVAL = 90;
export const DISSOLVE_DURATION = 15;
export const FILL_DURATION = 30;
export const WALL_FLASH_DURATION = 10;
export const FADE_OUT_START = 300;
export const FADE_OUT_DURATION = 60;

// === Wall Labels ===
export const WALL_LABELS: readonly string[] = ["assert", "expect", "verify", "test"];

// === Code Generation Sets ===
export const CODE_GENERATIONS: readonly string[][] = [
  [
    "function validate(input) {",
    "  const schema = z.object({",
    "    name: z.string().min(1),",
    "    age: z.number().int(),",
    "    email: z.string().email(),",
    "  });",
    "  return schema.parse(input);",
    "}",
    "",
    "export { validate };",
  ],
  [
    "const validateUser = (data) => {",
    "  if (!data.name?.trim()) {",
    "    throw new Error('invalid');",
    "  }",
    "  if (typeof data.age !== 'number')",
    "    return null;",
    "  const re = /^[^@]+@[^@]+$/;",
    "  if (!re.test(data.email))",
    "    throw new Error('bad email');",
    "  return { ...data };",
    "};",
  ],
  [
    "class Validator {",
    "  #rules = new Map();",
    "",
    "  check(input) {",
    "    for (const [k, fn] of this.#rules)",
    "      if (!fn(input[k]))",
    "        return { ok: false, field: k };",
    "    return { ok: true, data: input };",
    "  }",
    "}",
  ],
];

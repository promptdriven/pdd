import { z } from "zod";

// Video specs
export const MOLD_TO_PROMPT_FPS = 30;
export const MOLD_TO_PROMPT_DURATION_SECONDS = 20;
export const MOLD_TO_PROMPT_DURATION_FRAMES =
  MOLD_TO_PROMPT_FPS * MOLD_TO_PROMPT_DURATION_SECONDS;
export const MOLD_TO_PROMPT_WIDTH = 1920;
export const MOLD_TO_PROMPT_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Frame 0-90:    Setup — mold visible left-center, plastic part below
// Frame 90-240:  Primary morph — mold flattens to document, part stretches to code lines
// Frame 240-360: Labels — "PROMPT" title fades in, code becomes readable, blue glow
// Frame 360-480: Relationship — downward arrow/flow from prompt to code
// Frame 480-600: Hold — final state, prompt glowing blue, code present but not glowing
export const BEATS = {
  SETUP_START: 0,
  SETUP_END: 90,
  MORPH_START: 90,
  MORPH_END: 240,
  LABELS_START: 240,
  LABELS_END: 360,
  RELATIONSHIP_START: 360,
  RELATIONSHIP_END: 480,
  HOLD_START: 480,
  HOLD_END: 600,
  NARRATION_START: 360,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  BACKGROUND_GRADIENT_END: "#0f0f1a",
  // Mold (initial state)
  MOLD_METALLIC_LIGHT: "#A0B0C0",
  MOLD_METALLIC_MID: "#8A9BA8",
  MOLD_METALLIC_DARK: "#5A6A7A",
  MOLD_EDGE: "#C0CED8",
  MOLD_CAVITY: "#2a2a3e",
  // Part (initial state)
  PART_AMBER: "#D9944A",
  PART_AMBER_LIGHT: "#E8B070",
  // Document (final state)
  DOC_WHITE: "#FFFFFF",
  DOC_BORDER: "#D0D8E0",
  DOC_SHADOW: "rgba(0, 0, 0, 0.3)",
  DOC_TITLE_COLOR: "#1a1a2e",
  DOC_TEXT_COLOR: "#333333",
  // Code (final state)
  CODE_GRAY: "#A0A0A0",
  CODE_KEYWORD: "#A0A0A0",
  // Prompt glow
  PROMPT_GLOW: "#4A90D9",
  PROMPT_GLOW_RGBA: "rgba(74, 144, 217, 0.6)",
  // Flow arrow
  ARROW_COLOR: "rgba(74, 144, 217, 0.8)",
  ARROW_LABEL: "rgba(255, 255, 255, 0.7)",
  // Narration
  NARRATION_WHITE: "rgba(255, 255, 255, 0.95)",
};

// Mold shape configuration (initial state — wider, shorter, left-center)
export const MOLD_SHAPE = {
  // Initial: wide metallic rectangle
  initialX: 560,
  initialY: 260,
  initialWidth: 340,
  initialHeight: 140,
  initialRx: 6,
  // Final: taller, narrower document
  finalX: 560,
  finalY: 160,
  finalWidth: 420,
  finalHeight: 380,
  finalRx: 8,
};

// Part shape configuration (initial state — amber block below mold)
export const PART_SHAPE = {
  // Initial: compact amber part
  initialX: 640,
  initialY: 460,
  initialWidth: 180,
  initialHeight: 60,
  initialRx: 10,
  // Final: code region below document
  finalX: 570,
  finalY: 620,
  finalWidth: 400,
  finalHeight: 240,
  finalRx: 4,
};

// Prompt document text content
export const PROMPT_TITLE = "PROMPT";

export const PROMPT_LINES = [
  "Parse user IDs from untrusted",
  "input. Return None on failure,",
  "never throw. Handle unicode.",
  "",
  "Requirements:",
  "- Validate format",
  "- Sanitize input",
  "- Return clean ID or None",
];

// Code text content
export const CODE_LINES = [
  "def parse_user_id(input_str):",
  "    if not input_str:",
  "        return None",
  "    clean = sanitize(input_str)",
  "    if not validate_format(clean):",
  "        return None",
  "    return clean",
];

// Props schema
export const MoldToPromptProps = z.object({
  showNarration: z.boolean().default(true),
});

export const defaultMoldToPromptProps: z.infer<typeof MoldToPromptProps> = {
  showNarration: true,
};

export type MoldToPromptPropsType = z.infer<typeof MoldToPromptProps>;

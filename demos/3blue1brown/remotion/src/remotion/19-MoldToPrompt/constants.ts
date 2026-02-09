import { z } from "zod";

// Video specs
export const MOLD_TO_PROMPT_FPS = 30;
export const MOLD_TO_PROMPT_DURATION_SECONDS = 20;
export const MOLD_TO_PROMPT_DURATION_FRAMES =
  MOLD_TO_PROMPT_FPS * MOLD_TO_PROMPT_DURATION_SECONDS;
export const MOLD_TO_PROMPT_WIDTH = 1920;
export const MOLD_TO_PROMPT_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Frame 0-90:    Setup — Verilog code, gate netlist, Synopsys checkmark visible
// Frame 90-240:  Primary morph — THREE parallel transformations
// Frame 240-360: Labels — "PROMPT" title, code text, test checkmarks, glows
// Frame 360-480: Relationship — flow arrow from prompt to code
// Frame 480-600: Hold — final state, prompt + tests glowing, code present
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

  // Chip design / left side (teal colors from ChipDesignHistory)
  CODE_BG: "#1E1E2E",
  VERILOG_KEYWORD: "#2AA198",
  VERILOG_IDENTIFIER: "#E0E0E0",
  VERILOG_NUMBER: "#B58900",
  VERILOG_COMMENT: "#586E75",
  NETLIST_TEAL: "#1A7A6E",
  NETLIST_BORDER: "rgba(42, 161, 152, 0.3)",
  NETLIST_BG: "rgba(26, 122, 110, 0.08)",
  CHECK_GREEN: "#5AAA6E",
  SYNOPSYS_BORDER: "#8A9BA8",

  // Software / right side (PDD colors)
  PROMPT_BG: "#FFFFFF",
  PROMPT_BORDER: "#D0D8E0",
  PROMPT_TITLE_COLOR: "#1a1a2e",
  PROMPT_TEXT_COLOR: "#333333",
  PROMPT_GLOW: "#4A90D9", // Blue
  PROMPT_GLOW_RGBA: "rgba(74, 144, 217, 0.6)",

  CODE_GRAY: "#A0A0A0", // Software code (gray, no glow)
  CODE_BG_DARK: "#1E1E2A",

  TEST_AMBER: "#D9944A", // Tests (amber glow)
  TEST_AMBER_GLOW: "rgba(217, 148, 74, 0.6)",
  TEST_CHECK_GREEN: "#5AAA6E",

  // Flow arrow
  ARROW_COLOR: "rgba(74, 144, 217, 0.8)",
  ARROW_LABEL: "rgba(255, 255, 255, 0.7)",

  // Narration
  NARRATION_WHITE: "rgba(255, 255, 255, 0.95)",
};

// Verilog code block configuration (LEFT side, starting state)
export const VERILOG_BLOCK = {
  // Initial: Verilog code from chip design
  initialX: 260,
  initialY: 180,
  initialWidth: 400,
  initialHeight: 320,
  // Final: Prompt document (RIGHT side)
  finalX: 1160,
  finalY: 160,
  finalWidth: 420,
  finalHeight: 380,
};

// Gate netlist configuration (LEFT side, starting state)
export const NETLIST_BLOCK = {
  // Initial: Gate-level netlist from chip design
  initialX: 280,
  initialY: 560,
  initialWidth: 220,
  initialHeight: 140,
  // Final: Software code (RIGHT side)
  finalX: 1170,
  finalY: 620,
  finalWidth: 400,
  finalHeight: 240,
};

// Synopsys checkmark configuration (LEFT side, starting state)
export const CHECKMARK_CONFIG = {
  // Initial: Single Synopsys checkmark
  initialX: 280,
  initialY: 770,
  // Final: Test suite with multiple checkmarks (RIGHT side)
  finalX: 1170,
  finalY: 900,
};

// Verilog source code (from ChipDesignHistory)
export const VERILOG_SOURCE = `module alu(
  input  [7:0] a, b,
  input  [1:0] op,
  output reg [7:0] result
);
  always @(*) begin
    case(op)
      2'b00: result = a + b;
      2'b01: result = a - b;
      2'b10: result = a & b;
      2'b11: result = a | b;
    endcase
  end
endmodule`;

export const VERILOG_KEYWORDS = [
  "module",
  "input",
  "output",
  "reg",
  "always",
  "begin",
  "case",
  "endcase",
  "end",
  "endmodule",
];

// Gate netlist layout (from ChipDesignHistory)
export const NETLIST_GATES = [
  { type: "AND" as const, x: 30, y: 30 },
  { type: "AND" as const, x: 30, y: 80 },
  { type: "OR" as const, x: 110, y: 55 },
  { type: "NOT" as const, x: 170, y: 55 },
];

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

// Software code text content
export const CODE_LINES = [
  "def parse_user_id(input_str):",
  "    if not input_str:",
  "        return None",
  "    clean = sanitize(input_str)",
  "    if not validate_format(clean):",
  "        return None",
  "    return clean",
];

// Test suite content
export const TEST_LINES = [
  "test_valid_input",
  "test_empty_input",
  "test_unicode_handling",
];

// Props schema
export const MoldToPromptProps = z.object({
  showNarration: z.boolean().default(true),
});

export const defaultMoldToPromptProps: z.infer<typeof MoldToPromptProps> = {
  showNarration: true,
};

export type MoldToPromptPropsType = z.infer<typeof MoldToPromptProps>;

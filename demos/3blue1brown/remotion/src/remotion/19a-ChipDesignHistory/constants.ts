import { z } from "zod";

// Video specs
export const CHIP_DESIGN_FPS = 30;
export const CHIP_DESIGN_DURATION_SECONDS = 80;
export const CHIP_DESIGN_DURATION_FRAMES =
  CHIP_DESIGN_FPS * CHIP_DESIGN_DURATION_SECONDS;
export const CHIP_DESIGN_WIDTH = 1920;
export const CHIP_DESIGN_HEIGHT = 1080;

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  BACKGROUND_GRADIENT_END: "#0f0f1a",
  // Verilog code
  CODE_BG: "#1E1E2E",
  CODE_KEYWORD: "#2AA198",
  CODE_IDENTIFIER: "#E0E0E0",
  CODE_NUMBER: "#B58900",
  CODE_COMMENT: "#586E75",
  // Synthesis
  SYNTH_BORDER: "#8A9BA8",
  SYNTH_FILL: "rgba(138, 155, 168, 0.15)",
  SYNTH_LABEL: "#CCCCCC",
  // Netlists
  NETLIST_TEAL: "#1A7A6E",
  NETLIST_BORDER: "rgba(42, 161, 152, 0.3)",
  NETLIST_BG: "rgba(26, 122, 110, 0.08)",
  // Verification
  CHECK_GREEN: "#5AAA6E",
  CHECK_GREEN_GLOW: "rgba(90, 170, 110, 0.4)",
  // Staircase
  STEP_TRANSISTORS: "#586E75",
  STEP_SCHEMATICS: "#7A7A6E",
  STEP_RTL: "#2AA198",
  STEP_BEHAVIORAL: "#3CC2B4",
  STEP_NATURAL_LANG: "#4A90D9",
  ARROW_AMBER: "#D9944A",
  DECADE_LABEL: "#CCCCCC",
  // General
  WHITE: "#FFFFFF",
  BLUE_GLOW: "#4A90D9",
  BLUE_GLOW_RGBA: "rgba(74, 144, 217, 0.6)",
  NARRATION_WHITE: "rgba(255, 255, 255, 0.95)",
};

// Beat timings for each phase (in frames at 30fps, relative to phase start)

// Phase: verilogSynthesis (spec 09c) ~21s = 634 frames
// Covers narration segments 13-16: 1980s hand-drawn -> Verilog -> synthesis -> gates
export const VERILOG_BEATS = {
  // Schematic dissolves
  DISSOLVE_START: 0,
  DISSOLVE_END: 60,
  // Verilog code types in
  CODE_TYPE_START: 60,
  CODE_TYPE_END: 210,
  // Synthesis tool appears
  SYNTH_START: 210,
  SYNTH_END: 330,
  // Netlist flows out
  NETLIST_START: 330,
  NETLIST_END: 450,
  // Hold complete pipeline
  HOLD_START: 450,
  HOLD_END: 634,
};

// Phase: threeNetlists (spec 09d) ~13s = 397 frames
// Covers narration segments 17-19: non-deterministic, different gates, varied output
export const THREE_NETLISTS_BEATS = {
  // Setup: Verilog code + 3 empty slots
  SETUP_START: 0,
  SETUP_END: 60,
  // First synthesis run
  RUN1_START: 60,
  RUN1_END: 150,
  // Second synthesis run
  RUN2_START: 150,
  RUN2_END: 240,
  // Third synthesis run
  RUN3_START: 240,
  RUN3_END: 330,
  // Hold all three visible
  HOLD_START: 330,
  HOLD_END: 397,
};

// Phase: verification (spec 09d continued) ~22s = 646 frames
// Covers narration segments 20-23: Synopsys, SAT/SMT, function same every time
export const VERIFICATION_BEATS = {
  // Show three netlists from previous phase
  SETUP_START: 0,
  SETUP_END: 60,
  // Checkmarks appear sequentially
  CHECK1_START: 60,
  CHECK2_START: 90,
  CHECK3_START: 120,
  // "Functionally Equivalent" label
  LABEL_START: 180,
  LABEL_END: 240,
  // Hold on verified netlists
  HOLD_START: 240,
  HOLD_END: 646,
};

// Phase: abstractionTimeline (spec 09e) ~22s = 676 frames
// Covers narration segments 24-27: 1990 schematic, mid-90s, all HDL, moved up
export const TIMELINE_BEATS = {
  // Step 1: Transistors
  STEP1_START: 0,
  STEP1_END: 80,
  // Arrow + Step 2: Schematics
  STEP2_START: 80,
  STEP2_END: 160,
  // Arrow + Step 3: RTL/Verilog
  STEP3_START: 160,
  STEP3_END: 240,
  // Arrow + Step 4: Behavioral/HLS
  STEP4_START: 240,
  STEP4_END: 320,
  // Arrow + Step 5: Natural Language -> Code
  STEP5_START: 320,
  STEP5_END: 420,
  // Pulse on final step
  PULSE_START: 420,
  // Hold full staircase
  HOLD_START: 480,
  HOLD_END: 676,
};

// Verilog source code for display
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

// Verilog keywords for syntax highlighting
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

// Gate netlist layout variants
export const NETLIST_LAYOUTS = {
  A: [
    { type: "AND" as const, x: 30, y: 30 },
    { type: "AND" as const, x: 30, y: 80 },
    { type: "OR" as const, x: 110, y: 55 },
    { type: "NOT" as const, x: 170, y: 55 },
  ],
  B: [
    { type: "OR" as const, x: 30, y: 55 },
    { type: "NOT" as const, x: 90, y: 30 },
    { type: "AND" as const, x: 90, y: 80 },
    { type: "OR" as const, x: 150, y: 55 },
  ],
  C: [
    { type: "NAND" as const, x: 40, y: 30 },
    { type: "NOR" as const, x: 40, y: 80 },
    { type: "AND" as const, x: 120, y: 40 },
    { type: "NOT" as const, x: 120, y: 80 },
  ],
};

// Abstraction staircase steps
export const STAIRCASE_STEPS = [
  {
    label: "Transistors",
    decade: "1970s",
    color: COLORS.STEP_TRANSISTORS,
    width: 200,
  },
  {
    label: "Schematics",
    decade: "1980s",
    color: COLORS.STEP_SCHEMATICS,
    width: 210,
  },
  {
    label: "RTL / Verilog",
    decade: "1990s",
    color: COLORS.STEP_RTL,
    width: 220,
  },
  {
    label: "Behavioral / HLS",
    decade: "2010s",
    color: COLORS.STEP_BEHAVIORAL,
    width: 230,
  },
  {
    label: "Natural Language",
    sublabel: "\u2192 Code",
    decade: "2020s",
    color: COLORS.STEP_NATURAL_LANG,
    width: 260,
  },
];

// Props schema
export const ChipDesignHistoryProps = z.object({
  phase: z
    .enum([
      "verilogSynthesis",
      "threeNetlists",
      "verification",
      "abstractionTimeline",
    ])
    .default("verilogSynthesis"),
});

export const defaultChipDesignHistoryProps: z.infer<
  typeof ChipDesignHistoryProps
> = {
  phase: "verilogSynthesis",
};

export type ChipDesignHistoryPropsType = z.infer<typeof ChipDesignHistoryProps>;

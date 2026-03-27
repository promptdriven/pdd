// === Colors ===
export const BG_COLOR = '#0A0F1A';
export const CODE_BG_COLOR = '#1E293B';
export const WIRE_COLOR = '#E2E8F0';
export const GATE_COLOR = '#78909C';
export const LABEL_COLOR = '#64748B';
export const EQUIV_COLOR = '#5AAA6E';
export const ARROW_COLOR = '#64748B';
export const CODE_TEXT_COLOR = '#E2E8F0';
export const KEYWORD_COLOR = '#C084FC';
export const TYPE_COLOR = '#38BDF8';
export const COMMENT_COLOR = '#64748B';

// === Canvas ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// === Code Block Layout ===
export const CODE_X = 660;
export const CODE_Y = 80;
export const CODE_WIDTH = 600;
export const CODE_HEIGHT = 120;

// === Column Layout ===
export const COLUMN_POSITIONS = [200, 660, 1120] as const;
export const COLUMN_Y = 280;
export const COLUMN_WIDTH = 400;
export const COLUMN_HEIGHT = 500;

// === Animation Frame Ranges ===
export const ARROWS_START = 0;
export const ARROWS_DURATION = 60;
export const RUN1_START = 60;
export const RUN2_START = 120;
export const RUN3_START = 180;
export const NETLIST_GEN_DURATION = 60;
export const HOLD_START = 240;
export const CHECKMARK_START = 300;
export const CHECKMARK_DURATION = 30;
export const LABEL_FADE_DURATION = 20;
export const HOLD_EQUIV_START = 420;
export const FADE_OUT_START = 600;
export const FADE_OUT_DURATION = 60;
export const TOTAL_FRAMES = 750;

// === Checkmark ===
export const CHECKMARK_SIZE = 48;
export const CHECKMARK_Y = 720;
export const EQUIV_LABEL_Y = 780;

// === Verilog source ===
export const VERILOG_CODE = `module alu(
  input  [7:0] a, b,
  input  [1:0] op,
  output [7:0] result
);
  assign result = (op==0) ? a+b :
                  (op==1) ? a-b :
                  (op==2) ? a&b : a|b;
endmodule`;

// === Run data ===
export const RUNS = [
  { id: 'run_1', topology: 'dense-left' as const, label: 'Run 1', colX: 200 },
  { id: 'run_2', topology: 'tree-branch' as const, label: 'Run 2', colX: 660 },
  { id: 'run_3', topology: 'linear-chain' as const, label: 'Run 3', colX: 1120 },
] as const;

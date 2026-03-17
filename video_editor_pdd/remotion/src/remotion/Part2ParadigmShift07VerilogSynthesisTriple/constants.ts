// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// Background
export const BG_COLOR = "#0A0F1A";
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.03;
export const GRID_SPACING = 20;

// Colors
export const CODE_KEYWORD_COLOR = "#C792EA";
export const CODE_TEXT_COLOR = "#E2E8F0";
export const CODE_COMMENT_COLOR = "#546E7A";
export const CODE_STRING_COLOR = "#C3E88D";
export const CODE_BG_COLOR = "#1E293B";
export const CODE_BG_OPACITY = 0.3;

export const COMPILER_COLOR = "#4A90D9";
export const COMPILER_OPACITY = 0.6;
export const COMPILER_LABEL_OPACITY = 0.5;

export const GATE_COLOR = "#94A3B8";
export const GATE_OPACITY = 0.5;
export const WIRE_COLOR = "#475569";
export const WIRE_OPACITY = 0.3;

export const ARROW_COLOR = "#475569";
export const ARROW_OPACITY = 0.3;

export const SCHEMATIC_COLOR = "#64748B";
export const SCHEMATIC_OPACITY = 0.5;

export const CHECKMARK_COLOR = "#5AAA6E";
export const CHECKMARK_OPACITY = 0.6;
export const EQUIV_LABEL_COLOR = "#5AAA6E";
export const EQUIV_LABEL_OPACITY = 0.6;
export const EQUIV_LINE_OPACITY = 0.2;

export const SAME_INPUT_COLOR = "#64748B";
export const SAME_INPUT_OPACITY = 0.4;

// Typography
export const CODE_FONT = "'JetBrains Mono', 'Fira Code', monospace";
export const CODE_FONT_SIZE = 11;
export const UI_FONT = "'Inter', sans-serif";
export const UI_FONT_SIZE = 12;
export const COMPILER_LABEL_SIZE = 11;

// Phase 1 layout
export const SCHEMATIC_X = 960;
export const SCHEMATIC_Y = 300;
export const SCHEMATIC_W = 600;
export const SCHEMATIC_H = 300;

export const CODE_X = 960;
export const CODE_Y = 250;
export const CODE_W = 500;
export const CODE_H = 200;

export const COMPILER_X = 960;
export const COMPILER_Y = 480;
export const COMPILER_SIZE = 60;

export const NETLIST_X = 960;
export const NETLIST_Y = 650;
export const NETLIST_W = 400;
export const NETLIST_H = 200;

// Phase 2 layout
export const PHASE2_CODE_Y = 100;
export const PHASE2_CODE_W = 800;
export const PHASE2_CODE_H = 140;
export const PHASE2_CODE_FONT_SIZE = 10;

export const SAME_INPUT_Y = 25;

export const COL_1_X = 280;
export const COL_2_X = 960;
export const COL_3_X = 1640;
export const COL_WIDTH = 450;

export const PHASE2_NETLIST_Y = 550;
export const PHASE2_NETLIST_W = 400;
export const PHASE2_NETLIST_H = 250;

export const CHECKMARK_SIZE = 30;
export const CHECKMARK_Y = 420;

// Animation timing (frames at 30fps)
export const TOTAL_FRAMES = 540;

// Phase 1: Schematic dissolves -> Verilog appears
export const SCHEMATIC_DISSOLVE_START = 0;
export const SCHEMATIC_DISSOLVE_END = 40;

export const CODE_TYPING_START = 40;
export const CODE_TYPING_END = 90;
export const CODE_CHAR_DELAY = 2;

export const ARROW_DRAW_START = 90;
export const ARROW_DRAW_END = 110;
export const COMPILER_APPEAR_START = 90;
export const COMPILER_APPEAR_END = 130;

export const SINGLE_NETLIST_DRAW_START = 130;
export const SINGLE_NETLIST_DRAW_END = 180;

// Phase 2: Triple synthesis
export const PHASE2_START = 180;
export const PHASE2_CROSSFADE_END = 220;

export const TRIPLE_ARROW_START = 220; // relative to absolute frame
export const TRIPLE_ARROW_END = 260;

export const TRIPLE_NETLIST_START = 280;
export const TRIPLE_NETLIST_END = 380;
export const NETLIST_GATE_STAGGER = 3;

export const NETLIST_HOLD_START = 300;
export const NETLIST_HOLD_END = 400;

export const CHECKMARK_POP_START = 400;
export const CHECKMARK_POP_DURATION = 12;
export const CHECKMARK_STAGGER = 8;

export const EQUIV_LABEL_START = 420;
export const EQUIV_LABEL_END = 435;

export const DASHED_LINE_START = 430;
export const DASHED_LINE_END = 450;

export const HOLD_START = 460;
export const HOLD_END = 540;

// Verilog code content
export const VERILOG_CODE = `module counter(
  input clk, rst,
  output reg [7:0] count
);
  always @(posedge clk)
    if (rst) count <= 0;
    else count <= count + 1;
endmodule`;

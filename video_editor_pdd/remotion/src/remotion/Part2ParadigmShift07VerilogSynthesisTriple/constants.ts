// Colors
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.03;

export const CODE_BG = '#1E293B';
export const CODE_BG_OPACITY = 0.3;
export const CODE_KEYWORD = '#C792EA';
export const CODE_IDENT = '#E2E8F0';
export const CODE_COMMENT = '#546E7A';
export const CODE_STRING = '#C3E88D';

export const COMPILER_COLOR = '#4A90D9';
export const COMPILER_OPACITY = 0.95;
export const COMPILER_LABEL_OPACITY = 0.6;
export const COMPILER_LABEL_SIZE = 11;
export const GATE_COLOR = '#94A3B8';
export const GATE_OPACITY = 0.95;
export const WIRE_COLOR = '#475569';
export const WIRE_OPACITY = 0.85;
export const CHECKMARK_COLOR = '#5AAA6E';
export const LABEL_COLOR = '#64748B';
export const SCHEMATIC_COLOR = '#64748B';
export const UI_FONT = "'Inter', sans-serif";

// Dimensions
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const GRID_SPACING = 20;

// Phase 2 column positions
export const COL_1_X = 280;
export const COL_2_X = 960;
export const COL_3_X = 1640;
export const COL_WIDTH = 450;

// Animation frame markers
export const PHASE1_START = 0;
export const SCHEMATIC_END = 40;
export const CODE_APPEAR = 40;
export const CODE_END = 90;
export const COMPILER_APPEAR = 90;
export const COMPILER_END = 130;
export const NETLIST_APPEAR = 130;
export const NETLIST_END = 180;
export const PHASE2_START = 180;
export const ARROWS_START = 220;
export const TRIPLE_NETLIST_START = 280;
export const TRIPLE_NETLIST_END = 400;
export const CHECKMARK_START = 400;
export const CHECKMARK_END = 460;
export const TOTAL_FRAMES = 540;

// Verilog source code
export const VERILOG_CODE = `module counter(
  input clk, rst,
  output reg [7:0] count
);
  always @(posedge clk)
    if (rst) count <= 0;
    else count <= count + 1;
endmodule`;

// Verilog syntax tokens for coloring
export interface CodeToken {
  text: string;
  color: string;
  opacity?: number;
}

export type CodeLine = CodeToken[];

export const VERILOG_TOKENS: CodeLine[] = [
  [
    { text: 'module', color: CODE_KEYWORD },
    { text: ' counter(', color: CODE_IDENT },
  ],
  [
    { text: '  ', color: CODE_IDENT },
    { text: 'input', color: CODE_KEYWORD },
    { text: ' clk, rst,', color: CODE_IDENT },
  ],
  [
    { text: '  ', color: CODE_IDENT },
    { text: 'output', color: CODE_KEYWORD },
    { text: ' ', color: CODE_IDENT },
    { text: 'reg', color: CODE_KEYWORD },
    { text: ' [7:0] count', color: CODE_IDENT },
  ],
  [{ text: ');', color: CODE_IDENT }],
  [
    { text: '  ', color: CODE_IDENT },
    { text: 'always', color: CODE_KEYWORD },
    { text: ' @(', color: CODE_IDENT },
    { text: 'posedge', color: CODE_KEYWORD },
    { text: ' clk)', color: CODE_IDENT },
  ],
  [
    { text: '    ', color: CODE_IDENT },
    { text: 'if', color: CODE_KEYWORD },
    { text: ' (rst) count <= ', color: CODE_IDENT },
    { text: '0', color: CODE_STRING },
    { text: ';', color: CODE_IDENT },
  ],
  [
    { text: '    ', color: CODE_IDENT },
    { text: 'else', color: CODE_KEYWORD },
    { text: ' count <= count + ', color: CODE_IDENT },
    { text: '1', color: CODE_STRING },
    { text: ';', color: CODE_IDENT },
  ],
  [
    { text: 'endmodule', color: CODE_KEYWORD },
  ],
];

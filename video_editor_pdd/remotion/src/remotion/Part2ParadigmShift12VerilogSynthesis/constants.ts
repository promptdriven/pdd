// === Colors ===
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.05;

export const CODE_BG = '#1E293B';
export const CODE_BORDER_RADIUS = 8;
export const CODE_PADDING = 24;

// Syntax highlighting colors
export const SYNTAX_KEYWORD = '#C792EA';   // purple — module, always, assign, etc.
export const SYNTAX_IDENT = '#E2E8F0';     // white — identifiers
export const SYNTAX_COMMENT = '#546E7A';   // gray — comments
export const SYNTAX_NUMBER = '#F78C6C';    // orange — numeric literals
export const SYNTAX_PUNCTUATION = '#89DDFF'; // cyan — brackets, semicolons
export const SYNTAX_TYPE = '#FFCB6B';      // gold — reg, wire, input, output

// Chip / synthesis
export const CHIP_OUTLINE = '#4A90D9';
export const CHIP_FILL_OPACITY = 0.1;
export const CHIP_LABEL_COLOR = '#94A3B8';

// Gate stream
export const GATE_COLOR = '#5AAA6E';

// Schematic dissolve
export const SCHEMATIC_LINE_COLOR = '#3B82F6';
export const SCHEMATIC_NODE_COLOR = '#22C55E';

// === Dimensions ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

export const CODE_BLOCK_X = 560;
export const CODE_BLOCK_Y = 100;
export const CODE_BLOCK_WIDTH = 800;

export const CHIP_X = 960;
export const CHIP_Y = 580;
export const CHIP_WIDTH = 200;
export const CHIP_HEIGHT = 100;

export const GATE_STREAM_X = 1100;
export const GATE_STREAM_Y = 580;
export const GATE_STREAM_WIDTH = 700;

// === Grid ===
export const GRID_SPACING = 60;

// === Animation Timing (frames) ===
export const TOTAL_FRAMES = 360;

export const DISSOLVE_START = 0;
export const DISSOLVE_END = 60;

export const CODE_TYPE_START = 60;
export const CODE_TYPE_END = 150;

export const CHIP_FADE_START = 150;
export const CHIP_FADE_END = 210;

export const GATE_STREAM_START = 210;
export const GATE_HOLD_START = 300;

// Characters per frame for typing
export const TYPE_SPEED = 3; // frames per character

// === Verilog Code Sample ===
export const VERILOG_CODE_LINES: Array<{ text: string; tokens: Array<{ value: string; color: string }> }> = [
  {
    text: 'module counter(',
    tokens: [
      { value: 'module', color: SYNTAX_KEYWORD },
      { value: ' counter', color: SYNTAX_IDENT },
      { value: '(', color: SYNTAX_PUNCTUATION },
    ],
  },
  {
    text: '  input clk, rst,',
    tokens: [
      { value: '  ', color: SYNTAX_IDENT },
      { value: 'input', color: SYNTAX_TYPE },
      { value: ' clk', color: SYNTAX_IDENT },
      { value: ',', color: SYNTAX_PUNCTUATION },
      { value: ' rst', color: SYNTAX_IDENT },
      { value: ',', color: SYNTAX_PUNCTUATION },
    ],
  },
  {
    text: '  output reg [7:0] count',
    tokens: [
      { value: '  ', color: SYNTAX_IDENT },
      { value: 'output', color: SYNTAX_TYPE },
      { value: ' ', color: SYNTAX_IDENT },
      { value: 'reg', color: SYNTAX_TYPE },
      { value: ' ', color: SYNTAX_IDENT },
      { value: '[', color: SYNTAX_PUNCTUATION },
      { value: '7', color: SYNTAX_NUMBER },
      { value: ':', color: SYNTAX_PUNCTUATION },
      { value: '0', color: SYNTAX_NUMBER },
      { value: ']', color: SYNTAX_PUNCTUATION },
      { value: ' count', color: SYNTAX_IDENT },
    ],
  },
  {
    text: ');',
    tokens: [
      { value: ')', color: SYNTAX_PUNCTUATION },
      { value: ';', color: SYNTAX_PUNCTUATION },
    ],
  },
  {
    text: '  // 8-bit up counter',
    tokens: [
      { value: '  ', color: SYNTAX_IDENT },
      { value: '// 8-bit up counter', color: SYNTAX_COMMENT },
    ],
  },
  {
    text: '  always @(posedge clk)',
    tokens: [
      { value: '  ', color: SYNTAX_IDENT },
      { value: 'always', color: SYNTAX_KEYWORD },
      { value: ' @', color: SYNTAX_PUNCTUATION },
      { value: '(', color: SYNTAX_PUNCTUATION },
      { value: 'posedge', color: SYNTAX_KEYWORD },
      { value: ' clk', color: SYNTAX_IDENT },
      { value: ')', color: SYNTAX_PUNCTUATION },
    ],
  },
  {
    text: '    if (rst) count <= 0;',
    tokens: [
      { value: '    ', color: SYNTAX_IDENT },
      { value: 'if', color: SYNTAX_KEYWORD },
      { value: ' (', color: SYNTAX_PUNCTUATION },
      { value: 'rst', color: SYNTAX_IDENT },
      { value: ')', color: SYNTAX_PUNCTUATION },
      { value: ' count ', color: SYNTAX_IDENT },
      { value: '<=', color: SYNTAX_PUNCTUATION },
      { value: ' ', color: SYNTAX_IDENT },
      { value: '0', color: SYNTAX_NUMBER },
      { value: ';', color: SYNTAX_PUNCTUATION },
    ],
  },
  {
    text: '    else count <= count + 1;',
    tokens: [
      { value: '    ', color: SYNTAX_IDENT },
      { value: 'else', color: SYNTAX_KEYWORD },
      { value: ' count ', color: SYNTAX_IDENT },
      { value: '<=', color: SYNTAX_PUNCTUATION },
      { value: ' count ', color: SYNTAX_IDENT },
      { value: '+', color: SYNTAX_PUNCTUATION },
      { value: ' ', color: SYNTAX_IDENT },
      { value: '1', color: SYNTAX_NUMBER },
      { value: ';', color: SYNTAX_PUNCTUATION },
    ],
  },
  {
    text: 'endmodule',
    tokens: [
      { value: 'endmodule', color: SYNTAX_KEYWORD },
    ],
  },
];

// Flat string for character counting
export const VERILOG_CODE_FLAT = VERILOG_CODE_LINES.map((l) => l.text).join('\n');

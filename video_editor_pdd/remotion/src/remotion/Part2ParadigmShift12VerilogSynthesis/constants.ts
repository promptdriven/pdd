// ── Colors ──────────────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.05;

export const CODE_BG = "#1E293B";
export const CODE_KEYWORD = "#C792EA";
export const CODE_IDENTIFIER = "#E2E8F0";
export const CODE_COMMENT = "#546E7A";
export const CODE_NUMBER = "#F78C6C";
export const CODE_PUNCTUATION = "#89DDFF";

export const CHIP_OUTLINE = "#4A90D9";
export const CHIP_FILL_OPACITY = 0.1;
export const CHIP_LABEL_COLOR = "#94A3B8";

export const GATE_COLOR = "#5AAA6E";
export const SCHEMATIC_COLOR = "#4A90D9";

// ── Dimensions ──────────────────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;

export const CODE_BLOCK_X = 560;
export const CODE_BLOCK_Y = 100;
export const CODE_BLOCK_WIDTH = 800;
export const CODE_BLOCK_PADDING = 24;
export const CODE_BLOCK_BORDER_RADIUS = 8;
export const CODE_FONT_SIZE = 16;
export const CODE_LINE_HEIGHT = 24;

export const CHIP_X = 960;
export const CHIP_Y = 560;
export const CHIP_WIDTH = 200;
export const CHIP_HEIGHT = 100;

export const GATE_STREAM_X = 1100;
export const GATE_STREAM_Y = 560;
export const GATE_STREAM_WIDTH = 700;

// ── Animation Frames ────────────────────────────────────────────────
export const TOTAL_FRAMES = 360;
export const FPS = 30;

export const DISSOLVE_START = 0;
export const DISSOLVE_END = 60;

export const CODE_TYPE_START = 60;
export const CODE_TYPE_END = 150;

export const CHIP_FADE_START = 150;
export const CHIP_FADE_END = 210;

export const GATE_STREAM_START = 210;
export const GATE_HOLD_START = 300;

// ── Verilog Code ────────────────────────────────────────────────────
export const VERILOG_CODE = `module counter(
  input clk, rst,
  output reg [7:0] count
);
  always @(posedge clk)
    if (rst) count <= 0;
    else count <= count + 1;
endmodule`;

export const VERILOG_LINES = VERILOG_CODE.split("\n");

// Token types for syntax highlighting
export type TokenType = "keyword" | "identifier" | "comment" | "number" | "punctuation";

export interface Token {
  text: string;
  type: TokenType;
}

// Simple Verilog tokenizer
export function tokenizeLine(line: string): Token[] {
  const tokens: Token[] = [];
  const keywords = new Set([
    "module", "input", "output", "reg", "always", "if", "else", "endmodule", "assign", "wire",
  ]);

  let remaining = line;
  while (remaining.length > 0) {
    // Leading whitespace
    const wsMatch = remaining.match(/^(\s+)/);
    if (wsMatch) {
      tokens.push({ text: wsMatch[1], type: "identifier" });
      remaining = remaining.slice(wsMatch[1].length);
      continue;
    }

    // Comment
    if (remaining.startsWith("//")) {
      tokens.push({ text: remaining, type: "comment" });
      break;
    }

    // Number
    const numMatch = remaining.match(/^(\d+)/);
    if (numMatch) {
      tokens.push({ text: numMatch[1], type: "number" });
      remaining = remaining.slice(numMatch[1].length);
      continue;
    }

    // Bit width like [7:0]
    const bitMatch = remaining.match(/^(\[\d+:\d+\])/);
    if (bitMatch) {
      tokens.push({ text: bitMatch[1], type: "number" });
      remaining = remaining.slice(bitMatch[1].length);
      continue;
    }

    // Word (keyword or identifier)
    const wordMatch = remaining.match(/^([a-zA-Z_]\w*)/);
    if (wordMatch) {
      const word = wordMatch[1];
      const type: TokenType = keywords.has(word) ? "keyword" : "identifier";
      tokens.push({ text: word, type });
      remaining = remaining.slice(word.length);
      continue;
    }

    // Special: @(posedge ...)
    if (remaining.startsWith("@")) {
      const atMatch = remaining.match(/^(@\(posedge\s+\w+\))/);
      if (atMatch) {
        tokens.push({ text: "@(", type: "punctuation" });
        tokens.push({ text: "posedge", type: "keyword" });
        const inner = atMatch[1].match(/@\(posedge\s+(\w+)\)/);
        if (inner) {
          tokens.push({ text: " " + inner[1], type: "identifier" });
        }
        tokens.push({ text: ")", type: "punctuation" });
        remaining = remaining.slice(atMatch[1].length);
        continue;
      }
    }

    // Punctuation / operators
    const punctMatch = remaining.match(/^([^\w\s]+)/);
    if (punctMatch) {
      tokens.push({ text: punctMatch[1], type: "punctuation" });
      remaining = remaining.slice(punctMatch[1].length);
      continue;
    }

    // Fallback: single char
    tokens.push({ text: remaining[0], type: "identifier" });
    remaining = remaining.slice(1);
  }

  return tokens;
}

// Color map for token types
export function tokenColor(type: TokenType): string {
  switch (type) {
    case "keyword": return CODE_KEYWORD;
    case "identifier": return CODE_IDENTIFIER;
    case "comment": return CODE_COMMENT;
    case "number": return CODE_NUMBER;
    case "punctuation": return CODE_PUNCTUATION;
  }
}

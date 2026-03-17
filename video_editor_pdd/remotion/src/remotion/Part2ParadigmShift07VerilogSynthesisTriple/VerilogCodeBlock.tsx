import React from "react";
import { useCurrentFrame } from "remotion";
import {
  CODE_KEYWORD_COLOR,
  CODE_TEXT_COLOR,
  CODE_COMMENT_COLOR,
  CODE_STRING_COLOR,
  CODE_BG_COLOR,
  CODE_BG_OPACITY,
  CODE_FONT,
} from "./constants";

// Token types for syntax coloring
type TokenType = "keyword" | "text" | "comment" | "string" | "bracket";

interface Token {
  text: string;
  type: TokenType;
}

const TOKEN_COLORS: Record<TokenType, string> = {
  keyword: CODE_KEYWORD_COLOR,
  text: CODE_TEXT_COLOR,
  comment: CODE_COMMENT_COLOR,
  string: CODE_STRING_COLOR,
  bracket: CODE_TEXT_COLOR,
};

// Pre-tokenized Verilog code
const CODE_LINES: Token[][] = [
  [
    { text: "module", type: "keyword" },
    { text: " counter(", type: "text" },
  ],
  [
    { text: "  ", type: "text" },
    { text: "input", type: "keyword" },
    { text: " clk, rst,", type: "text" },
  ],
  [
    { text: "  ", type: "text" },
    { text: "output", type: "keyword" },
    { text: " ", type: "text" },
    { text: "reg", type: "keyword" },
    { text: " [", type: "text" },
    { text: "7", type: "string" },
    { text: ":", type: "text" },
    { text: "0", type: "string" },
    { text: "] count", type: "text" },
  ],
  [
    { text: ");", type: "text" },
  ],
  [
    { text: "  ", type: "text" },
    { text: "always", type: "keyword" },
    { text: " @(", type: "text" },
    { text: "posedge", type: "keyword" },
    { text: " clk)", type: "text" },
  ],
  [
    { text: "    ", type: "text" },
    { text: "if", type: "keyword" },
    { text: " (rst) count <= ", type: "text" },
    { text: "0", type: "string" },
    { text: ";", type: "text" },
  ],
  [
    { text: "    ", type: "text" },
    { text: "else", type: "keyword" },
    { text: " count <= count + ", type: "text" },
    { text: "1", type: "string" },
    { text: ";", type: "text" },
  ],
  [
    { text: "endmodule", type: "keyword" },
  ],
];

// Compute total character count for typing
const TOTAL_CHARS = CODE_LINES.reduce(
  (acc, line) => acc + line.reduce((a, t) => a + t.text.length, 0) + 1, // +1 for newline
  0
);

interface VerilogCodeBlockProps {
  x: number;
  y: number;
  width: number;
  height: number;
  fontSize: number;
  typeEffect?: boolean;
  charDelay?: number;
  typeStartFrame?: number;
}

export const VerilogCodeBlock: React.FC<VerilogCodeBlockProps> = ({
  x,
  y,
  width,
  height,
  fontSize,
  typeEffect = false,
  charDelay = 2,
  typeStartFrame = 0,
}) => {
  const frame = useCurrentFrame();

  const elapsed = Math.max(0, frame - typeStartFrame);
  const charsToShow = typeEffect
    ? Math.min(Math.floor(elapsed / charDelay), TOTAL_CHARS)
    : TOTAL_CHARS;

  let charCount = 0;
  const lineHeight = fontSize * 1.6;

  return (
    <div
      style={{
        position: "absolute",
        left: x - width / 2,
        top: y - height / 2,
        width,
        height,
        backgroundColor: CODE_BG_COLOR,
        opacity: typeEffect && frame < typeStartFrame ? 0 : 1,
        borderRadius: 4,
        padding: "12px 16px",
        overflow: "hidden",
        display: "flex",
        flexDirection: "column",
        justifyContent: "center",
      }}
      // Apply bg opacity via inline rgba
    >
      <div
        style={{
          position: "absolute",
          inset: 0,
          backgroundColor: CODE_BG_COLOR,
          opacity: CODE_BG_OPACITY,
          borderRadius: 4,
        }}
      />
      <div style={{ position: "relative", zIndex: 1 }}>
        {CODE_LINES.map((line, lineIdx) => {
          const lineContent: React.ReactNode[] = [];
          let lineVisible = false;

          for (const token of line) {
            const tokenChars = token.text.length;
            if (charCount >= charsToShow) break;

            const visibleChars = Math.min(tokenChars, charsToShow - charCount);
            if (visibleChars > 0) {
              lineVisible = true;
              lineContent.push(
                <span
                  key={`${lineIdx}-${charCount}`}
                  style={{ color: TOKEN_COLORS[token.type] }}
                >
                  {token.text.slice(0, visibleChars)}
                </span>
              );
            }
            charCount += tokenChars;
          }
          // Count the newline character
          charCount += 1;

          if (!lineVisible && typeEffect) return null;

          return (
            <div
              key={`line-${lineIdx}`}
              style={{
                fontFamily: CODE_FONT,
                fontSize,
                lineHeight: `${lineHeight}px`,
                whiteSpace: "pre",
                height: lineHeight,
              }}
            >
              {lineContent}
            </div>
          );
        })}
      </div>
    </div>
  );
};

export default VerilogCodeBlock;

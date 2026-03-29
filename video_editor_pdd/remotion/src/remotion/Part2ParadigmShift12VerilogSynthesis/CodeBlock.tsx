import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  CODE_BG,
  CODE_BLOCK_X,
  CODE_BLOCK_Y,
  CODE_BLOCK_WIDTH,
  CODE_BLOCK_PADDING,
  CODE_BLOCK_BORDER_RADIUS,
  CODE_FONT_SIZE,
  CODE_LINE_HEIGHT,
  CODE_TYPE_START,
  CODE_TYPE_END,
  VERILOG_LINES,
  tokenizeLine,
  tokenColor,
} from "./constants";

export const CodeBlock: React.FC = () => {
  const frame = useCurrentFrame();

  // Calculate total characters typed so far
  const typeFrame = frame - CODE_TYPE_START;
  if (typeFrame < 0) return null;

  const totalChars = VERILOG_LINES.join("\n").length;
  const maxFrames = CODE_TYPE_END - CODE_TYPE_START;
  const charsTyped = Math.min(
    Math.floor(typeFrame * (totalChars / maxFrames)),
    totalChars
  );

  // Container fade in
  const containerOpacity = interpolate(typeFrame, [0, 10], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Build the visible text with syntax highlighting
  let charCount = 0;

  return (
    <div
      style={{
        position: "absolute",
        left: CODE_BLOCK_X,
        top: CODE_BLOCK_Y,
        width: CODE_BLOCK_WIDTH,
        backgroundColor: CODE_BG,
        borderRadius: CODE_BLOCK_BORDER_RADIUS,
        padding: CODE_BLOCK_PADDING,
        opacity: containerOpacity,
        fontFamily: "'JetBrains Mono', 'Fira Code', 'Courier New', monospace",
        fontSize: CODE_FONT_SIZE,
        lineHeight: `${CODE_LINE_HEIGHT}px`,
        boxShadow: "0 4px 24px rgba(0,0,0,0.4)",
        border: "1px solid rgba(74, 144, 217, 0.2)",
      }}
    >
      {/* Line numbers gutter + code */}
      {VERILOG_LINES.map((line, lineIdx) => {
        const lineStart = charCount;
        const lineLen = line.length + (lineIdx < VERILOG_LINES.length - 1 ? 1 : 0); // +1 for newline
        charCount += lineLen;

        if (lineStart >= charsTyped) return null;

        const visibleChars = Math.min(charsTyped - lineStart, line.length);
        const visibleText = line.slice(0, visibleChars);
        const tokens = tokenizeLine(visibleText);

        return (
          <div key={lineIdx} style={{ display: "flex", minHeight: CODE_LINE_HEIGHT }}>
            {/* Line number */}
            <span
              style={{
                width: 36,
                textAlign: "right",
                paddingRight: 16,
                color: "#546E7A",
                userSelect: "none",
                flexShrink: 0,
                opacity: 0.6,
              }}
            >
              {lineIdx + 1}
            </span>
            {/* Code content */}
            <span style={{ whiteSpace: "pre" }}>
              {tokens.map((token, ti) => (
                <span key={ti} style={{ color: tokenColor(token.type) }}>
                  {token.text}
                </span>
              ))}
              {/* Cursor at typing position */}
              {visibleChars < line.length && visibleChars === charsTyped - lineStart && (
                <span
                  style={{
                    display: "inline-block",
                    width: 2,
                    height: CODE_FONT_SIZE,
                    backgroundColor: "#E2E8F0",
                    marginLeft: 1,
                    opacity: frame % 30 < 15 ? 1 : 0.3,
                  }}
                />
              )}
            </span>
          </div>
        );
      })}
      {/* Cursor at end */}
      {charsTyped >= totalChars && (
        <span
          style={{
            display: "inline-block",
            width: 2,
            height: CODE_FONT_SIZE,
            backgroundColor: "#E2E8F0",
            marginLeft: 1,
            opacity: frame % 30 < 15 ? 1 : 0.3,
            position: "relative",
            top: -CODE_LINE_HEIGHT,
            left: 52 + VERILOG_LINES[VERILOG_LINES.length - 1].length * (CODE_FONT_SIZE * 0.6),
          }}
        />
      )}
    </div>
  );
};

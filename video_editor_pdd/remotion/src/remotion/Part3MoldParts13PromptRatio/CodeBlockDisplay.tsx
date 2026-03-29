import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BLOCK_BG,
  CODE_BORDER,
  CODE_LABEL_COLOR,
  CODE_X,
  CODE_Y,
  CODE_WIDTH,
  CODE_HEIGHT,
  CODE_LINES,
  CODE_FADE_START,
  CODE_FADE_DUR,
  SYNTAX_COMMENT,
  SYNTAX_KEYWORD,
  SYNTAX_STRING,
  SYNTAX_NUMBER,
  SYNTAX_FUNCTION,
  SYNTAX_DEFAULT,
} from "./constants";

/**
 * Naive syntax highlight — returns a color for each code line token.
 */
function getLineColor(line: string): string {
  const trimmed = line.trim();
  if (trimmed.startsWith("//")) return SYNTAX_COMMENT;
  if (trimmed.startsWith("include")) return SYNTAX_KEYWORD;
  if (
    trimmed.startsWith("module ") ||
    trimmed.startsWith("for ") ||
    trimmed.startsWith("if ") ||
    trimmed.startsWith("let ") ||
    trimmed.startsWith("impl ")
  )
    return SYNTAX_KEYWORD;
  if (trimmed.includes('"')) return SYNTAX_STRING;
  if (/^\s*\d/.test(trimmed) || /=\s*\d/.test(trimmed)) return SYNTAX_NUMBER;
  if (/^\s*\w+\(/.test(trimmed) || trimmed.startsWith("fn "))
    return SYNTAX_FUNCTION;
  return SYNTAX_DEFAULT;
}

export const CodeBlockDisplay: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [CODE_FADE_START, CODE_FADE_START + CODE_FADE_DUR],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: CODE_X,
        top: CODE_Y,
        width: CODE_WIDTH,
        opacity,
      }}
    >
      {/* Label */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 600,
          color: CODE_LABEL_COLOR,
          marginBottom: 6,
        }}
      >
        Generated Code
      </div>

      {/* Code block */}
      <div
        style={{
          width: CODE_WIDTH,
          height: CODE_HEIGHT,
          backgroundColor: BLOCK_BG,
          border: `1px solid ${CODE_BORDER}`,
          borderRadius: 8,
          padding: 12,
          overflow: "hidden",
          boxSizing: "border-box",
          position: "relative",
        }}
      >
        {CODE_LINES.map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 10,
              lineHeight: "13px",
              color: getLineColor(line),
              whiteSpace: "pre",
              opacity: 0.85,
            }}
          >
            {line || "\u00A0"}
          </div>
        ))}

        {/* Overflow gradient indicating more code below */}
        <div
          style={{
            position: "absolute",
            bottom: 0,
            left: 0,
            right: 0,
            height: 60,
            background: `linear-gradient(transparent, ${BLOCK_BG})`,
            borderRadius: "0 0 8px 8px",
          }}
        />
      </div>

      {/* Badge */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 11,
          color: CODE_LABEL_COLOR,
          marginTop: 6,
        }}
      >
        ~200 lines
      </div>
    </div>
  );
};

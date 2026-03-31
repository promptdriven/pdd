import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CODE_FONT,
  CODE_FONT_SIZE,
  CODE_LINE_HEIGHT,
  GUTTER_WIDTH,
  COLOR_TEXT,
  COLOR_KEYWORD,
  COLOR_FUNCTION,
  COLOR_STRING,
  COLOR_COMMENT,
  COLOR_COMMENT_KEYWORD,
  COLOR_LINE_NUMBER,
  COLOR_GUTTER_MODIFIED,
  COLOR_GUTTER_ADDED,
  LINE_HIGHLIGHT_BG,
  PULSE_START,
  PULSE_CYCLE,
  type CodeLineData,
  type TokenType,
} from "./constants";

const TOKEN_COLOR_MAP: Record<TokenType, string> = {
  keyword: COLOR_KEYWORD,
  function: COLOR_FUNCTION,
  string: COLOR_STRING,
  comment: COLOR_COMMENT,
  commentKeyword: COLOR_COMMENT_KEYWORD,
  text: COLOR_TEXT,
  operator: COLOR_TEXT,
  number: "#FAB387",
  decorator: "#F9E2AF",
};

interface CodeLineProps {
  lineData: CodeLineData;
  lineNumber: number;
  isCurrentLine: boolean;
}

const CodeLine: React.FC<CodeLineProps> = ({
  lineData,
  lineNumber,
  isCurrentLine,
}) => {
  const frame = useCurrentFrame();

  // Pulse effect for HACK/TODO/PATCH comments
  let commentPulseOpacity = 1;
  if (lineData.isPatchComment && frame >= PULSE_START) {
    const pulseFrame = (frame - PULSE_START) % PULSE_CYCLE;
    commentPulseOpacity = interpolate(
      pulseFrame,
      [0, PULSE_CYCLE / 2, PULSE_CYCLE],
      [0.7, 1.0, 0.7],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
  }

  // Gutter mark symbol and color
  let gutterSymbol = " ";
  let gutterColor = "transparent";
  if (lineData.gutterMark === "modified") {
    gutterSymbol = "|";
    gutterColor = COLOR_GUTTER_MODIFIED;
  } else if (lineData.gutterMark === "added") {
    gutterSymbol = "+";
    gutterColor = COLOR_GUTTER_ADDED;
  }

  // Render tokens with syntax highlighting
  const renderTokens = () => {
    return lineData.tokens.map((token, i) => {
      // For comment tokens containing HACK/TODO/PATCH, highlight those keywords
      if (token.type === "comment" && lineData.isPatchComment) {
        const parts = token.text.split(/(HACK|TODO|PATCH)/g);
        return (
          <span key={i} style={{ opacity: commentPulseOpacity }}>
            {parts.map((part, j) => {
              const isKeyword = ["HACK", "TODO", "PATCH"].includes(part);
              return (
                <span
                  key={j}
                  style={{
                    color: isKeyword ? COLOR_COMMENT_KEYWORD : COLOR_COMMENT,
                    fontWeight: isKeyword ? 700 : 400,
                    textShadow: isKeyword
                      ? `0 0 8px ${COLOR_COMMENT_KEYWORD}40`
                      : "none",
                  }}
                >
                  {part}
                </span>
              );
            })}
          </span>
        );
      }

      return (
        <span
          key={i}
          style={{
            color: TOKEN_COLOR_MAP[token.type] || COLOR_TEXT,
          }}
        >
          {token.text}
        </span>
      );
    });
  };

  return (
    <div
      style={{
        display: "flex",
        height: CODE_LINE_HEIGHT,
        alignItems: "center",
        backgroundColor: isCurrentLine ? LINE_HIGHLIGHT_BG : "transparent",
        fontFamily: CODE_FONT,
        fontSize: CODE_FONT_SIZE,
        lineHeight: `${CODE_LINE_HEIGHT}px`,
        whiteSpace: "pre",
      }}
    >
      {/* Gutter mark */}
      <div
        style={{
          width: 16,
          textAlign: "center",
          color: gutterColor,
          fontSize: CODE_FONT_SIZE,
          fontWeight: 700,
          flexShrink: 0,
        }}
      >
        {gutterSymbol}
      </div>

      {/* Line number */}
      <div
        style={{
          width: GUTTER_WIDTH - 16,
          textAlign: "right",
          paddingRight: 16,
          color: COLOR_LINE_NUMBER,
          fontSize: CODE_FONT_SIZE,
          flexShrink: 0,
          userSelect: "none",
        }}
      >
        {lineNumber}
      </div>

      {/* Code content */}
      <div
        style={{
          flex: 1,
          paddingLeft: 16,
          overflow: "hidden",
        }}
      >
        {renderTokens()}
      </div>
    </div>
  );
};

export default CodeLine;

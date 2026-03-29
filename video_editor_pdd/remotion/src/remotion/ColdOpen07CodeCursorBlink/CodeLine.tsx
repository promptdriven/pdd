import React from "react";
import {
  CODE_FONT,
  CODE_FONT_SIZE,
  CODE_LEFT_PADDING,
  GUTTER_WIDTH,
  LINE_HEIGHT,
  LINE_NUMBER_COLOR,
  LINE_NUMBER_FONT_SIZE,
  TOP_PADDING,
  LINE_HIGHLIGHTS,
  PATCH_COMMENTS,
  getTokenColor,
  type CodeToken,
  type PatchAge,
} from "./constants";

interface CodeLineProps {
  lineNumber: number; // 1-based
  tokens: CodeToken[];
}

function getPatchLeftBorderStyle(lineNumber: number): React.CSSProperties | null {
  const highlight = LINE_HIGHLIGHTS.find((h) => h.line === lineNumber);
  if (!highlight) return null;
  return {
    borderLeft: `3px solid ${highlight.color}`,
    borderLeftColor: highlight.color,
    opacity: 1,
  };
}

function getPatchBorderOpacity(lineNumber: number): number {
  const patchComment = PATCH_COMMENTS.find((p) => p.line === lineNumber);
  if (!patchComment) return 0;
  const ageOpacity: Record<PatchAge, number> = {
    recent: 0.6,
    medium: 0.3,
    old: 0.15,
  };
  return ageOpacity[patchComment.age];
}

function getLineBgHighlight(lineNumber: number): string | null {
  const highlight = LINE_HIGHLIGHTS.find((h) => h.line === lineNumber);
  if (!highlight) return null;
  // Convert hex color to rgba with specified opacity
  const hex = highlight.color.replace("#", "");
  const r = parseInt(hex.substring(0, 2), 16);
  const g = parseInt(hex.substring(2, 4), 16);
  const b = parseInt(hex.substring(4, 6), 16);
  return `rgba(${r}, ${g}, ${b}, ${highlight.opacity})`;
}

export const CodeLine: React.FC<CodeLineProps> = ({ lineNumber, tokens }) => {
  const y = TOP_PADDING + (lineNumber - 1) * LINE_HEIGHT;
  const bgColor = getLineBgHighlight(lineNumber);
  const borderOpacity = getPatchBorderOpacity(lineNumber);
  const hasPatchBorder = borderOpacity > 0;
  const highlight = LINE_HIGHLIGHTS.find((h) => h.line === lineNumber);

  return (
    <div
      style={{
        position: "absolute",
        top: y,
        left: 0,
        width: "100%",
        height: LINE_HEIGHT,
        display: "flex",
        alignItems: "center",
        backgroundColor: bgColor || "transparent",
        borderLeft: hasPatchBorder
          ? `3px solid ${highlight?.color || "transparent"}`
          : "3px solid transparent",
        borderLeftColor: hasPatchBorder
          ? highlight?.color || "transparent"
          : "transparent",
        opacity: 1,
      }}
    >
      {/* Left border opacity overlay — applied separately for subtle effect */}
      {hasPatchBorder && (
        <div
          style={{
            position: "absolute",
            left: -3,
            top: 0,
            width: 3,
            height: LINE_HEIGHT,
            backgroundColor: highlight?.color || "transparent",
            opacity: borderOpacity,
          }}
        />
      )}

      {/* Line number */}
      <div
        style={{
          width: GUTTER_WIDTH,
          textAlign: "right",
          paddingRight: 12,
          fontFamily: CODE_FONT,
          fontSize: LINE_NUMBER_FONT_SIZE,
          color: LINE_NUMBER_COLOR,
          opacity: 0.5,
          flexShrink: 0,
          userSelect: "none",
        }}
      >
        {lineNumber}
      </div>

      {/* Code tokens */}
      <div
        style={{
          paddingLeft: CODE_LEFT_PADDING,
          fontFamily: CODE_FONT,
          fontSize: CODE_FONT_SIZE,
          whiteSpace: "pre",
          lineHeight: `${LINE_HEIGHT}px`,
        }}
      >
        {tokens.map((token, i) => {
          const isComment =
            token.type === "patch_comment" ||
            token.type === "todo_comment" ||
            token.type === "hotfix_comment" ||
            token.type === "comment";
          return (
            <span
              key={i}
              style={{
                color: getTokenColor(token.type),
                fontStyle: isComment ? "italic" : "normal",
              }}
            >
              {token.text}
            </span>
          );
        })}
      </div>
    </div>
  );
};

export default CodeLine;

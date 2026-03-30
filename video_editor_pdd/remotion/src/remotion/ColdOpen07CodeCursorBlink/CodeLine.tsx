import React from "react";
import {
  CodeLineData,
  PatchLineHighlight,
  LINE_HEIGHT,
  LINE_GUTTER_WIDTH,
  CODE_FONT_SIZE,
  LINE_NUMBER_FONT_SIZE,
  LINE_NUMBER_COLOR,
  CODE_FONT_FAMILY,
  CODE_PADDING_LEFT,
  EDITOR_PADDING_LEFT,
  PATCH_LINE_HIGHLIGHTS,
} from "./constants";

interface CodeLineProps {
  lineNumber: number; // 1-indexed
  spans: CodeLineData;
  topOffset: number;
}

/**
 * Renders a single line of the code editor: line number gutter +
 * syntax-highlighted code spans + optional patch-age left border.
 */
export const CodeLine: React.FC<CodeLineProps> = ({
  lineNumber,
  spans,
  topOffset,
}) => {
  // Look up patch highlight for this line
  const highlight: PatchLineHighlight | undefined = PATCH_LINE_HIGHLIGHTS.find(
    (h) => h.line === lineNumber
  );

  return (
    <div
      style={{
        position: "absolute",
        top: topOffset,
        left: EDITOR_PADDING_LEFT,
        right: 0,
        height: LINE_HEIGHT,
        display: "flex",
        alignItems: "center",
      }}
    >
      {/* Patch-age left border indicator */}
      {highlight && (
        <div
          style={{
            position: "absolute",
            left: 0,
            top: 0,
            width: 3,
            height: LINE_HEIGHT,
            backgroundColor: highlight.borderColor,
            opacity: highlight.borderOpacity,
            borderRadius: 1,
          }}
        />
      )}

      {/* Line number */}
      <div
        style={{
          width: LINE_GUTTER_WIDTH,
          textAlign: "right",
          paddingRight: 12,
          fontFamily: CODE_FONT_FAMILY,
          fontSize: LINE_NUMBER_FONT_SIZE,
          color: LINE_NUMBER_COLOR,
          opacity: 0.5,
          userSelect: "none",
          flexShrink: 0,
        }}
      >
        {lineNumber}
      </div>

      {/* Code content */}
      <div
        style={{
          paddingLeft: CODE_PADDING_LEFT,
          fontFamily: CODE_FONT_FAMILY,
          fontSize: CODE_FONT_SIZE,
          lineHeight: `${LINE_HEIGHT}px`,
          whiteSpace: "pre",
          overflow: "hidden",
        }}
      >
        {spans.map((span, i) => (
          <span
            key={i}
            style={{
              color: span.color,
              fontStyle: span.italic ? "italic" : "normal",
            }}
          >
            {span.text}
          </span>
        ))}
      </div>
    </div>
  );
};

export default CodeLine;

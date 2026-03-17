import React from "react";
import {
  INITIAL_CODE_BLOCK,
  SYNTAX_KEYWORD,
  SYNTAX_STRING,
  SYNTAX_FUNCTION,
  SYNTAX_OPERATOR,
  DIFF_GREEN,
} from "./constants";

/**
 * The single edited function visible before zoom-out begins.
 * Represents the "one clean edit" from the previous shot.
 */
export const InitialCodeBlock: React.FC = () => {
  const { width, height, bg, border } = INITIAL_CODE_BLOCK;
  const centerX = (958 - width) / 2;
  const centerY = (1080 - height) / 2;

  const lines: Array<{ tokens: Array<{ text: string; color: string }>; indent: number }> = [
    {
      indent: 0,
      tokens: [
        { text: "function ", color: SYNTAX_KEYWORD },
        { text: "validateUser", color: SYNTAX_FUNCTION },
        { text: "(input) {", color: SYNTAX_OPERATOR },
      ],
    },
    {
      indent: 1,
      tokens: [
        { text: "if ", color: SYNTAX_KEYWORD },
        { text: "(input.", color: SYNTAX_OPERATOR },
        { text: "role", color: "#E2E8F0" },
        { text: " === ", color: SYNTAX_OPERATOR },
        { text: "'admin'", color: SYNTAX_STRING },
        { text: ") {", color: SYNTAX_OPERATOR },
      ],
    },
    {
      indent: 2,
      tokens: [
        { text: "return ", color: SYNTAX_KEYWORD },
        { text: "authorize", color: SYNTAX_FUNCTION },
        { text: "(input);", color: SYNTAX_OPERATOR },
      ],
    },
    {
      indent: 1,
      tokens: [{ text: "}", color: SYNTAX_OPERATOR }],
    },
    {
      indent: 1,
      tokens: [
        { text: "// fixed null case", color: "#64748B" },
      ],
    },
    {
      indent: 1,
      tokens: [
        { text: "if ", color: SYNTAX_KEYWORD },
        { text: "(!input) ", color: SYNTAX_OPERATOR },
        { text: "return ", color: SYNTAX_KEYWORD },
        { text: "null", color: "#F472B6" },
        { text: ";", color: SYNTAX_OPERATOR },
      ],
    },
    {
      indent: 1,
      tokens: [
        { text: "return ", color: SYNTAX_KEYWORD },
        { text: "defaultAuth", color: SYNTAX_FUNCTION },
        { text: "(input);", color: SYNTAX_OPERATOR },
      ],
    },
    {
      indent: 0,
      tokens: [{ text: "}", color: SYNTAX_OPERATOR }],
    },
  ];

  return (
    <div
      style={{
        position: "absolute",
        left: centerX,
        top: centerY,
        width,
        height,
        backgroundColor: bg,
        border: `1px solid ${border}`,
        borderRadius: 6,
        padding: 16,
        fontFamily: "'JetBrains Mono', monospace",
        fontSize: 11,
        lineHeight: "18px",
        overflow: "hidden",
      }}
    >
      {/* Green diff bar on left */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: 4,
          height: "100%",
          backgroundColor: DIFF_GREEN,
          opacity: 0.7,
        }}
      />

      {/* Code lines */}
      {lines.map((line, i) => (
        <div key={i} style={{ paddingLeft: line.indent * 16 + 12 }}>
          {line.tokens.map((token, j) => (
            <span key={j} style={{ color: token.color }}>
              {token.text}
            </span>
          ))}
        </div>
      ))}
    </div>
  );
};

// CodePanel.tsx — Individual code editor panel sub-component
import React from "react";
import {
  PANEL_WIDTH,
  PANEL_HEIGHT,
  PANEL_BG,
  PANEL_BORDER,
  PANEL_BORDER_RADIUS,
  HEADER_FONT,
  CODE_FONT,
  HEADER_SIZE,
  CODE_SIZE,
  HEADER_COLOR,
  type CodeLine,
} from "./constants";

interface CodePanelProps {
  label: string;
  code: CodeLine[];
  borderColor?: string;
  borderGlow?: boolean;
  glowColor?: string;
}

export const CodePanel: React.FC<CodePanelProps> = ({
  label,
  code,
  borderColor = PANEL_BORDER,
  borderGlow = false,
  glowColor = "transparent",
}) => {
  return (
    <div
      style={{
        width: PANEL_WIDTH,
        height: PANEL_HEIGHT,
        backgroundColor: PANEL_BG,
        border: `1px solid ${borderColor}`,
        borderRadius: PANEL_BORDER_RADIUS,
        overflow: "hidden",
        position: "relative",
        boxShadow: borderGlow
          ? `0 0 12px ${glowColor}, 0 0 24px ${glowColor}40`
          : "none",
      }}
    >
      {/* Header badge */}
      <div
        style={{
          padding: "8px 12px",
          fontFamily: HEADER_FONT,
          fontSize: HEADER_SIZE,
          fontWeight: 600,
          color: HEADER_COLOR,
          borderBottom: `1px solid ${PANEL_BORDER}`,
        }}
      >
        {label}
      </div>

      {/* Code lines */}
      <div style={{ padding: "10px 12px" }}>
        {code.map((line, idx) => (
          <div
            key={idx}
            style={{
              fontFamily: CODE_FONT,
              fontSize: CODE_SIZE,
              lineHeight: "18px",
              color: line.color,
              paddingLeft: line.indent * 16,
              whiteSpace: "pre",
            }}
          >
            {line.text}
          </div>
        ))}
      </div>
    </div>
  );
};

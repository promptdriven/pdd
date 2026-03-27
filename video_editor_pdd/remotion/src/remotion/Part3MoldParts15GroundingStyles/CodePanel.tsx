import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PANEL_BG,
  PANEL_WIDTH,
  PANEL_HEIGHT,
  SYN_KEYWORD,
  SYN_STRING,
  SYN_TYPE,
  SYN_FUNCTION,
  SYN_DEFAULT,
  SYN_SELF,
  SYN_PAREN,
} from "./constants";

interface CodePanelProps {
  x: number;
  y: number;
  header: string;
  headerColor: string;
  borderColor: string;
  code: string;
  /** Frame (relative to parent Sequence) at which type-in starts */
  typeInStart: number;
  /** Frame at which both-valid glow starts */
  glowStart: number;
  /** Frame at which this panel's glow brightens (selected) */
  glowBrightStart?: number;
}

// Simple Python syntax highlighter
function highlightLine(line: string): React.ReactNode[] {
  const tokens: React.ReactNode[] = [];
  const keywords =
    /\b(class|def|return|if|in|from|import|self|lambda|Optional|Dict)\b/g;
  const strings = /(["'])(?:(?=(\\?))\2.)*?\1/g;
  const types = /\b(Config|User|str|int|bool)\b/g;
  const functions =
    /\b(parse|pipe|strip|split_on|head|validate_id|extract_name|map|__init__|_validate)\b/g;

  // Build a map of character positions to styles
  const charStyles: { color: string; bold?: boolean }[] = Array.from(
    { length: line.length },
    () => ({ color: SYN_DEFAULT })
  );

  // Apply keyword styling
  let match: RegExpExecArray | null;
  keywords.lastIndex = 0;
  while ((match = keywords.exec(line)) !== null) {
    const start = match.index;
    for (let i = 0; i < match[0].length; i++) {
      if (match[0] === "self") {
        charStyles[start + i] = { color: SYN_SELF };
      } else if (
        ["Optional", "Dict"].includes(match[0])
      ) {
        charStyles[start + i] = { color: SYN_TYPE };
      } else {
        charStyles[start + i] = { color: SYN_KEYWORD };
      }
    }
  }

  // Apply type styling
  types.lastIndex = 0;
  while ((match = types.exec(line)) !== null) {
    const start = match.index;
    for (let i = 0; i < match[0].length; i++) {
      charStyles[start + i] = { color: SYN_TYPE };
    }
  }

  // Apply function styling
  functions.lastIndex = 0;
  while ((match = functions.exec(line)) !== null) {
    const start = match.index;
    for (let i = 0; i < match[0].length; i++) {
      charStyles[start + i] = { color: SYN_FUNCTION };
    }
  }

  // Apply string styling
  strings.lastIndex = 0;
  while ((match = strings.exec(line)) !== null) {
    const start = match.index;
    for (let i = 0; i < match[0].length; i++) {
      charStyles[start + i] = { color: SYN_STRING };
    }
  }

  // Parentheses, brackets
  for (let i = 0; i < line.length; i++) {
    if ("()[]{}".includes(line[i]) && charStyles[i].color === SYN_DEFAULT) {
      charStyles[i] = { color: SYN_PAREN };
    }
  }

  // Group consecutive chars with same style into spans
  let currentColor = "";
  let currentText = "";
  for (let i = 0; i < line.length; i++) {
    const style = charStyles[i];
    if (style.color !== currentColor) {
      if (currentText) {
        tokens.push(
          <span key={`${i}-${currentColor}`} style={{ color: currentColor }}>
            {currentText}
          </span>
        );
      }
      currentColor = style.color;
      currentText = line[i];
    } else {
      currentText += line[i];
    }
  }
  if (currentText) {
    tokens.push(
      <span key={`end-${currentColor}`} style={{ color: currentColor }}>
        {currentText}
      </span>
    );
  }

  return tokens;
}

const CodePanel: React.FC<CodePanelProps> = ({
  x,
  y,
  header,
  headerColor,
  borderColor,
  code,
  typeInStart,
  glowStart,
  glowBrightStart,
}) => {
  const frame = useCurrentFrame();

  // Type-in effect: reveal characters over time (1 char per frame)
  const typeFrame = Math.max(0, frame - typeInStart);
  const totalChars = code.length;
  const visibleChars = Math.min(totalChars, typeFrame);
  const visibleCode = code.slice(0, visibleChars);
  const lines = visibleCode.split("\n");

  // Glow effect
  const glowFrame = Math.max(0, frame - glowStart);
  const glowOpacity = interpolate(glowFrame, [0, 20], [0, 0.6], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Bright glow for selected panel
  const brightGlowOpacity = glowBrightStart
    ? interpolate(
        Math.max(0, frame - glowBrightStart),
        [0, 20],
        [0, 0.4],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.quad),
        }
      )
    : 0;

  // Panel fade-in
  const panelOpacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        width: PANEL_WIDTH,
        height: PANEL_HEIGHT,
        opacity: panelOpacity,
      }}
    >
      {/* Glow shadow */}
      <div
        style={{
          position: "absolute",
          inset: -8,
          borderRadius: 12,
          boxShadow: `0 0 30px ${borderColor}`,
          opacity: glowOpacity + brightGlowOpacity,
          pointerEvents: "none",
        }}
      />
      {/* Panel body */}
      <div
        style={{
          width: PANEL_WIDTH,
          height: PANEL_HEIGHT,
          backgroundColor: PANEL_BG,
          border: `2px solid ${borderColor}`,
          borderRadius: 8,
          overflow: "hidden",
          display: "flex",
          flexDirection: "column",
        }}
      >
        {/* Header */}
        <div
          style={{
            padding: "10px 16px",
            borderBottom: `2px solid ${borderColor}B3`,
            fontFamily: "Inter, sans-serif",
            fontSize: 14,
            fontWeight: 600,
            color: headerColor,
          }}
        >
          {header}
        </div>
        {/* Code area */}
        <div
          style={{
            flex: 1,
            padding: "12px 16px",
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 11,
            lineHeight: 1.6,
            color: SYN_DEFAULT,
            whiteSpace: "pre",
            overflow: "hidden",
          }}
        >
          {lines.map((line, i) => (
            <div key={i}>{highlightLine(line)}</div>
          ))}
          {/* Cursor blink */}
          {visibleChars < totalChars && (
            <span
              style={{
                display: "inline-block",
                width: 6,
                height: 13,
                backgroundColor: headerColor,
                opacity: Math.sin(frame * 0.3) > 0 ? 0.8 : 0,
                verticalAlign: "middle",
                marginLeft: 1,
              }}
            />
          )}
        </div>
      </div>
      {/* "Valid" checkmark after glow */}
      {glowFrame > 10 && (
        <div
          style={{
            position: "absolute",
            bottom: -30,
            left: 0,
            right: 0,
            textAlign: "center",
            fontFamily: "Inter, sans-serif",
            fontSize: 13,
            fontWeight: 600,
            color: "#22C55E",
            opacity: interpolate(glowFrame, [10, 25], [0, 0.9], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }),
          }}
        >
          Valid
        </div>
      )}
    </div>
  );
};

export default CodePanel;

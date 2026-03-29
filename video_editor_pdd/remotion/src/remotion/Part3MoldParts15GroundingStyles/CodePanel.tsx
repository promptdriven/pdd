import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CODE_BG,
  SYNTAX_KEYWORD,
  SYNTAX_STRING,
  SYNTAX_FUNCTION,
  SYNTAX_TYPE,
  SYNTAX_PLAIN,
  SYNTAX_DECORATOR,
} from "./constants";

interface CodePanelProps {
  x: number;
  y: number;
  width: number;
  height: number;
  header: string;
  headerColor: string;
  borderColor: string;
  code: string;
  typeInStart: number;
  glowStart: number;
  glowEnd: number;
  selectGlowStart?: number;
  selectGlowEnd?: number;
  isSelected?: boolean;
  fadeInStart: number;
  fadeInEnd: number;
}

// Simple Python syntax highlighter
function highlightPython(line: string): React.ReactNode[] {
  const tokens: React.ReactNode[] = [];
  const keywords =
    /\b(class|def|if|else|return|import|from|for|in|not|and|or|self|None|True|False|raise|as|with)\b/g;
  const types = /\b(str|dict|int|float|bool|list|Optional|Result|Config|User|Ok|Err)\b/g;
  const strings = /(["'])(?:(?!\1).)*?\1/g;
  const functions = /\b([a-zA-Z_]\w*)\s*(?=\()/g;

  // Build a simple token map
  const charColors: string[] = new Array(line.length).fill(SYNTAX_PLAIN);

  // Mark keywords
  let match: RegExpExecArray | null;
  keywords.lastIndex = 0;
  while ((match = keywords.exec(line)) !== null) {
    for (let i = match.index; i < match.index + match[0].length; i++) {
      charColors[i] = SYNTAX_KEYWORD;
    }
  }

  // Mark types
  types.lastIndex = 0;
  while ((match = types.exec(line)) !== null) {
    for (let i = match.index; i < match.index + match[0].length; i++) {
      charColors[i] = SYNTAX_TYPE;
    }
  }

  // Mark strings
  strings.lastIndex = 0;
  while ((match = strings.exec(line)) !== null) {
    for (let i = match.index; i < match.index + match[0].length; i++) {
      charColors[i] = SYNTAX_STRING;
    }
  }

  // Mark function calls (after keywords so keywords override)
  functions.lastIndex = 0;
  while ((match = functions.exec(line)) !== null) {
    const name = match[1];
    // Don't color keywords as functions
    if (
      [
        "class",
        "def",
        "if",
        "else",
        "return",
        "import",
        "from",
        "for",
        "in",
        "not",
        "self",
        "raise",
      ].includes(name)
    )
      continue;
    const start = match.index;
    for (let i = start; i < start + name.length; i++) {
      if (charColors[i] === SYNTAX_PLAIN) {
        charColors[i] = SYNTAX_FUNCTION;
      }
    }
  }

  // Mark decorators
  if (line.trimStart().startsWith("@")) {
    const idx = line.indexOf("@");
    for (let i = idx; i < line.length; i++) {
      charColors[i] = SYNTAX_DECORATOR;
    }
  }

  // Collapse consecutive chars of the same color into spans
  let currentColor = charColors[0] || SYNTAX_PLAIN;
  let currentText = "";
  for (let i = 0; i < line.length; i++) {
    if (charColors[i] === currentColor) {
      currentText += line[i];
    } else {
      if (currentText) {
        tokens.push(
          <span key={`${i}-${currentText}`} style={{ color: currentColor }}>
            {currentText}
          </span>
        );
      }
      currentColor = charColors[i];
      currentText = line[i];
    }
  }
  if (currentText) {
    tokens.push(
      <span key={`end-${currentText}`} style={{ color: currentColor }}>
        {currentText}
      </span>
    );
  }

  return tokens;
}

const CodePanel: React.FC<CodePanelProps> = ({
  x,
  y,
  width,
  height,
  header,
  headerColor,
  borderColor,
  code,
  typeInStart,
  glowStart,
  glowEnd,
  selectGlowStart,
  selectGlowEnd,
  isSelected = false,
  fadeInStart,
  fadeInEnd,
}) => {
  const frame = useCurrentFrame();

  // Fade in the panel
  const panelOpacity = interpolate(
    frame,
    [fadeInStart, fadeInEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Type-in effect: reveal characters over time (1 char per frame)
  const totalChars = code.length;
  const charsVisible = Math.min(
    totalChars,
    Math.max(0, frame - typeInStart)
  );
  const visibleCode = code.substring(0, charsVisible);

  // Both-valid glow
  const bothGlow = interpolate(
    frame,
    [glowStart, glowStart + 20, glowEnd],
    [0, 1, 0.4],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Selected glow (right panel glows brighter)
  const selectGlow =
    isSelected && selectGlowStart !== undefined && selectGlowEnd !== undefined
      ? interpolate(
          frame,
          [selectGlowStart, selectGlowStart + 20, selectGlowEnd],
          [0.4, 1, 0.8],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.quad),
          }
        )
      : 0;

  const glowIntensity = Math.max(bothGlow, selectGlow);

  const lines = visibleCode.split("\n");

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        width,
        height,
        opacity: panelOpacity,
        borderRadius: 8,
        border: `2px solid ${borderColor}`,
        backgroundColor: CODE_BG,
        boxShadow:
          glowIntensity > 0
            ? `0 0 ${20 * glowIntensity}px ${borderColor}${Math.round(glowIntensity * 80)
                .toString(16)
                .padStart(2, "0")}, inset 0 0 ${10 * glowIntensity}px ${borderColor}20`
            : "none",
        overflow: "hidden",
        display: "flex",
        flexDirection: "column",
      }}
    >
      {/* Header bar */}
      <div
        style={{
          padding: "10px 16px",
          borderBottom: `1px solid ${borderColor}40`,
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
          whiteSpace: "pre",
          overflow: "hidden",
        }}
      >
        {lines.map((line, i) => (
          <div key={i}>{highlightPython(line)}</div>
        ))}
        {/* Blinking cursor during typing */}
        {charsVisible < totalChars && charsVisible > 0 && (
          <span
            style={{
              display: "inline-block",
              width: 6,
              height: 13,
              backgroundColor: headerColor,
              opacity: Math.sin(frame * 0.3) > 0 ? 0.8 : 0,
              marginLeft: 1,
              verticalAlign: "middle",
            }}
          />
        )}
      </div>

      {/* "Pass" indicator during glow phase */}
      {glowIntensity > 0.3 && (
        <div
          style={{
            position: "absolute",
            bottom: 12,
            right: 16,
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 11,
            fontWeight: 600,
            color: "#22C55E",
            opacity: interpolate(glowIntensity, [0.3, 0.8], [0, 1], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }),
          }}
        >
          TESTS PASS
        </div>
      )}
    </div>
  );
};

export default CodePanel;

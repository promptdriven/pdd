import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  GUTTER_BG,
  LINE_NUM_COLOR,
  PROMPT_TYPE_START,
  CODE_APPEAR_START,
  CODE_APPEAR_END,
  CODE_SCROLL_START,
  FADEOUT_END,
} from "./constants";

interface CodePanelProps {
  lines: string[];
  variant: "prompt" | "code";
  keywordColor: string;
  stringColor: string;
}

const GUTTER_WIDTH = 44;
const LINE_HEIGHT = 22;
const CODE_FONT_SIZE = 14;

/** Simple syntax-ish coloring: keywords get keywordColor, strings get stringColor */
function colorize(
  line: string,
  keywordColor: string,
  stringColor: string
): React.ReactNode[] {
  const keywords = [
    "import", "from", "export", "const", "let", "function", "return",
    "async", "await", "if", "interface", "new", "router", "purpose",
    "validate", "on_login", "on_failure", "store", "expose", "test",
  ];

  const parts: React.ReactNode[] = [];
  // Match quoted strings, keywords, or other tokens
  const regex = /("(?:[^"\\]|\\.)*"|'(?:[^'\\]|\\.)*'|\b\w+\b|[^\s\w]+|\s+)/g;
  let match: RegExpExecArray | null;
  let idx = 0;

  while ((match = regex.exec(line)) !== null) {
    const token = match[0];
    if (token.startsWith('"') || token.startsWith("'")) {
      parts.push(
        <span key={idx} style={{ color: stringColor }}>
          {token}
        </span>
      );
    } else if (keywords.includes(token)) {
      parts.push(
        <span key={idx} style={{ color: keywordColor, fontWeight: 600 }}>
          {token}
        </span>
      );
    } else if (token.startsWith("#")) {
      parts.push(
        <span key={idx} style={{ color: keywordColor, fontWeight: 700 }}>
          {token}
        </span>
      );
    } else {
      parts.push(
        <span key={idx} style={{ color: "rgba(226, 232, 240, 0.85)" }}>
          {token}
        </span>
      );
    }
    idx++;
  }

  return parts;
}

export const CodePanel: React.FC<CodePanelProps> = ({
  lines,
  variant,
  keywordColor,
  stringColor,
}) => {
  const frame = useCurrentFrame();

  // For prompt: type in character by character
  // For code: reveal lines progressively
  const isPrompt = variant === "prompt";

  const totalChars = lines.join("\n").length;
  const charsPerFrame = 2;
  const charsVisible = isPrompt
    ? Math.floor(
        interpolate(
          frame,
          [PROMPT_TYPE_START, PROMPT_TYPE_START + totalChars / charsPerFrame],
          [0, totalChars],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
        )
      )
    : totalChars;

  // For code panel: line reveal progress
  const codeLinesVisible = !isPrompt
    ? Math.floor(
        interpolate(
          frame,
          [CODE_APPEAR_START, CODE_APPEAR_END],
          [0, lines.length],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
        )
      )
    : lines.length;

  // Auto-scroll for code panel
  const scrollOffset = !isPrompt
    ? interpolate(
        frame,
        [CODE_SCROLL_START, FADEOUT_END],
        [0, Math.max(0, lines.length * LINE_HEIGHT - 800)],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.linear,
        }
      )
    : 0;

  // Build visible lines for prompt (char-by-char typing)
  const getPromptVisibleLines = (): { text: string; lineNum: number }[] => {
    const result: { text: string; lineNum: number }[] = [];
    let remaining = charsVisible;
    for (let i = 0; i < lines.length && remaining > 0; i++) {
      const line = lines[i];
      const visibleLen = Math.min(remaining, line.length);
      result.push({ text: line.substring(0, visibleLen), lineNum: i + 1 });
      remaining -= line.length + 1; // +1 for newline
    }
    return result;
  };

  const visibleLines = isPrompt
    ? getPromptVisibleLines()
    : lines.slice(0, codeLinesVisible).map((text, i) => ({
        text,
        lineNum: i + 1,
      }));

  return (
    <div
      style={{
        width: "100%",
        height: "100%",
        overflow: "hidden",
        display: "flex",
        flexDirection: "row",
      }}
    >
      {/* Line number gutter */}
      <div
        style={{
          width: GUTTER_WIDTH,
          minWidth: GUTTER_WIDTH,
          backgroundColor: GUTTER_BG,
          borderRight: "1px solid rgba(148, 163, 184, 0.1)",
          paddingTop: 8,
          overflow: "hidden",
        }}
      >
        <div style={{ transform: `translateY(${-scrollOffset}px)` }}>
          {visibleLines.map((l) => (
            <div
              key={l.lineNum}
              style={{
                height: LINE_HEIGHT,
                lineHeight: `${LINE_HEIGHT}px`,
                fontFamily: "JetBrains Mono, monospace",
                fontSize: 12,
                color: LINE_NUM_COLOR,
                textAlign: "right",
                paddingRight: 8,
              }}
            >
              {l.lineNum}
            </div>
          ))}
        </div>
      </div>

      {/* Code content */}
      <div
        style={{
          flex: 1,
          paddingTop: 8,
          paddingLeft: 12,
          paddingRight: 8,
          overflow: "hidden",
        }}
      >
        <div style={{ transform: `translateY(${-scrollOffset}px)` }}>
          {visibleLines.map((l) => (
            <div
              key={l.lineNum}
              style={{
                height: LINE_HEIGHT,
                lineHeight: `${LINE_HEIGHT}px`,
                fontFamily: "JetBrains Mono, monospace",
                fontSize: CODE_FONT_SIZE,
                whiteSpace: "pre",
              }}
            >
              {l.text.length > 0
                ? colorize(l.text, keywordColor, stringColor)
                : "\u00A0"}
            </div>
          ))}
        </div>
      </div>
    </div>
  );
};

export default CodePanel;

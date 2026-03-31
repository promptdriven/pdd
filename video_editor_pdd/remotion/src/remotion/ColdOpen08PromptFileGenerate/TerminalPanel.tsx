import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  PANEL_BG,
  PANEL_BORDER,
  TEXT_MUTED,
  TEXT_DIM,
  ACCENT_GREEN,
  BRIGHT_GREEN,
  MONO_FONT,
  TERMINAL_PANEL,
  TERMINAL_START,
  TERMINAL_FADE_END,
  CMD_START,
  CMD_TEXT,
  CMD_FRAMES_PER_CHAR,
  CODE_STREAM_START,
  CODE_STREAM_END,
  RESULT_START,
  TOTAL_CODE_LINES,
  PYTHON_CODE_LINES,
  SYN_KEYWORD,
  SYN_STRING,
  SYN_COMMENT,
  SYN_BUILTIN,
  SYN_DECORATOR,
  SYN_NUMBER,
  SYN_OPERATOR,
  SYN_DEFAULT,
} from "./constants";

// ── Syntax highlighting ─────────────────────────────────────────────
interface TokenSpan {
  text: string;
  color: string;
}

const KEYWORDS = new Set([
  "import",
  "from",
  "class",
  "def",
  "return",
  "if",
  "else",
  "elif",
  "try",
  "except",
  "for",
  "in",
  "not",
  "and",
  "or",
  "with",
  "as",
  "while",
  "None",
  "True",
  "False",
  "self",
]);

const BUILTINS = new Set([
  "print",
  "len",
  "sum",
  "str",
  "int",
  "float",
  "bool",
  "list",
  "dict",
  "open",
  "range",
  "round",
  "type",
]);

function highlightLine(line: string): TokenSpan[] {
  if (!line.trim()) return [{ text: line || " ", color: SYN_DEFAULT }];

  // Comments
  if (line.trimStart().startsWith("#")) {
    return [{ text: line, color: SYN_COMMENT }];
  }

  // Decorators
  if (line.trimStart().startsWith("@")) {
    return [{ text: line, color: SYN_DECORATOR }];
  }

  // Docstrings
  if (line.trimStart().startsWith('"""') || line.trimStart().startsWith("'''")) {
    return [{ text: line, color: SYN_STRING }];
  }

  const spans: TokenSpan[] = [];
  // Simple token-based highlighting
  const regex = /(""".*?"""|'''.*?'''|".*?"|'.*?'|#.*$|\b\d+(?:\.\d+)?\b|[a-zA-Z_]\w*|[^\s\w]+|\s+)/g;
  let match: RegExpExecArray | null;

  while ((match = regex.exec(line)) !== null) {
    const token = match[0];

    if (token.startsWith("#")) {
      spans.push({ text: token, color: SYN_COMMENT });
    } else if (
      (token.startsWith('"') && token.endsWith('"')) ||
      (token.startsWith("'") && token.endsWith("'"))
    ) {
      spans.push({ text: token, color: SYN_STRING });
    } else if (/^\d+(?:\.\d+)?$/.test(token)) {
      spans.push({ text: token, color: SYN_NUMBER });
    } else if (KEYWORDS.has(token)) {
      spans.push({ text: token, color: SYN_KEYWORD });
    } else if (BUILTINS.has(token)) {
      spans.push({ text: token, color: SYN_BUILTIN });
    } else if (/^[^\s\w]+$/.test(token)) {
      spans.push({ text: token, color: SYN_OPERATOR });
    } else {
      spans.push({ text: token, color: SYN_DEFAULT });
    }
  }

  return spans.length > 0 ? spans : [{ text: line, color: SYN_DEFAULT }];
}

// ── Component ───────────────────────────────────────────────────────
export const TerminalPanel: React.FC = () => {
  const frame = useCurrentFrame();

  // Panel fade-in
  const localFadeStart = TERMINAL_START;
  const fadeDuration = TERMINAL_FADE_END - TERMINAL_START;

  if (frame < localFadeStart) return null;

  const panelOpacity = interpolate(
    frame,
    [localFadeStart, localFadeStart + fadeDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const panelTranslateY = interpolate(
    frame,
    [localFadeStart, localFadeStart + fadeDuration],
    [12, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Command typing
  const cmdLength = CMD_TEXT.length;
  const cmdEndFrame = CMD_START + cmdLength * CMD_FRAMES_PER_CHAR;
  const charsVisible =
    frame < CMD_START
      ? 0
      : Math.min(
          Math.floor((frame - CMD_START) / CMD_FRAMES_PER_CHAR),
          cmdLength
        );
  const cmdDisplayed = CMD_TEXT.slice(0, charsVisible);
  const showCursor = frame >= CMD_START && frame < CODE_STREAM_START;

  // Code streaming
  const codeStreamDuration = CODE_STREAM_END - CODE_STREAM_START;
  const linesVisible =
    frame < CODE_STREAM_START
      ? 0
      : Math.min(
          Math.floor(
            interpolate(
              frame,
              [CODE_STREAM_START, CODE_STREAM_END],
              [0, TOTAL_CODE_LINES],
              {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              }
            )
          ),
          TOTAL_CODE_LINES
        );

  // Line counter
  const showResult = frame >= RESULT_START;
  const lineCounterValue = showResult ? TOTAL_CODE_LINES : linesVisible;

  // Checkmark animation
  const checkOpacity = showResult
    ? interpolate(frame, [RESULT_START, RESULT_START + 10], [0, 1], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.poly(4)),
      })
    : 0;

  const checkScale = showResult
    ? interpolate(frame, [RESULT_START, RESULT_START + 10], [0.3, 1], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.back(1.7)),
      })
    : 0;

  // Visible code lines — auto-scroll to keep latest visible
  const maxVisibleLines = 42;
  const visibleCodeLines = PYTHON_CODE_LINES.slice(0, linesVisible);
  const scrollOffset =
    linesVisible > maxVisibleLines ? linesVisible - maxVisibleLines : 0;
  const displayedLines = visibleCodeLines.slice(scrollOffset);

  return (
    <div
      style={{
        position: "absolute",
        left: TERMINAL_PANEL.x,
        top: TERMINAL_PANEL.y,
        width: TERMINAL_PANEL.width,
        height: TERMINAL_PANEL.height,
        opacity: panelOpacity,
        transform: `translateY(${panelTranslateY}px)`,
      }}
    >
      {/* Terminal chrome */}
      <div
        style={{
          background: PANEL_BG,
          borderRadius: 8,
          border: `1px solid ${PANEL_BORDER}`,
          height: "100%",
          display: "flex",
          flexDirection: "column",
          overflow: "hidden",
        }}
      >
        {/* Title bar */}
        <div
          style={{
            padding: "8px 14px",
            borderBottom: `1px solid ${PANEL_BORDER}`,
            display: "flex",
            alignItems: "center",
            gap: 6,
          }}
        >
          <div
            style={{
              width: 10,
              height: 10,
              borderRadius: "50%",
              background: "#FF5F57",
            }}
          />
          <div
            style={{
              width: 10,
              height: 10,
              borderRadius: "50%",
              background: "#FEBC2E",
            }}
          />
          <div
            style={{
              width: 10,
              height: 10,
              borderRadius: "50%",
              background: "#28C840",
            }}
          />
          <span
            style={{
              fontFamily: MONO_FONT,
              fontSize: 11,
              color: TEXT_DIM,
              marginLeft: 8,
            }}
          >
            terminal
          </span>
        </div>

        {/* Content area */}
        <div
          style={{
            flex: 1,
            padding: "12px 16px",
            overflow: "hidden",
            position: "relative",
          }}
        >
          {/* Command line */}
          <div
            style={{
              fontFamily: MONO_FONT,
              fontSize: 14,
              color: TEXT_MUTED,
              lineHeight: "22px",
              marginBottom: 8,
              whiteSpace: "pre",
            }}
          >
            {cmdDisplayed}
            {showCursor && (
              <span
                style={{
                  display: "inline-block",
                  width: 8,
                  height: 16,
                  background: TEXT_MUTED,
                  opacity: frame % 30 < 15 ? 0.8 : 0,
                  verticalAlign: "middle",
                  marginLeft: 1,
                }}
              />
            )}
          </div>

          {/* Separator after command completes */}
          {frame >= CODE_STREAM_START && (
            <div
              style={{
                height: 2,
                background: PANEL_BORDER,
                marginBottom: 8,
                opacity: 0.7,
              }}
            />
          )}

          {/* Code stream */}
          {linesVisible > 0 && (
            <div
              style={{
                fontFamily: MONO_FONT,
                fontSize: 11,
                lineHeight: "18px",
                overflow: "hidden",
              }}
            >
              {displayedLines.map((line, i) => {
                const lineNum = scrollOffset + i + 1;
                const spans = highlightLine(line);
                return (
                  <div
                    key={lineNum}
                    style={{
                      display: "flex",
                      whiteSpace: "pre",
                    }}
                  >
                    <span
                      style={{
                        color: TEXT_DIM,
                        width: 36,
                        textAlign: "right",
                        marginRight: 12,
                        userSelect: "none",
                        flexShrink: 0,
                        opacity: 0.5,
                      }}
                    >
                      {lineNum}
                    </span>
                    <span>
                      {spans.map((s, j) => (
                        <span key={j} style={{ color: s.color }}>
                          {s.text}
                        </span>
                      ))}
                    </span>
                  </div>
                );
              })}
            </div>
          )}

          {/* Checkmark after command (appears at result) */}
          {showResult && frame >= CMD_START && (
            <div
              style={{
                position: "absolute",
                top: 12,
                right: 16,
                display: "flex",
                alignItems: "center",
                gap: 6,
                opacity: checkOpacity,
                transform: `scale(${checkScale})`,
              }}
            >
              <svg width="18" height="18" viewBox="0 0 18 18" fill="none">
                <circle cx="9" cy="9" r="9" fill={BRIGHT_GREEN} fillOpacity={0.15} />
                <path
                  d="M5 9.5L7.5 12L13 6.5"
                  stroke={ACCENT_GREEN}
                  strokeWidth={2}
                  strokeLinecap="round"
                  strokeLinejoin="round"
                />
              </svg>
              <span
                style={{
                  fontFamily: MONO_FONT,
                  fontSize: 11,
                  color: ACCENT_GREEN,
                }}
              >
                done
              </span>
            </div>
          )}

          {/* Line counter — bottom-right */}
          {linesVisible > 0 && (
            <div
              style={{
                position: "absolute",
                bottom: 12,
                right: 16,
                fontFamily: MONO_FONT,
                fontSize: 11,
                color: TEXT_DIM,
              }}
            >
              {lineCounterValue} lines
            </div>
          )}
        </div>
      </div>
    </div>
  );
};

export default TerminalPanel;

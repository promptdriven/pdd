import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  FPS,
  BG_COLOR,
  GUTTER_BG,
  GUTTER_WIDTH,
  TITLE_BAR_BG,
  TITLE_BAR_HEIGHT,
  TAB_BAR_HEIGHT,
  COLOR_TEXT,
  COLOR_FUNCTION,
  CODE_FONT,
  CODE_FONT_SIZE,
  CODE_LINE_HEIGHT,
  CURSOR_COLOR,
  CURSOR_WIDTH,
  CURSOR_HEIGHT,
  CURSOR_BLINK_MS,
  FADE_IN_END,
  SCROLL_START,
  SCROLL_END,
  PRE_FADE_START,
  PRE_FADE_END,
  SCROLL_PIXELS,
  PULSE_START,
  PULSE_CYCLE,
  COLOR_COMMENT,
  COLOR_COMMENT_KEYWORD,
  COLOR_KEYWORD,
  COLOR_STRING,
  COLOR_LINE_NUMBER,
  COLOR_GUTTER_MODIFIED,
  COLOR_GUTTER_ADDED,
  LINE_HIGHLIGHT_BG,
  CODE_LINES,
  type TokenType,
} from "./constants";

// ── Default props ──
export const defaultColdOpen05CodeCursorBlinkProps = {};

// ── Token color map ──
const TOKEN_COLORS: Record<TokenType, string> = {
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

// ── Inline sub-components ──

const TitleBar: React.FC = () => (
  <div
    style={{
      position: "absolute",
      top: 0,
      left: 0,
      width: "100%",
      height: TITLE_BAR_HEIGHT,
      backgroundColor: TITLE_BAR_BG,
      display: "flex",
      alignItems: "center",
      paddingLeft: 16,
      zIndex: 5,
    }}
  >
    {/* Window buttons */}
    <div style={{ display: "flex", gap: 8, marginRight: 16 }}>
      {["#ED6A5E", "#F4BF4F", "#61C554"].map((color) => (
        <div
          key={color}
          style={{
            width: 12,
            height: 12,
            borderRadius: "50%",
            backgroundColor: color,
          }}
        />
      ))}
    </div>
    <span
      style={{
        fontFamily: "Inter, sans-serif",
        fontSize: 13,
        color: COLOR_TEXT,
        opacity: 0.8,
      }}
    >
      process_order.py
    </span>
  </div>
);

const TabBar: React.FC = () => (
  <div
    style={{
      position: "absolute",
      top: TITLE_BAR_HEIGHT,
      left: 0,
      width: "100%",
      height: TAB_BAR_HEIGHT,
      backgroundColor: TITLE_BAR_BG,
      display: "flex",
      alignItems: "center",
      borderBottom: "1px solid #313244",
      zIndex: 5,
    }}
  >
    {/* Active tab */}
    <div
      style={{
        display: "flex",
        alignItems: "center",
        gap: 8,
        padding: "0 16px",
        height: "100%",
        backgroundColor: BG_COLOR,
        borderTop: "2px solid #89B4FA",
        fontFamily: "Inter, sans-serif",
        fontSize: 13,
        color: COLOR_TEXT,
      }}
    >
      {/* Modified dot */}
      <div
        style={{
          width: 8,
          height: 8,
          borderRadius: "50%",
          backgroundColor: COLOR_TEXT,
          opacity: 0.6,
        }}
      />
      process_order.py
    </div>
  </div>
);

// ── Render a single code token ──
const renderToken = (
  token: { text: string; type: TokenType },
  isPatch: boolean,
  pulseOpacity: number,
  idx: number
) => {
  if (token.type === "comment" && isPatch) {
    const parts = token.text.split(/(HACK|TODO|PATCH)/g);
    return (
      <span key={idx} style={{ opacity: pulseOpacity }}>
        {parts.map((part, j) => {
          const isKw = ["HACK", "TODO", "PATCH"].includes(part);
          return (
            <span
              key={j}
              style={{
                color: isKw ? COLOR_COMMENT_KEYWORD : COLOR_COMMENT,
                fontWeight: isKw ? 700 : 400,
                textShadow: isKw
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
    <span key={idx} style={{ color: TOKEN_COLORS[token.type] || COLOR_TEXT }}>
      {token.text}
    </span>
  );
};

// ── Main Component ──
export const ColdOpen05CodeCursorBlink: React.FC = () => {
  const frame = useCurrentFrame();

  // 1. Fade-in (frames 0–15): opacity 0 → 1
  const fadeInOpacity = interpolate(frame, [0, FADE_IN_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // 2. Code scroll (frames 15–90): translateY 0 → -SCROLL_PIXELS
  const scrollOffset = interpolate(
    frame,
    [SCROLL_START, SCROLL_END],
    [0, SCROLL_PIXELS],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // 3. Pre-fade (frames 150–210): opacity 1.0 → 0.85
  const preFadeOpacity = interpolate(
    frame,
    [PRE_FADE_START, PRE_FADE_END],
    [1.0, 0.85],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  // 4. Cursor blink
  const blinkCycleFrames = (CURSOR_BLINK_MS * 2 * FPS) / 1000;
  const blinkOnFrames = (CURSOR_BLINK_MS * FPS) / 1000;
  const cursorVisible = (frame % blinkCycleFrames) < blinkOnFrames;

  // 5. Comment pulse opacity
  const getPulseOpacity = (): number => {
    if (frame < PULSE_START) return 1;
    const pulseFrame = (frame - PULSE_START) % PULSE_CYCLE;
    return interpolate(
      pulseFrame,
      [0, PULSE_CYCLE / 2, PULSE_CYCLE],
      [0.7, 1.0, 0.7],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
  };
  const pulseOpacity = getPulseOpacity();

  // Code area dimensions
  const codeAreaTop = TITLE_BAR_HEIGHT + TAB_BAR_HEIGHT;

  // Cursor position — at line 1, after function signature
  const cursorCharOffset = 44; // approx chars in "def process_order(order, user, config):"
  const cursorLeft = GUTTER_WIDTH + 16 + CODE_FONT_SIZE * 0.6 * cursorCharOffset;
  const cursorTop = codeAreaTop + 8 - scrollOffset;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        opacity: fadeInOpacity * preFadeOpacity,
        overflow: "hidden",
      }}
    >
      {/* Title bar */}
      <TitleBar />

      {/* Tab bar */}
      <TabBar />

      {/* Gutter background */}
      <div
        style={{
          position: "absolute",
          top: codeAreaTop,
          left: 0,
          width: GUTTER_WIDTH,
          height: 1080 - codeAreaTop,
          backgroundColor: GUTTER_BG,
          zIndex: 2,
        }}
      />

      {/* Code lines container — scrolls */}
      <div
        style={{
          position: "absolute",
          top: codeAreaTop + 8,
          left: 0,
          width: "100%",
          transform: `translateY(${-scrollOffset}px)`,
          zIndex: 1,
        }}
      >
        {CODE_LINES.map((lineData, i) => {
          const lineNumber = i + 1;
          const isCurrentLine = i === 0;

          // Gutter mark
          let gutterSymbol = " ";
          let gutterColor = "transparent";
          if (lineData.gutterMark === "modified") {
            gutterSymbol = "|";
            gutterColor = COLOR_GUTTER_MODIFIED;
          } else if (lineData.gutterMark === "added") {
            gutterSymbol = "+";
            gutterColor = COLOR_GUTTER_ADDED;
          }

          return (
            <div
              key={i}
              style={{
                display: "flex",
                height: CODE_LINE_HEIGHT,
                alignItems: "center",
                backgroundColor: isCurrentLine
                  ? LINE_HIGHLIGHT_BG
                  : "transparent",
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

              {/* Code tokens */}
              <div style={{ flex: 1, paddingLeft: 16, overflow: "hidden" }}>
                {lineData.tokens.map((token, j) =>
                  renderToken(
                    token,
                    !!lineData.isPatchComment,
                    pulseOpacity,
                    j
                  )
                )}
              </div>
            </div>
          );
        })}
      </div>

      {/* Blinking cursor */}
      <div
        style={{
          position: "absolute",
          left: cursorLeft,
          top: cursorTop,
          width: CURSOR_WIDTH,
          height: CURSOR_HEIGHT,
          backgroundColor: CURSOR_COLOR,
          opacity: cursorVisible ? 1 : 0,
          zIndex: 10,
        }}
      />
    </AbsoluteFill>
  );
};

export default ColdOpen05CodeCursorBlink;

import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  AMBER,
  RED,
  GREEN,
  CODE_MUTED,
  FONT_CODE,
  FONT_UI,
  PANEL_PADDING,
  WINDOW_TOP,
  WINDOW_HEIGHT,
  PANEL_WIDTH,
  LEFT_CODE_START,
  LEFT_CODE_END,
  LEFT_HIGHLIGHT_START,
  LEFT_HIGHLIGHT_STAGGER,
  TOKEN_COUNT_START,
  TOKEN_COUNT_END,
  FILL_BAR_START,
  FILL_BAR_END,
  PULSE_CYCLE,
  PULSE_MIN,
  PULSE_MAX,
  CODE_LINES,
  IRRELEVANT_RANGES,
  RELEVANT_RANGE,
} from "./constants";

const LINE_HEIGHT = 10;
const CODE_X = PANEL_PADDING + 12;
const CODE_Y_START = WINDOW_TOP + 20;
const WINDOW_X = PANEL_PADDING;
const WINDOW_WIDTH = PANEL_WIDTH - PANEL_PADDING * 2;

export const LeftPanel: React.FC = () => {
  const frame = useCurrentFrame();

  // Code fill progress
  const codeFill = interpolate(
    frame,
    [LEFT_CODE_START, LEFT_CODE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  const visibleLines = Math.floor(codeFill * CODE_LINES.length);

  // Token count opacity
  const tokenOpacity = interpolate(
    frame,
    [TOKEN_COUNT_START, TOKEN_COUNT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Fill bar width
  const fillBarProgress = interpolate(
    frame,
    [FILL_BAR_START, FILL_BAR_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Red highlight pulse (after frame 360)
  const pulsePhase = frame > 360
    ? interpolate(
        frame % PULSE_CYCLE,
        [0, PULSE_CYCLE / 2, PULSE_CYCLE],
        [PULSE_MIN, PULSE_MAX, PULSE_MIN],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.sin) }
      )
    : PULSE_MIN;

  // Highlight block renderer
  const renderHighlightBlock = (
    range: { start: number; end: number },
    color: string,
    bgOpacity: number,
    borderOpacity: number,
    label: string,
    index: number,
    highlightDelay: number
  ) => {
    const blockOpacity = interpolate(
      frame,
      [highlightDelay, highlightDelay + 15],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
    );

    if (blockOpacity <= 0) return null;

    const yTop = CODE_Y_START + range.start * LINE_HEIGHT - 2;
    const blockHeight = (range.end - range.start + 1) * LINE_HEIGHT + 4;

    return (
      <div
        key={`highlight-${index}`}
        style={{
          position: "absolute",
          left: WINDOW_X + 8,
          top: yTop,
          width: WINDOW_WIDTH - 16,
          height: blockHeight,
          backgroundColor: `${color}${Math.round(bgOpacity * 255).toString(16).padStart(2, "0")}`,
          border: `1px solid ${color}${Math.round(borderOpacity * 255).toString(16).padStart(2, "0")}`,
          borderRadius: 2,
          opacity: blockOpacity,
        }}
      >
        <span
          style={{
            position: "absolute",
            right: 4,
            top: 1,
            fontFamily: FONT_UI,
            fontSize: 7,
            color: color,
            opacity: label === "relevant" ? 0.5 : 0.4,
          }}
        >
          {label}
        </span>
      </div>
    );
  };

  return (
    <div style={{ position: "absolute", left: 0, top: 0, width: PANEL_WIDTH, height: "100%" }}>
      {/* Context window border */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_X,
          top: WINDOW_TOP,
          width: WINDOW_WIDTH,
          height: WINDOW_HEIGHT,
          border: `1px solid ${AMBER}4D`, // 0.3 opacity
          borderRadius: 6,
          overflow: "hidden",
        }}
      >
        {/* Code lines */}
        <div style={{ position: "relative", padding: "16px 12px" }}>
          {CODE_LINES.slice(0, visibleLines).map((line, i) => (
            <div
              key={i}
              style={{
                fontFamily: FONT_CODE,
                fontSize: 8,
                color: CODE_MUTED,
                opacity: 0.35,
                lineHeight: `${LINE_HEIGHT}px`,
                whiteSpace: "pre",
                overflow: "hidden",
              }}
            >
              {line || "\u00A0"}
            </div>
          ))}
        </div>

        {/* Fill indicator bar at bottom */}
        <div
          style={{
            position: "absolute",
            bottom: 0,
            left: 0,
            width: WINDOW_WIDTH,
            height: 3,
            backgroundColor: `${RED}0A`,
          }}
        >
          <div
            style={{
              width: `${fillBarProgress * 100}%`,
              height: "100%",
              backgroundColor: `${RED}33`, // 0.2
            }}
          />
        </div>
      </div>

      {/* Irrelevant highlights (red) */}
      {IRRELEVANT_RANGES.map((range, i) => {
        const delay = LEFT_HIGHLIGHT_START + i * LEFT_HIGHLIGHT_STAGGER;
        const currentOpacity = frame > 360 ? pulsePhase : PULSE_MIN;
        return renderHighlightBlock(range, RED, currentOpacity, 0.2, "irrelevant", i, delay);
      })}

      {/* Relevant highlight (green) */}
      {renderHighlightBlock(RELEVANT_RANGE, GREEN, 0.1, 0.3, "relevant", 99, LEFT_HIGHLIGHT_START + 30)}

      {/* Token count */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_X,
          bottom: 38,
          width: WINDOW_WIDTH,
          textAlign: "center",
          fontFamily: FONT_UI,
          fontSize: 11,
          color: AMBER,
          opacity: tokenOpacity * 0.5,
        }}
      >
        15,000 tokens
      </div>

      {/* Quality note */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_X,
          bottom: 22,
          width: WINDOW_WIDTH,
          textAlign: "center",
          fontFamily: FONT_UI,
          fontSize: 10,
          color: RED,
          opacity: tokenOpacity * 0.4,
        }}
      >
        ~60% irrelevant
      </div>
    </div>
  );
};

export default LeftPanel;

import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PROMPT_FADE_START,
  PROMPT_FADE_END,
  HIGHLIGHT_START,
  HIGHLIGHT_END,
  PROMPT_PANEL_X,
  PROMPT_PANEL_Y,
  PROMPT_PANEL_WIDTH,
  PROMPT_PANEL_HEIGHT,
  PANEL_BG,
  AMBER_ACCENT,
  TEXT_LIGHT,
  PROMPT_LINES,
} from "./constants";

export const PromptDocument: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(
    frame,
    [PROMPT_FADE_START, PROMPT_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const highlightProgress = interpolate(
    frame,
    [HIGHLIGHT_START, HIGHLIGHT_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: PROMPT_PANEL_X - PROMPT_PANEL_WIDTH / 2,
        top: PROMPT_PANEL_Y - PROMPT_PANEL_HEIGHT / 2,
        width: PROMPT_PANEL_WIDTH,
        height: PROMPT_PANEL_HEIGHT,
        backgroundColor: PANEL_BG,
        opacity: fadeIn,
        borderRadius: 4,
        padding: 16,
        boxSizing: "border-box",
        overflow: "hidden",
      }}
    >
      {/* Header */}
      <div
        style={{
          fontFamily: "JetBrains Mono, monospace",
          fontSize: 10,
          color: AMBER_ACCENT,
          opacity: 0.4,
          marginBottom: 8,
        }}
      >
        prompt.md
      </div>

      {/* Content lines */}
      {PROMPT_LINES.map((line, i) => {
        const isHighlighted = line.highlight && highlightProgress > 0;
        const lineColor = isHighlighted ? AMBER_ACCENT : TEXT_LIGHT;
        const lineOpacity = isHighlighted ? 0.3 + highlightProgress * 0.2 : 0.6;

        return (
          <div
            key={i}
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: 12,
              lineHeight: "16px",
              color: lineColor,
              opacity: lineOpacity,
              whiteSpace: "pre-wrap",
              minHeight: line.text === "" ? 8 : undefined,
            }}
          >
            {line.text || "\u00A0"}
          </div>
        );
      })}
    </div>
  );
};

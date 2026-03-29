import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BLOCK_BG,
  PROMPT_ACCENT,
  PROMPT_X,
  PROMPT_Y,
  PROMPT_WIDTH,
  PROMPT_HEIGHT,
  PROMPT_LINES,
  PROMPT_FADE_START,
  PROMPT_FADE_DUR,
} from "./constants";

export const PromptBlock: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [PROMPT_FADE_START, PROMPT_FADE_START + PROMPT_FADE_DUR],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: PROMPT_X,
        top: PROMPT_Y,
        width: PROMPT_WIDTH,
        height: PROMPT_HEIGHT,
        opacity,
      }}
    >
      {/* Label above */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 600,
          color: PROMPT_ACCENT,
          marginBottom: 6,
        }}
      >
        Prompt
      </div>

      {/* Block */}
      <div
        style={{
          width: PROMPT_WIDTH,
          height: PROMPT_HEIGHT,
          backgroundColor: BLOCK_BG,
          border: `1px solid rgba(217, 148, 74, 0.3)`,
          borderRadius: 8,
          padding: 12,
          overflow: "hidden",
          boxSizing: "border-box",
        }}
      >
        {PROMPT_LINES.map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 11,
              lineHeight: "15px",
              color: `rgba(217, 148, 74, 0.7)`,
              whiteSpace: "pre",
            }}
          >
            {line || "\u00A0"}
          </div>
        ))}
      </div>

      {/* Badge */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 11,
          color: `rgba(217, 148, 74, 0.5)`,
          marginTop: 6,
        }}
      >
        ~15 lines
      </div>
    </div>
  );
};

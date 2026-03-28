import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  PROMPT_FILE_X,
  PROMPT_FILE_Y,
  PROMPT_FILE_WIDTH,
  PROMPT_FILE_HEIGHT,
  PROMPT_FILE_BORDER,
  PROMPT_FILE_RADIUS,
  PROMPT_GLOW_BLUR,
  PROMPT_GLOW_OPACITY,
  PROMPT_FILE_NAME,
  GREEN_ACCENT,
  TEXT_MUTED,
  MARKDOWN_LINES,
  SHIMMER_START,
  SHIMMER_DURATION,
  BADGE_START,
  BADGE_DURATION,
} from "./constants";

export const PromptFile: React.FC = () => {
  const frame = useCurrentFrame();

  // Shimmer effect during regeneration (frames 45-60)
  const shimmerOpacity = interpolate(
    frame,
    [SHIMMER_START, SHIMMER_START + SHIMMER_DURATION / 2, SHIMMER_START + SHIMMER_DURATION],
    [0, 0.15, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Enhanced glow after badge appears
  const glowIntensity = interpolate(
    frame,
    [BADGE_START, BADGE_START + BADGE_DURATION],
    [PROMPT_GLOW_OPACITY, 0.22],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const glowBlur = interpolate(
    frame,
    [BADGE_START, BADGE_START + BADGE_DURATION],
    [PROMPT_GLOW_BLUR, 30],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: PROMPT_FILE_X - PROMPT_FILE_WIDTH / 2,
        top: PROMPT_FILE_Y - PROMPT_FILE_HEIGHT / 2,
        width: PROMPT_FILE_WIDTH,
        height: PROMPT_FILE_HEIGHT,
        borderRadius: PROMPT_FILE_RADIUS,
        border: `${PROMPT_FILE_BORDER}px solid ${GREEN_ACCENT}`,
        backgroundColor: "#0D1117",
        boxShadow: `0 0 ${glowBlur}px rgba(90, 170, 110, ${glowIntensity})`,
        overflow: "hidden",
      }}
    >
      {/* File header */}
      <div
        style={{
          padding: "10px 14px",
          borderBottom: `1px solid rgba(90, 170, 110, 0.3)`,
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 14,
            fontWeight: 600,
            color: GREEN_ACCENT,
          }}
        >
          {PROMPT_FILE_NAME}
        </span>
      </div>

      {/* Markdown content lines */}
      <div style={{ padding: "10px 14px", position: "relative" }}>
        {MARKDOWN_LINES.map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: 11,
              color: TEXT_MUTED,
              opacity: 0.4,
              lineHeight: "18px",
              whiteSpace: "nowrap",
              overflow: "hidden",
            }}
          >
            {line || "\u00A0"}
          </div>
        ))}

        {/* Shimmer overlay during regeneration */}
        {shimmerOpacity > 0 && (
          <div
            style={{
              position: "absolute",
              inset: 0,
              background: `linear-gradient(90deg, transparent, rgba(90, 170, 110, ${shimmerOpacity}), transparent)`,
              animation: undefined,
            }}
          />
        )}
      </div>
    </div>
  );
};

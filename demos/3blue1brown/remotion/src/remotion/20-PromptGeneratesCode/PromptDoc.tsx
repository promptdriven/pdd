import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { COLORS, PROMPT_DOC, PROMPT_LINES, BEATS } from "./constants";

/**
 * Renders the prompt document with animated blue glow.
 * Frame 0-60: glow intensifies (activation).
 * Frame 360+: final steady blue glow.
 */
export const PromptDoc: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase 1: activation glow ramp (0-60)
  const activationGlow = interpolate(
    frame,
    [BEATS.PROMPT_ACTIVATE_START, BEATS.PROMPT_ACTIVATE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    },
  );

  // Pulsing during activation
  const pulse =
    frame < BEATS.PROMPT_ACTIVATE_END
      ? Math.sin(frame * 0.15) * 0.3 * activationGlow
      : 0;

  // Final state glow boost
  const finalGlow = interpolate(
    frame,
    [BEATS.FINAL_START, BEATS.FINAL_START + 30],
    [0, 0.3],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    },
  );

  const glowIntensity = Math.min(activationGlow + pulse + finalGlow, 1.3);
  const blurRadius = 10 + glowIntensity * 12;
  const spreadRadius = 2 + glowIntensity * 6;

  return (
    <div
      style={{
        position: "absolute",
        left: PROMPT_DOC.x,
        top: PROMPT_DOC.y,
        width: PROMPT_DOC.width,
        height: PROMPT_DOC.height,
        borderRadius: PROMPT_DOC.borderRadius,
        background: "#ffffff",
        border: `2px solid ${COLORS.PROMPT_BLUE}`,
        boxShadow: `0 0 ${blurRadius}px ${spreadRadius}px ${COLORS.PROMPT_BLUE_GLOW}`,
        padding: 20,
        display: "flex",
        flexDirection: "column",
        justifyContent: "center",
        gap: 8,
        opacity: interpolate(frame, [0, 15], [0, 1], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        }),
      }}
    >
      {/* Header bar */}
      <div
        style={{
          fontSize: 11,
          fontFamily:
            "'JetBrains Mono', 'Fira Code', 'Courier New', monospace",
          fontWeight: 700,
          color: COLORS.PROMPT_BLUE,
          textTransform: "uppercase" as const,
          letterSpacing: 1.5,
          marginBottom: 6,
        }}
      >
        PROMPT
      </div>

      {/* Prompt text lines */}
      {PROMPT_LINES.map((line, i) => {
        const lineOpacity = interpolate(
          frame,
          [5 + i * 8, 15 + i * 8],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          },
        );
        return (
          <div
            key={i}
            style={{
              fontSize: 13,
              fontFamily:
                "'JetBrains Mono', 'Fira Code', 'Courier New', monospace",
              fontWeight: 400,
              color: "#333333",
              lineHeight: 1.5,
              opacity: lineOpacity,
            }}
          >
            {line}
          </div>
        );
      })}
    </div>
  );
};

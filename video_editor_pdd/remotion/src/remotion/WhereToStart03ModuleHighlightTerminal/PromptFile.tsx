import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  GREEN_ACCENT,
  PROMPT_FILE_X,
  PROMPT_FILE_Y,
  MODULE_WIDTH,
  MODULE_HEIGHT,
  PROMPT_LINES,
  MATERIALIZE_START,
  MATERIALIZE_DURATION,
} from "./constants";

/**
 * The prompt file that materializes on the right side.
 * Rises from nothing with a glowing green border, then pulses steadily.
 */
export const PromptFile: React.FC = () => {
  const frame = useCurrentFrame();

  // Materialization progress
  const materializeProgress = interpolate(
    frame,
    [MATERIALIZE_START, MATERIALIZE_START + MATERIALIZE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Scale from 0.8 to 1.0 during materialization
  const scale = interpolate(materializeProgress, [0, 1], [0.85, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Glow pulse after materialization completes
  const isFullyMaterialized = frame >= MATERIALIZE_START + MATERIALIZE_DURATION;
  const pulsePhase = isFullyMaterialized
    ? Math.sin(((frame - MATERIALIZE_START - MATERIALIZE_DURATION) / 30) * Math.PI * 2) * 0.5 + 0.5
    : 0;
  const glowIntensity = isFullyMaterialized
    ? 0.2 + pulsePhase * 0.15
    : materializeProgress * 0.2;

  // Vertical offset: rises up during materialization
  const yOffset = interpolate(materializeProgress, [0, 1], [30, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  if (frame < MATERIALIZE_START) return null;

  return (
    <div
      style={{
        position: "absolute",
        left: PROMPT_FILE_X - MODULE_WIDTH / 2,
        top: PROMPT_FILE_Y - MODULE_HEIGHT / 2 + yOffset,
        width: MODULE_WIDTH,
        height: MODULE_HEIGHT,
        borderRadius: 4,
        border: `2px solid ${GREEN_ACCENT}`,
        backgroundColor: "rgba(10, 15, 26, 0.9)",
        boxShadow: `0 0 ${15 + pulsePhase * 10}px rgba(90, 170, 110, ${glowIntensity})`,
        overflow: "hidden",
        padding: 12,
        opacity: materializeProgress,
        transform: `scale(${scale})`,
        transformOrigin: "center center",
      }}
    >
      {/* File header */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 12,
          fontWeight: 600,
          color: GREEN_ACCENT,
          marginBottom: 10,
          opacity: materializeProgress,
        }}
      >
        auth_handler.prompt.md
      </div>

      {/* Fake markdown content lines */}
      {PROMPT_LINES.map((line, i) => {
        // Stagger line appearance
        const lineProgress = interpolate(
          materializeProgress,
          [i * 0.08, Math.min(i * 0.08 + 0.3, 1)],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }
        );

        if (line.width === 0) {
          return <div key={i} style={{ height: 8 }} />;
        }

        return (
          <div
            key={i}
            style={{
              height: line.isHeader ? 5 : 3,
              width: `${line.width * 80}%`,
              marginLeft: line.indent * 16,
              marginBottom: 6,
              backgroundColor: line.isHeader
                ? GREEN_ACCENT
                : "rgba(90, 170, 110, 0.5)",
              opacity: lineProgress * 0.7,
              borderRadius: 1,
            }}
          />
        );
      })}
    </div>
  );
};

export default PromptFile;

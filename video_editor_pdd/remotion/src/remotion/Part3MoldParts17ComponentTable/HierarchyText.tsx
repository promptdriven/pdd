// HierarchyText.tsx — Pulsing hierarchy line with highlighted phrases
import React from "react";
import { interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  FONT_FAMILY,
  HIERARCHY_FONT_SIZE,
  HIERARCHY_FONT_WEIGHT,
  HIERARCHY_EMPHASIS_WEIGHT,
  HIERARCHY_TEXT_COLOR,
  TESTS_COLOR,
  HIERARCHY_Y,
  SUBTEXT_Y,
  SUBTEXT_FONT_SIZE,
  SUBTEXT_FONT_WEIGHT,
  SUBTEXT_COLOR,
  HIERARCHY_FADE_START,
  HIERARCHY_FADE_DURATION,
  SUBTEXT_FADE_START,
  SUBTEXT_FADE_DURATION,
  PULSE_CYCLE_FRAMES,
  PULSE_GLOW_OPACITY,
  PULSE_GLOW_BLUR,
} from "./constants";

interface HierarchyTextProps {
  absoluteFrame: number;
}

const HierarchyText: React.FC<HierarchyTextProps> = ({ absoluteFrame }) => {
  // Hierarchy line fade-in
  const hierarchyLocalFrame = absoluteFrame - HIERARCHY_FADE_START;
  const hierarchyOpacity = interpolate(
    hierarchyLocalFrame,
    [0, HIERARCHY_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Pulse effect for "tests win" and "Always" — only after fully visible
  const pulseFrame = Math.max(0, hierarchyLocalFrame - HIERARCHY_FADE_DURATION);
  const pulseProgress = (pulseFrame % PULSE_CYCLE_FRAMES) / PULSE_CYCLE_FRAMES;
  const pulseValue = interpolate(
    pulseProgress,
    [0, 0.5, 1],
    [0, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );
  const glowIntensity = pulseValue * PULSE_GLOW_OPACITY;
  const glowBlur = PULSE_GLOW_BLUR;

  // Subtext fade-in
  const subtextLocalFrame = absoluteFrame - SUBTEXT_FADE_START;
  const subtextOpacity = interpolate(
    subtextLocalFrame,
    [0, SUBTEXT_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const showHierarchy = absoluteFrame >= HIERARCHY_FADE_START;
  const showSubtext = absoluteFrame >= SUBTEXT_FADE_START;

  return (
    <>
      {/* Hierarchy line */}
      {showHierarchy && (
        <div
          style={{
            position: "absolute",
            top: HIERARCHY_Y,
            left: 0,
            width: CANVAS_WIDTH,
            textAlign: "center",
            fontFamily: FONT_FAMILY,
            fontSize: HIERARCHY_FONT_SIZE,
            fontWeight: HIERARCHY_FONT_WEIGHT,
            color: HIERARCHY_TEXT_COLOR,
            opacity: hierarchyOpacity,
          }}
        >
          <span>When these conflict, </span>
          <span
            style={{
              fontWeight: HIERARCHY_EMPHASIS_WEIGHT,
              color: TESTS_COLOR,
              textShadow:
                hierarchyLocalFrame > HIERARCHY_FADE_DURATION
                  ? `0 0 ${glowBlur}px rgba(74, 144, 217, ${glowIntensity})`
                  : "none",
            }}
          >
            tests win
          </span>
          <span>. </span>
          <span
            style={{
              fontWeight: HIERARCHY_EMPHASIS_WEIGHT,
              color: TESTS_COLOR,
              textShadow:
                hierarchyLocalFrame > HIERARCHY_FADE_DURATION
                  ? `0 0 ${glowBlur}px rgba(74, 144, 217, ${glowIntensity})`
                  : "none",
            }}
          >
            Always
          </span>
          <span>.</span>
        </div>
      )}

      {/* Subtext */}
      {showSubtext && (
        <div
          style={{
            position: "absolute",
            top: SUBTEXT_Y,
            left: 0,
            width: CANVAS_WIDTH,
            textAlign: "center",
            fontFamily: FONT_FAMILY,
            fontSize: SUBTEXT_FONT_SIZE,
            fontWeight: SUBTEXT_FONT_WEIGHT,
            color: SUBTEXT_COLOR,
            opacity: subtextOpacity,
          }}
        >
          The walls override the specification. The specification overrides the
          style.
        </div>
      )}
    </>
  );
};

export default HierarchyText;

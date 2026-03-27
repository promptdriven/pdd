import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  RULE_Y,
  RULE_WIDTH,
  RULE_HEIGHT,
  RULE_COLOR,
  RULE_OPACITY,
  ACCENT_COLOR,
  ACCENT_GLOW_OPACITY,
  ACCENT_GLOW_WIDTH,
  ACCENT_GLOW_Y,
  RULE_DRAW_START,
  RULE_DRAW_END,
  ACCENT_PULSE_START,
  ACCENT_PULSE_END,
} from "./constants";

export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();

  // Rule draws from center outward
  const ruleProgress = interpolate(
    frame,
    [RULE_DRAW_START, RULE_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    }
  );

  const currentRuleWidth = RULE_WIDTH * ruleProgress;
  const ruleLeft = (CANVAS_WIDTH - currentRuleWidth) / 2;

  // Accent glow pulse: fade in then fade out over 3 frames
  const accentOpacity = interpolate(
    frame,
    [ACCENT_PULSE_START, (ACCENT_PULSE_START + ACCENT_PULSE_END) / 2, ACCENT_PULSE_END],
    [0, ACCENT_GLOW_OPACITY, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.sin),
    }
  );

  // Keep a residual glow after pulse
  const residualGlow = interpolate(
    frame,
    [ACCENT_PULSE_END, ACCENT_PULSE_END + 5],
    [0, ACCENT_GLOW_OPACITY * 0.5],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const finalAccentOpacity = Math.max(accentOpacity, residualGlow);

  return (
    <>
      {/* Main horizontal rule */}
      {ruleProgress > 0 && (
        <div
          style={{
            position: "absolute",
            top: RULE_Y,
            left: ruleLeft,
            width: currentRuleWidth,
            height: RULE_HEIGHT,
            backgroundColor: RULE_COLOR,
            opacity: RULE_OPACITY,
          }}
        />
      )}

      {/* Blue accent glow beneath rule */}
      {finalAccentOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: ACCENT_GLOW_Y,
            left: (CANVAS_WIDTH - ACCENT_GLOW_WIDTH) / 2,
            width: ACCENT_GLOW_WIDTH,
            height: 1,
            backgroundColor: ACCENT_COLOR,
            opacity: finalAccentOpacity,
            boxShadow: `0 0 8px ${ACCENT_COLOR}`,
          }}
        />
      )}
    </>
  );
};

export default HorizontalRule;

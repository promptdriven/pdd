import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  RULE_COLOR,
  RULE_OPACITY,
  RULE_Y,
  RULE_WIDTH,
  RULE_HEIGHT,
  RULE_CENTER_X,
  RULE_DRAW_START,
  RULE_DRAW_END,
  ACCENT_COLOR,
  ACCENT_GLOW_OPACITY,
  GLOW_WIDTH,
  GLOW_HEIGHT,
  GLOW_Y,
  GLOW_PULSE_START,
  GLOW_PULSE_END,
} from "./constants";

/** Horizontal rule that draws from center outward, plus accent glow pulse. */
export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();

  // Rule draws from 0 → full width over [25, 30]
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

  // Accent glow pulse: opacity goes 0 → peak → 0 over [45, 48]
  const glowOpacity = interpolate(
    frame,
    [GLOW_PULSE_START, (GLOW_PULSE_START + GLOW_PULSE_END) / 2, GLOW_PULSE_END],
    [0, ACCENT_GLOW_OPACITY, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.sin),
    }
  );

  return (
    <>
      {/* Main horizontal rule */}
      <div
        style={{
          position: "absolute",
          top: RULE_Y - RULE_HEIGHT / 2,
          left: RULE_CENTER_X - currentRuleWidth / 2,
          width: currentRuleWidth,
          height: RULE_HEIGHT,
          backgroundColor: RULE_COLOR,
          opacity: RULE_OPACITY,
        }}
      />

      {/* Blue accent glow beneath rule */}
      <div
        style={{
          position: "absolute",
          top: GLOW_Y - GLOW_HEIGHT / 2,
          left: RULE_CENTER_X - GLOW_WIDTH / 2,
          width: GLOW_WIDTH,
          height: GLOW_HEIGHT,
          backgroundColor: ACCENT_COLOR,
          opacity: glowOpacity,
          boxShadow: `0 0 12px 4px ${ACCENT_COLOR}`,
        }}
      />
    </>
  );
};

export default HorizontalRule;

import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame } from "remotion";
import { RadialGlow } from "./RadialGlow";
import {
  GLOW_A_CENTER,
  GLOW_A_RADIUS,
  GLOW_A_COLOR,
  GLOW_A_OPACITY_MIN,
  GLOW_A_OPACITY_MAX,
  GLOW_A_SPEED,
  GLOW_B_CENTER,
  GLOW_B_RADIUS,
  GLOW_B_COLOR,
  GLOW_B_OPACITY_MIN,
  GLOW_B_OPACITY_MAX,
  GLOW_B_SPEED,
  GLOW_B_PHASE_OFFSET,
  GLOW_C_CENTER,
  GLOW_C_RADIUS,
  GLOW_C_COLOR,
  GLOW_C_OPACITY,
  WIDTH,
  HEIGHT,
} from "./constants";

export const defaultColdOpen07MonitorGlowOverlayProps = {};

/**
 * Monitor Glow Ambient Overlay — a compositing enhancement layer.
 *
 * Renders three soft radial gradients that simulate ambient monitor light:
 * - Glow A (left edge): pulsing blue, ~6s cycle
 * - Glow B (right edge): pulsing cool blue, ~8s cycle, counter-phased
 * - Glow C (top-right): static amber accent
 *
 * Uses screen blend mode so it adds light without obscuring content beneath.
 * Overall effect is subtle (15–25% opacity per glow).
 */
export const ColdOpen07MonitorGlowOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  // Sinusoidal oscillation for Glow A: maps sin output [-1, 1] → [min, max]
  const glowAOpacity = interpolate(
    Math.sin(frame * GLOW_A_SPEED),
    [-1, 1],
    [GLOW_A_OPACITY_MIN, GLOW_A_OPACITY_MAX]
  );

  // Sinusoidal oscillation for Glow B: counter-phased via π offset
  const glowBOpacity = interpolate(
    Math.sin(frame * GLOW_B_SPEED + GLOW_B_PHASE_OFFSET),
    [-1, 1],
    [GLOW_B_OPACITY_MIN, GLOW_B_OPACITY_MAX]
  );

  return (
    <AbsoluteFill
      style={{
        width: WIDTH,
        height: HEIGHT,
        mixBlendMode: "screen",
        pointerEvents: "none",
      }}
    >
      {/* Left-edge blue monitor glow — pulsing */}
      <RadialGlow
        center={GLOW_A_CENTER}
        radius={GLOW_A_RADIUS}
        color={GLOW_A_COLOR}
        opacity={glowAOpacity}
      />

      {/* Right-edge cool blue glow — counter-phased pulsing */}
      <RadialGlow
        center={GLOW_B_CENTER}
        radius={GLOW_B_RADIUS}
        color={GLOW_B_COLOR}
        opacity={glowBOpacity}
      />

      {/* Top-right amber accent — static */}
      <RadialGlow
        center={GLOW_C_CENTER}
        radius={GLOW_C_RADIUS}
        color={GLOW_C_COLOR}
        opacity={GLOW_C_OPACITY}
      />
    </AbsoluteFill>
  );
};

export default ColdOpen07MonitorGlowOverlay;

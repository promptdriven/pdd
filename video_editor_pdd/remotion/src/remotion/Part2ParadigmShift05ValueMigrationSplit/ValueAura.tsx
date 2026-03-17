import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  AURA_BLUR,
  AURA_PULSE_MIN,
  AURA_PULSE_MAX,
  AURA_PULSE_PERIOD,
  AURA_START,
} from "./constants";

interface ValueAuraProps {
  centerX: number;
  centerY: number;
  width: number;
  height: number;
  color: string;
}

export const ValueAura: React.FC<ValueAuraProps> = ({
  centerX,
  centerY,
  width,
  height,
  color,
}) => {
  const frame = useCurrentFrame();

  // Fade in the aura
  const fadeIn = interpolate(
    frame,
    [AURA_START, AURA_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Pulsing opacity cycle
  const cycleFrame = Math.max(0, frame - AURA_START);
  const pulsePhase = (cycleFrame % AURA_PULSE_PERIOD) / AURA_PULSE_PERIOD;
  // Use sine wave for smooth pulsing: 0→1→0 over the cycle
  const sineValue = Math.sin(pulsePhase * Math.PI * 2);
  const pulseOpacity = interpolate(
    sineValue,
    [-1, 1],
    [AURA_PULSE_MIN, AURA_PULSE_MAX]
  );

  const opacity = frame >= AURA_START ? fadeIn * pulseOpacity : 0;

  return (
    <div
      style={{
        position: "absolute",
        left: centerX - width / 2 - AURA_BLUR,
        top: centerY - height / 2 - AURA_BLUR,
        width: width + AURA_BLUR * 2,
        height: height + AURA_BLUR * 2,
        borderRadius: "50%",
        background: `radial-gradient(ellipse at center, ${color} 0%, transparent 70%)`,
        filter: `blur(${AURA_BLUR}px)`,
        opacity,
        pointerEvents: "none" as const,
      }}
    />
  );
};

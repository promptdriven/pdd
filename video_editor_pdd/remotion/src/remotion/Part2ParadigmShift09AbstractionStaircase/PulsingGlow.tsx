import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { ACTIVE_COLOR, PULSE_PERIOD, STEP_WIDTH, STEP_HEIGHT } from "./constants";

interface PulsingGlowProps {
  x: number;
  y: number;
  startFrame: number;
}

export const PulsingGlow: React.FC<PulsingGlowProps> = ({
  x,
  y,
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  const fadeIn = interpolate(localFrame, [0, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const cycleFrame = localFrame % PULSE_PERIOD;
  const pulseOpacity = interpolate(
    cycleFrame,
    [0, PULSE_PERIOD / 2, PULSE_PERIOD],
    [0.08, 0.15, 0.08],
    { easing: Easing.inOut(Easing.sin) }
  );

  const borderOpacity = interpolate(
    cycleFrame,
    [0, PULSE_PERIOD / 2, PULSE_PERIOD],
    [0.2, 0.5, 0.2],
    { easing: Easing.inOut(Easing.sin) }
  );

  return (
    <>
      {/* Ambient glow */}
      <div
        style={{
          position: "absolute",
          left: x - 30,
          top: y - STEP_HEIGHT - 30,
          width: STEP_WIDTH + 60,
          height: STEP_HEIGHT + 60,
          borderRadius: 16,
          background: `radial-gradient(ellipse at center, ${ACTIVE_COLOR} 0%, transparent 70%)`,
          opacity: pulseOpacity * fadeIn,
          filter: "blur(20px)",
          pointerEvents: "none",
        }}
      />
      {/* Pulsing border */}
      <div
        style={{
          position: "absolute",
          left: x,
          top: y - STEP_HEIGHT,
          width: STEP_WIDTH,
          height: STEP_HEIGHT,
          border: `2px solid ${ACTIVE_COLOR}`,
          borderRadius: 4,
          opacity: borderOpacity * fadeIn,
          pointerEvents: "none",
        }}
      />
    </>
  );
};

interface ParticleDriftProps {
  x: number;
  y: number;
  startFrame: number;
}

export const ParticleDrift: React.FC<ParticleDriftProps> = ({
  x,
  y,
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  const fadeIn = interpolate(localFrame, [0, 30], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Generate deterministic particles
  const particles = Array.from({ length: 8 }).map((_, i) => {
    const seed = i * 37 + 13;
    const offsetX = ((seed * 7) % 200) - 20;
    const speed = 0.3 + ((seed * 3) % 5) / 10;
    const size = 2 + ((seed * 11) % 3);
    const phase = (seed * 17) % 100;

    const yOffset = ((localFrame + phase) * speed) % 120;
    const particleOpacity = interpolate(
      yOffset,
      [0, 20, 80, 120],
      [0, 0.12, 0.1, 0],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );

    return (
      <div
        key={i}
        style={{
          position: "absolute",
          left: x + offsetX,
          top: y - STEP_HEIGHT - yOffset,
          width: size,
          height: size,
          borderRadius: "50%",
          backgroundColor: ACTIVE_COLOR,
          opacity: particleOpacity * fadeIn,
        }}
      />
    );
  });

  return <>{particles}</>;
};

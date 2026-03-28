import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PARTICLE_COUNT,
  PARTICLE_SIZE,
  ARC_PEAK_Y,
  ARC_START_X,
  ARC_START_Y,
  ARC_END_X,
  ARC_END_Y,
  PARTICLE_STAGGER_DELAY,
  PARTICLE_SOURCE_COLOR,
  PARTICLE_DEST_COLOR,
  PARTICLE_OPACITY,
  FLOW_START_FRAME,
} from "./constants";

/**
 * Parses a hex color string to [r, g, b].
 */
function hexToRgb(hex: string): [number, number, number] {
  const h = hex.replace("#", "");
  return [
    parseInt(h.substring(0, 2), 16),
    parseInt(h.substring(2, 4), 16),
    parseInt(h.substring(4, 6), 16),
  ];
}

function lerpColor(
  color1: [number, number, number],
  color2: [number, number, number],
  t: number
): string {
  const r = Math.round(color1[0] + (color2[0] - color1[0]) * t);
  const g = Math.round(color1[1] + (color2[1] - color1[1]) * t);
  const b = Math.round(color1[2] + (color2[2] - color1[2]) * t);
  return `rgb(${r},${g},${b})`;
}

/**
 * Compute a point along a parabolic arc from start to end,
 * peaking at arcPeakY, parameterized by t in [0,1].
 */
function getArcPoint(t: number): { x: number; y: number } {
  const x = ARC_START_X + (ARC_END_X - ARC_START_X) * t;
  // Parabolic arc: y dips upward (lower y value) at midpoint
  const baseY = ARC_START_Y + (ARC_END_Y - ARC_START_Y) * t;
  const arcOffset = -4 * (ARC_START_Y - ARC_PEAK_Y) * t * (1 - t);
  const y = baseY + arcOffset;
  return { x, y };
}

const sourceRgb = hexToRgb(PARTICLE_SOURCE_COLOR);
const destRgb = hexToRgb(PARTICLE_DEST_COLOR);

// Each particle takes this many frames to traverse the arc
const PARTICLE_TRAVEL_FRAMES = 50;
// Total cycle length for looping
const CYCLE_LENGTH = PARTICLE_COUNT * PARTICLE_STAGGER_DELAY;

export const ParticleArc: React.FC = () => {
  const frame = useCurrentFrame();
  const flowFrame = frame - FLOW_START_FRAME;

  // Don't render before flow starts
  if (flowFrame < 0) return null;

  // Fade in the particle system over the first 15 frames
  const systemOpacity = interpolate(flowFrame, [0, 15], [0, 1], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const particles: React.ReactNode[] = [];

  for (let i = 0; i < PARTICLE_COUNT; i++) {
    // Each particle starts at a staggered time, looping
    const particleStartOffset = i * PARTICLE_STAGGER_DELAY;
    const localFrame = flowFrame - particleStartOffset;

    // Determine current cycle position (looping)
    const cycleFrame =
      localFrame >= 0
        ? ((localFrame % CYCLE_LENGTH) + CYCLE_LENGTH) % CYCLE_LENGTH
        : -1;

    if (cycleFrame < 0) continue;

    // t goes from 0 to 1 over PARTICLE_TRAVEL_FRAMES
    const t = interpolate(cycleFrame, [0, PARTICLE_TRAVEL_FRAMES], [0, 1], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    });

    // Only show particles that are currently traveling
    if (cycleFrame > PARTICLE_TRAVEL_FRAMES) continue;

    const { x, y } = getArcPoint(t);
    const color = lerpColor(sourceRgb, destRgb, t);

    // Particle fades in/out at the edges of its travel
    const particleOpacity = interpolate(
      t,
      [0, 0.1, 0.9, 1],
      [0, PARTICLE_OPACITY, PARTICLE_OPACITY, 0],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );

    particles.push(
      <circle
        key={`p-${i}`}
        cx={x}
        cy={y}
        r={PARTICLE_SIZE}
        fill={color}
        opacity={particleOpacity}
      />
    );
  }

  return (
    <svg
      width={1920}
      height={1080}
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        opacity: systemOpacity,
      }}
    >
      {particles}
    </svg>
  );
};

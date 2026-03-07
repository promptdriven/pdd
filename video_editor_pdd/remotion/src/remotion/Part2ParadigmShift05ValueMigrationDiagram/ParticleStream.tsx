import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate } from "remotion";
import {
  PARTICLE_COUNT,
  PARTICLE_SIZE,
  PARTICLE_COLOR,
  PARTICLE_WAVE_AMPLITUDE,
  PART_CENTER_X,
  STREAM_FROM_Y,
  STREAM_TO_Y,
  PARTICLES_START,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

export const ParticleStream: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < PARTICLES_START) return null;

  const masterOpacity = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const streamHeight = STREAM_FROM_Y - STREAM_TO_Y;

  return (
    <AbsoluteFill style={{ opacity: masterOpacity }}>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {Array.from({ length: PARTICLE_COUNT }).map((_, i) => {
          const cycleLength = 90; // frames per full upward travel
          const offset = (i / PARTICLE_COUNT) * cycleLength;
          const localFrame = frame - PARTICLES_START;
          const t = ((localFrame + offset) % cycleLength) / cycleLength;

          // y: bottom (STREAM_FROM_Y) → top (STREAM_TO_Y)
          const y = STREAM_FROM_Y - t * streamHeight;

          // Sinusoidal wave on x axis
          const x =
            PART_CENTER_X +
            Math.sin(t * Math.PI * 4 + i * 0.7) * PARTICLE_WAVE_AMPLITUDE;

          // Fade in near bottom, fade out near top
          const particleOpacity = interpolate(
            t,
            [0, 0.1, 0.85, 1],
            [0, 0.9, 0.9, 0],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          );

          return (
            <circle
              key={i}
              cx={x}
              cy={y}
              r={PARTICLE_SIZE / 2}
              fill={PARTICLE_COLOR}
              opacity={particleOpacity}
            />
          );
        })}
      </svg>
    </AbsoluteFill>
  );
};

export default ParticleStream;

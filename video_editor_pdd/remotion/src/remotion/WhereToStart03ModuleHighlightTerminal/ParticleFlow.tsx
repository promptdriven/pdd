import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PARTICLE_COLOR,
  CODE_FILE_X,
  CODE_FILE_Y,
  PROMPT_FILE_X,
  PROMPT_FILE_Y,
  PARTICLE_START,
  PARTICLE_DURATION,
  PARTICLE_COUNT,
} from "./constants";

interface Particle {
  id: number;
  startFrame: number;
  arcHeight: number;
  speed: number;
  size: number;
}

// Pre-generate particles with deterministic pseudo-random values
const particles: Particle[] = Array.from({ length: PARTICLE_COUNT }, (_, i) => ({
  id: i,
  startFrame: PARTICLE_START + i * 3, // 3-frame stagger
  arcHeight: -40 - ((i * 17 + 7) % 60), // arc height between -40 and -100
  speed: 0.8 + ((i * 13 + 3) % 10) / 25, // speed factor 0.8 - 1.2
  size: 1.5 + ((i * 7 + 11) % 5) / 5, // size 1.5 - 2.5
}));

const FROM_X = CODE_FILE_X + 100; // Right edge of code file area
const FROM_Y = CODE_FILE_Y;
const TO_X = PROMPT_FILE_X - 100; // Left edge of prompt file area
const TO_Y = PROMPT_FILE_Y;

/**
 * Particle flow from code file to prompt file.
 * Particles travel along gentle arcs from left to right.
 */
export const ParticleFlow: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < PARTICLE_START) return null;

  return (
    <svg
      style={{
        position: "absolute",
        inset: 0,
        width: "100%",
        height: "100%",
        pointerEvents: "none",
      }}
    >
      {particles.map((p) => {
        if (frame < p.startFrame) return null;

        const particleDuration = PARTICLE_DURATION * p.speed;
        const localFrame = frame - p.startFrame;

        const t = interpolate(
          localFrame,
          [0, particleDuration],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.inOut(Easing.quad),
          }
        );

        if (t >= 1) return null;

        // Quadratic bezier arc
        const cx = (FROM_X + TO_X) / 2;
        const cy = (FROM_Y + TO_Y) / 2 + p.arcHeight;

        const x =
          (1 - t) * (1 - t) * FROM_X +
          2 * (1 - t) * t * cx +
          t * t * TO_X;
        const y =
          (1 - t) * (1 - t) * FROM_Y +
          2 * (1 - t) * t * cy +
          t * t * TO_Y;

        // Fade in at start, fade out at end
        const opacity = interpolate(
          t,
          [0, 0.1, 0.8, 1],
          [0, 0.6, 0.6, 0],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }
        );

        return (
          <circle
            key={p.id}
            cx={x}
            cy={y}
            r={p.size}
            fill={PARTICLE_COLOR}
            opacity={opacity}
          />
        );
      })}

      {/* Faint trailing arc path */}
      {frame >= PARTICLE_START && frame < PARTICLE_START + PARTICLE_DURATION + 30 && (
        <path
          d={`M ${FROM_X} ${FROM_Y} Q ${(FROM_X + TO_X) / 2} ${(FROM_Y + TO_Y) / 2 - 70} ${TO_X} ${TO_Y}`}
          fill="none"
          stroke={PARTICLE_COLOR}
          strokeWidth={1}
          opacity={interpolate(
            frame,
            [PARTICLE_START, PARTICLE_START + 20, PARTICLE_START + PARTICLE_DURATION, PARTICLE_START + PARTICLE_DURATION + 30],
            [0, 0.15, 0.15, 0],
            {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }
          )}
          strokeDasharray="4 6"
        />
      )}
    </svg>
  );
};

export default ParticleFlow;

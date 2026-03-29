import React, { useMemo } from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  PANEL_WIDTH,
  CANVAS_HEIGHT,
  LIQUID_COLOR,
  LIQUID_OPACITY,
  MOLD_INJECTION_X,
  MOLD_INJECTION_Y,
  MOLD_OUTER_X,
  MOLD_OUTER_Y,
  MOLD_OUTER_W,
  MOLD_OUTER_H,
  MOLD_CORNER_RADIUS,
  PHASE_ANIMATE_START,
} from './constants';

// Seeded pseudo-random for deterministic particles
function seededRandom(seed: number): number {
  const x = Math.sin(seed * 12.9898 + seed * 78.233) * 43758.5453;
  return x - Math.floor(x);
}

interface Particle {
  id: number;
  startFrame: number;
  startX: number;
  startY: number;
  targetX: number;
  targetY: number;
  speed: number;
  size: number;
  wobbleAmplitude: number;
  wobbleFrequency: number;
}

const NUM_PARTICLES = 80;

export const LiquidFlow: React.FC = () => {
  const frame = useCurrentFrame();

  // Generate particles deterministically
  const particles = useMemo<Particle[]>(() => {
    const result: Particle[] = [];
    for (let i = 0; i < NUM_PARTICLES; i++) {
      const r1 = seededRandom(i * 3 + 1);
      const r2 = seededRandom(i * 3 + 2);
      const r3 = seededRandom(i * 3 + 3);
      const r4 = seededRandom(i * 7 + 5);
      const r5 = seededRandom(i * 11 + 7);

      // Particles start at injection point and flow downward into the mold
      const startFrame = PHASE_ANIMATE_START + Math.floor(r1 * 200);
      const targetX =
        MOLD_OUTER_X + MOLD_CORNER_RADIUS + r2 * (MOLD_OUTER_W - MOLD_CORNER_RADIUS * 2);
      const targetY =
        MOLD_OUTER_Y + MOLD_CORNER_RADIUS + r3 * (MOLD_OUTER_H - MOLD_CORNER_RADIUS * 2);

      result.push({
        id: i,
        startFrame,
        startX: MOLD_INJECTION_X + (r4 - 0.5) * 20,
        startY: MOLD_INJECTION_Y,
        targetX,
        targetY,
        speed: 0.6 + r5 * 0.8,
        size: 3 + r4 * 5,
        wobbleAmplitude: 5 + r2 * 15,
        wobbleFrequency: 0.05 + r3 * 0.1,
      });
    }
    return result;
  }, []);

  // Clip path for constraining particles within mold
  const clipId = 'mold-clip';

  return (
    <svg
      width={PANEL_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <clipPath id={clipId}>
          <rect
            x={MOLD_OUTER_X + 4}
            y={MOLD_INJECTION_Y}
            width={MOLD_OUTER_W - 8}
            height={MOLD_OUTER_H + (MOLD_OUTER_Y - MOLD_INJECTION_Y) - 4}
            rx={MOLD_CORNER_RADIUS}
          />
        </clipPath>
        <filter id="liquidBlur">
          <feGaussianBlur stdDeviation={1.5} />
        </filter>
      </defs>

      <g clipPath={`url(#${clipId})`}>
        {particles.map((p) => {
          if (frame < p.startFrame) return null;

          const age = frame - p.startFrame;
          const travelDuration = 120 / p.speed;
          const t = Math.min(age / travelDuration, 1);

          // Ease in for initial flow
          const easedT = Easing.in(Easing.quad)(t);

          const x =
            p.startX +
            (p.targetX - p.startX) * easedT +
            Math.sin(age * p.wobbleFrequency) * p.wobbleAmplitude * (1 - easedT);
          const y = p.startY + (p.targetY - p.startY) * easedT;

          // Particle fades in then holds
          const particleOpacity = interpolate(age, [0, 8], [0, LIQUID_OPACITY], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          });

          // Once settled, particle becomes part of the fill
          const settledOpacity = t >= 1 ? LIQUID_OPACITY * 1.2 : particleOpacity;

          return (
            <circle
              key={p.id}
              cx={x}
              cy={y}
              r={p.size * (t >= 1 ? 1.3 : 1)}
              fill={LIQUID_COLOR}
              fillOpacity={settledOpacity}
              filter={t < 1 ? 'url(#liquidBlur)' : undefined}
            />
          );
        })}
      </g>
    </svg>
  );
};

export default LiquidFlow;

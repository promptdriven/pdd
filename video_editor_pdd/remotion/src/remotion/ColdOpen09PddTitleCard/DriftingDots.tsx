import React, { useMemo } from 'react';
import { useCurrentFrame } from 'remotion';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  ACCENT_BLUE,
  DOT_COUNT,
  DOT_MIN_SIZE,
  DOT_MAX_SIZE,
  DOT_OPACITY,
  DOT_SPEED,
} from './constants';

// Seeded pseudo-random number generator for deterministic dot positions
function seededRandom(seed: number): () => number {
  let s = seed;
  return () => {
    s = (s * 16807 + 0) % 2147483647;
    return (s - 1) / 2147483646;
  };
}

interface Dot {
  x: number;
  y: number;
  size: number;
  driftAngle: number; // direction of drift in radians
}

export const DriftingDots: React.FC<{ globalOpacity?: number }> = ({
  globalOpacity = 1,
}) => {
  const frame = useCurrentFrame();

  const dots = useMemo<Dot[]>(() => {
    const rng = seededRandom(42);
    return Array.from({ length: DOT_COUNT }, () => ({
      x: rng() * CANVAS_WIDTH,
      y: rng() * CANVAS_HEIGHT,
      size: DOT_MIN_SIZE + rng() * (DOT_MAX_SIZE - DOT_MIN_SIZE),
      driftAngle: rng() * Math.PI * 2,
    }));
  }, []);

  return (
    <>
      {dots.map((dot, i) => {
        const dx = Math.cos(dot.driftAngle) * DOT_SPEED * frame;
        const dy = Math.sin(dot.driftAngle) * DOT_SPEED * frame;

        // Wrap around canvas edges
        const x = ((dot.x + dx) % CANVAS_WIDTH + CANVAS_WIDTH) % CANVAS_WIDTH;
        const y = ((dot.y + dy) % CANVAS_HEIGHT + CANVAS_HEIGHT) % CANVAS_HEIGHT;

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: x,
              top: y,
              width: dot.size,
              height: dot.size,
              borderRadius: '50%',
              backgroundColor: ACCENT_BLUE,
              opacity: DOT_OPACITY * globalOpacity,
            }}
          />
        );
      })}
    </>
  );
};

export default DriftingDots;

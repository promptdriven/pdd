import React, { useMemo } from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  MODULE_X,
  MODULE_Y,
  PROMPT_X,
  PROMPT_Y,
  BLUE_ACCENT,
  PARTICLE_COUNT,
  PARTICLE_SIZE,
  PARTICLE_STAGGER,
} from './constants';

/**
 * Evaluates a cubic Bezier curve at parameter t.
 * Control points: P0 = start, P1 = cp1, P2 = cp2, P3 = end
 */
function bezierPoint(
  t: number,
  p0: number,
  p1: number,
  p2: number,
  p3: number,
): number {
  const u = 1 - t;
  return u * u * u * p0 + 3 * u * u * t * p1 + 3 * u * t * t * p2 + t * t * t * p3;
}

const ParticleStream: React.FC<{ startFrame: number }> = ({ startFrame }) => {
  const frame = useCurrentFrame();

  // Generate stable particle configs
  const particles = useMemo(() => {
    const result: Array<{
      delay: number;
      travelDuration: number;
      opacity: number;
      size: number;
    }> = [];
    for (let i = 0; i < PARTICLE_COUNT; i++) {
      // Use deterministic pseudo-random based on index
      const seed = (i * 7 + 3) % 17;
      result.push({
        delay: i * PARTICLE_STAGGER,
        travelDuration: 35 + (seed % 15), // 35-49 frames travel time
        opacity: 0.3 + (seed / 17) * 0.3, // 0.3-0.6
        size: PARTICLE_SIZE + (seed % 3) - 1, // 2-4px
      });
    }
    return result;
  }, []);

  // Bezier control points for arc path
  const startX = MODULE_X + 60; // center of module block
  const startY = MODULE_Y + 30;
  const endX = PROMPT_X; // center of prompt document
  const endY = PROMPT_Y;
  const cp1X = startX + (endX - startX) * 0.3;
  const cp1Y = startY - 120; // arc upward
  const cp2X = startX + (endX - startX) * 0.7;
  const cp2Y = endY - 100;

  const relativeFrame = frame - startFrame;
  if (relativeFrame < 0) return null;

  return (
    <>
      {particles.map((p, i) => {
        const particleFrame = relativeFrame - p.delay;
        if (particleFrame < 0 || particleFrame > p.travelDuration + 10) return null;

        const progress = interpolate(
          particleFrame,
          [0, p.travelDuration],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.inOut(Easing.cubic),
          },
        );

        // Fade out at the end
        const fadeOut = interpolate(
          particleFrame,
          [p.travelDuration - 5, p.travelDuration + 5],
          [1, 0],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
        );

        const x = bezierPoint(progress, startX, cp1X, cp2X, endX);
        const y = bezierPoint(progress, startY, cp1Y, cp2Y, endY);

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: x - p.size / 2,
              top: y - p.size / 2,
              width: p.size,
              height: p.size,
              borderRadius: '50%',
              backgroundColor: BLUE_ACCENT,
              opacity: p.opacity * fadeOut,
              boxShadow: `0 0 ${p.size * 2}px ${BLUE_ACCENT}`,
            }}
          />
        );
      })}
    </>
  );
};

export default ParticleStream;

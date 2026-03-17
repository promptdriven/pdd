import React, { useMemo } from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  MODULE_POS,
  MODULE_SIZE,
  PROMPT_POS,
  PROMPT_SIZE,
  PARTICLE_COUNT,
  PARTICLE_SIZE,
  SELECTION_BLUE,
} from './constants';

/**
 * Particles flow along a Bezier curve from the code block center
 * to the prompt document center, staggered and organic.
 */

const FROM_X = MODULE_POS.x + MODULE_SIZE.w / 2;
const FROM_Y = MODULE_POS.y + MODULE_SIZE.h / 2;
const TO_X = PROMPT_POS.x + PROMPT_SIZE.w / 2;
const TO_Y = PROMPT_POS.y + PROMPT_SIZE.h / 2;

// Bezier control points — arc upward
const CP1_X = FROM_X + (TO_X - FROM_X) * 0.3;
const CP1_Y = FROM_Y - 160;
const CP2_X = FROM_X + (TO_X - FROM_X) * 0.7;
const CP2_Y = TO_Y - 140;

function cubicBezier(t: number, p0: number, p1: number, p2: number, p3: number) {
  const u = 1 - t;
  return u * u * u * p0 + 3 * u * u * t * p1 + 3 * u * t * t * p2 + t * t * t * p3;
}

interface Particle {
  id: number;
  staggerOffset: number; // frame offset
  travelDuration: number;
  baseOpacity: number;
  sizeJitter: number;
  curveJitter: number; // slight perpendicular offset
}

export const ParticleStream: React.FC<{ startFrame: number }> = ({ startFrame }) => {
  const frame = useCurrentFrame();

  const particles = useMemo<Particle[]>(() => {
    const seed = 42;
    const arr: Particle[] = [];
    for (let i = 0; i < PARTICLE_COUNT; i++) {
      // Deterministic pseudo-random
      const r1 = Math.sin(seed + i * 127.1) * 43758.5453;
      const rand1 = r1 - Math.floor(r1);
      const r2 = Math.sin(seed + i * 269.5) * 13758.1234;
      const rand2 = r2 - Math.floor(r2);
      const r3 = Math.sin(seed + i * 419.2) * 23421.6311;
      const rand3 = r3 - Math.floor(r3);

      arr.push({
        id: i,
        staggerOffset: Math.floor(i * 3 + rand1 * 4), // ~3 frames apart with jitter
        travelDuration: 35 + Math.floor(rand2 * 15), // 35-50 frames
        baseOpacity: 0.3 + rand3 * 0.3, // 0.3-0.6
        sizeJitter: 0.7 + rand1 * 0.6, // 0.7-1.3 multiplier
        curveJitter: (rand2 - 0.5) * 30, // -15 to +15 px
      });
    }
    return arr;
  }, []);

  const relativeFrame = frame - startFrame;
  if (relativeFrame < 0) return null;

  return (
    <>
      {particles.map((p) => {
        const particleLocal = relativeFrame - p.staggerOffset;
        if (particleLocal < 0 || particleLocal > p.travelDuration + 10) return null;

        const t = interpolate(
          particleLocal,
          [0, p.travelDuration],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.bezier(0.42, 0, 0.58, 1),
          },
        );

        const x = cubicBezier(t, FROM_X, CP1_X, CP2_X, TO_X);
        const y = cubicBezier(t, FROM_Y, CP1_Y, CP2_Y, TO_Y);

        // Perpendicular offset for organic feel
        const nx = -(TO_Y - FROM_Y);
        const ny = TO_X - FROM_X;
        const len = Math.sqrt(nx * nx + ny * ny) || 1;
        const offsetX = (nx / len) * p.curveJitter * Math.sin(t * Math.PI);
        const offsetY = (ny / len) * p.curveJitter * Math.sin(t * Math.PI);

        // Fade in at start, fade out at end
        const opacity = interpolate(
          particleLocal,
          [0, 5, p.travelDuration - 5, p.travelDuration],
          [0, p.baseOpacity, p.baseOpacity, 0],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
        );

        const size = PARTICLE_SIZE * p.sizeJitter;

        return (
          <div
            key={p.id}
            style={{
              position: 'absolute',
              left: x + offsetX - size / 2,
              top: y + offsetY - size / 2,
              width: size,
              height: size,
              borderRadius: '50%',
              backgroundColor: SELECTION_BLUE,
              opacity,
              boxShadow: `0 0 ${size * 2}px ${SELECTION_BLUE}`,
            }}
          />
        );
      })}
    </>
  );
};

export default ParticleStream;

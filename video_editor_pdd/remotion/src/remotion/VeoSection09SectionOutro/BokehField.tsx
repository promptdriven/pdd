import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { CANVAS, COLORS, PARTICLES } from './constants';

interface Particle {
  x: number;
  y: number;
  radius: number;
  opacity: number;
  speed: number;
  phase: number;
  color: string;
}

export const BokehField: React.FC = () => {
  const frame = useCurrentFrame();

  const particles = useMemo<Particle[]>(() => {
    const seeded: Particle[] = [];
    for (let i = 0; i < PARTICLES.count; i++) {
      const seed = (i * 7919 + 13) % 1000;
      const seed2 = (i * 6271 + 37) % 1000;
      const seed3 = (i * 4523 + 59) % 1000;
      seeded.push({
        x: (seed / 1000) * CANVAS.width,
        y: (seed2 / 1000) * CANVAS.height,
        radius:
          PARTICLES.minRadius +
          (seed3 / 1000) * (PARTICLES.maxRadius - PARTICLES.minRadius),
        opacity:
          PARTICLES.opacityMin +
          (seed / 1000) * (PARTICLES.opacityMax - PARTICLES.opacityMin),
        speed: 0.5 + (seed2 / 1000) * PARTICLES.driftSpeed,
        phase: (seed3 / 1000) * Math.PI * 2,
        color: i % 2 === 0 ? COLORS.particleColor1 : COLORS.particleColor2,
      });
    }
    return seeded;
  }, []);

  return (
    <>
      {particles.map((p, i) => {
        const drift = frame * p.speed;
        // Diagonal drift: move both horizontally and vertically
        const px =
          ((p.x + Math.sin(p.phase + drift * 0.02) * 40 + drift * 0.15) %
            CANVAS.width +
            CANVAS.width) %
          CANVAS.width;
        const py =
          ((p.y - drift * 0.3 + Math.cos(p.phase + drift * 0.015) * 30) %
            CANVAS.height +
            CANVAS.height) %
          CANVAS.height;

        const pulseOpacity = interpolate(
          Math.sin(p.phase + frame * 0.08),
          [-1, 1],
          [p.opacity * 0.6, p.opacity],
        );

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: px - p.radius,
              top: py - p.radius,
              width: p.radius * 2,
              height: p.radius * 2,
              borderRadius: '50%',
              background: `radial-gradient(circle, ${p.color} 0%, transparent 70%)`,
              opacity: pulseOpacity,
            }}
          />
        );
      })}
    </>
  );
};

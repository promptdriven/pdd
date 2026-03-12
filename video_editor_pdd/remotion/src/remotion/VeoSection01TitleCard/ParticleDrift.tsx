import React from 'react';
import { AbsoluteFill, useCurrentFrame, random } from 'remotion';
import { COLORS, CANVAS, DIMENSIONS, ANIMATION } from './constants';

interface Particle {
  x: number;
  startY: number;
  radius: number;
  speed: number;
  opacity: number;
}

export const ParticleDrift: React.FC = () => {
  const frame = useCurrentFrame();

  const particles = React.useMemo<Particle[]>(() => {
    const result: Particle[] = [];
    for (let i = 0; i < DIMENSIONS.particleCount; i++) {
      result.push({
        x: random(`particle-x-${i}`) * CANVAS.width,
        startY: CANVAS.height + random(`particle-startY-${i}`) * CANVAS.height,
        radius:
          DIMENSIONS.particleMinRadius +
          random(`particle-r-${i}`) *
            (DIMENSIONS.particleMaxRadius - DIMENSIONS.particleMinRadius),
        speed: 1.5 + random(`particle-speed-${i}`) * 2.5,
        opacity:
          0.1 + random(`particle-opacity-${i}`) * (DIMENSIONS.particleOpacity - 0.1 + 0.05),
      });
    }
    return result;
  }, []);

  return (
    <AbsoluteFill style={{ pointerEvents: 'none' }}>
      {particles.map((p, i) => {
        const y = p.startY - p.speed * frame;
        // Wrap particles that have drifted off the top
        const wrappedY = ((y % (CANVAS.height + 40)) + CANVAS.height + 40) % (CANVAS.height + 40) - 20;

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: p.x - p.radius,
              top: wrappedY - p.radius,
              width: p.radius * 2,
              height: p.radius * 2,
              borderRadius: '50%',
              backgroundColor: COLORS.particle,
              opacity: p.opacity,
              filter: 'blur(1px)',
            }}
          />
        );
      })}
    </AbsoluteFill>
  );
};

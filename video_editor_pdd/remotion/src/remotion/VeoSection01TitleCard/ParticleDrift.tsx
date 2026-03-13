import React from 'react';
import { AbsoluteFill, useCurrentFrame, random } from 'remotion';
import { COLORS, type TitleCardLayout } from './constants';

interface Particle {
  x: number;
  startY: number;
  radius: number;
  speed: number;
  opacity: number;
}

export const ParticleDrift: React.FC<{ layout: TitleCardLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  const particles = React.useMemo<Particle[]>(() => {
    const result: Particle[] = [];
    for (let i = 0; i < layout.dimensions.particleCount; i++) {
      result.push({
        x: random(`particle-x-${i}`) * layout.width,
        startY: random(`particle-startY-${i}`) * layout.height,
        radius:
          layout.dimensions.particleMinRadius +
          random(`particle-r-${i}`) *
            (layout.dimensions.particleMaxRadius - layout.dimensions.particleMinRadius),
        speed:
          layout.dimensions.particleMinSpeed +
          random(`particle-speed-${i}`) *
            (layout.dimensions.particleMaxSpeed - layout.dimensions.particleMinSpeed),
        opacity:
          0.08 + random(`particle-opacity-${i}`) * (layout.dimensions.particleOpacity - 0.05),
      });
    }
    return result;
  }, [layout]);

  return (
    <AbsoluteFill style={{ pointerEvents: 'none' }}>
      {particles.map((p, i) => {
        // Particles drift upward; wrap from bottom when they leave the top
        const totalTravel = p.speed * frame;
        const y = p.startY - totalTravel;
        const wrappedY =
          ((y % (layout.height + 40)) + layout.height + 40) % (layout.height + 40) - 20;

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

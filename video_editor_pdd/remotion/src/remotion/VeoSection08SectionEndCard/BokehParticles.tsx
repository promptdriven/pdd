import React from 'react';
import { AbsoluteFill, useCurrentFrame, random } from 'remotion';
import { COLORS, DIMENSIONS, type EndCardLayout } from './constants';

interface BokehParticle {
  x: number;
  y: number;
  radius: number;
  opacity: number;
  speedX: number;
  speedY: number;
}

export const BokehParticles: React.FC<{ layout: EndCardLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  const particles = React.useMemo<BokehParticle[]>(() => {
    const result: BokehParticle[] = [];
    for (let i = 0; i < DIMENSIONS.bokehCount; i++) {
      const radius =
        DIMENSIONS.bokehMinRadius +
        random(`bokeh-r-${i}`) * (DIMENSIONS.bokehMaxRadius - DIMENSIONS.bokehMinRadius);
      const opacity =
        DIMENSIONS.bokehMinOpacity +
        random(`bokeh-o-${i}`) * (DIMENSIONS.bokehMaxOpacity - DIMENSIONS.bokehMinOpacity);
      // Random direction angle for drift
      const angle = random(`bokeh-a-${i}`) * Math.PI * 2;
      const speed =
        DIMENSIONS.bokehMinSpeed +
        random(`bokeh-s-${i}`) * (DIMENSIONS.bokehMaxSpeed - DIMENSIONS.bokehMinSpeed);
      result.push({
        x: random(`bokeh-x-${i}`) * layout.width,
        y: random(`bokeh-y-${i}`) * layout.height,
        radius: radius * layout.uniformScale,
        opacity,
        speedX: Math.cos(angle) * speed * layout.uniformScale,
        speedY: Math.sin(angle) * speed * layout.uniformScale,
      });
    }
    return result;
  }, [layout]);

  return (
    <AbsoluteFill style={{ pointerEvents: 'none' }}>
      {particles.map((p, i) => {
        const px =
          ((p.x + p.speedX * frame) % layout.width + layout.width) % layout.width;
        const py =
          ((p.y + p.speedY * frame) % layout.height + layout.height) % layout.height;

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
              backgroundColor: COLORS.bokeh,
              opacity: p.opacity,
              filter: `blur(${DIMENSIONS.bokehBlur * layout.uniformScale}px)`,
            }}
          />
        );
      })}
    </AbsoluteFill>
  );
};

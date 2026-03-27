import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';

/**
 * EjectedPartsStream renders a visual stream of tiny ejected parts
 * that accumulate, showing the scale of production.
 */

const PART_COLOR = '#D9944A';
const TOTAL_FRAMES = 300;

export const EjectedPartsStream: React.FC = () => {
  const frame = useCurrentFrame();

  // How many mini-parts to show — grows exponentially
  const logCount = interpolate(frame, [0, TOTAL_FRAMES], [0, Math.log(60)], {
    easing: Easing.in(Easing.exp),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });
  const partCount = Math.min(Math.round(Math.exp(logCount)), 60);

  const parts = [];
  for (let i = 0; i < partCount; i++) {
    // Arrange in a loose flowing pattern arcing upward from mold
    const col = i % 10;
    const row = Math.floor(i / 10);
    const x = 460 + col * 34 + (row % 2) * 17;
    const y = 120 + row * 34;
    const entryDelay = i * 0.5;
    const opacity = interpolate(frame, [entryDelay, entryDelay + 5], [0, 0.85], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    });
    const scale = interpolate(frame, [entryDelay, entryDelay + 8], [0.3, 1], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    });

    parts.push(
      <div
        key={i}
        style={{
          position: 'absolute',
          left: x,
          top: y,
          width: 24,
          height: 18,
          borderRadius: 4,
          background: PART_COLOR,
          opacity,
          transform: `scale(${scale})`,
          boxShadow: '0 1px 4px rgba(0,0,0,0.3)',
        }}
      />,
    );
  }

  return <>{parts}</>;
};

export default EjectedPartsStream;

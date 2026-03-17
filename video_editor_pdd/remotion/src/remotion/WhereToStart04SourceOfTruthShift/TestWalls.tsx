import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, TIMING, LAYOUT } from './constants';

/**
 * Three small amber wall icons with staggered scale-in animation,
 * each with a label below.
 */
export const TestWalls: React.FC = () => {
  const frame = useCurrentFrame();

  const wallsStartFrame = TIMING.labelsStart;

  return (
    <>
      {LAYOUT.walls.map((wall, index) => {
        const wallDelay = wallsStartFrame + index * TIMING.wallStagger;

        const scale = interpolate(
          frame,
          [wallDelay, wallDelay + TIMING.wallScaleDuration],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.cubic),
          }
        );

        const opacity = interpolate(
          frame,
          [wallDelay, wallDelay + TIMING.wallScaleDuration],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }
        );

        return (
          <div
            key={index}
            style={{
              position: 'absolute',
              left: wall.x,
              top: wall.y,
              display: 'flex',
              flexDirection: 'column',
              alignItems: 'center',
              transform: `scale(${scale})`,
              opacity,
            }}
          >
            {/* Wall icon — small rectangle */}
            <div
              style={{
                width: 8,
                height: 24,
                backgroundColor: COLORS.wallColor,
                opacity: 0.5,
                borderRadius: 2,
              }}
            />
            {/* Wall label */}
            <div
              style={{
                marginTop: 6,
                fontFamily: '"JetBrains Mono", monospace',
                fontSize: 7,
                color: COLORS.wallColor,
                opacity: 0.3,
                whiteSpace: 'nowrap',
              }}
            >
              {LAYOUT.wallLabels[index]}
            </div>
          </div>
        );
      })}
    </>
  );
};

export default TestWalls;

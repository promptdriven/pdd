import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, TEST_WALLS, TEST_WALL_Y, TIMING } from './constants';

/**
 * Three small amber "wall" icons representing test constraints,
 * staggered scale-in animation.
 */
const TestWalls: React.FC = () => {
  const frame = useCurrentFrame();
  const wallStart = TIMING.labelsStart;

  return (
    <>
      {TEST_WALLS.map((wall, i) => {
        const staggerOffset = i * TIMING.wallStagger;
        const wallFrame = wallStart + staggerOffset;

        const scale = interpolate(
          frame,
          [wallFrame, wallFrame + TIMING.wallDuration],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.cubic),
          }
        );

        const labelOpacity = interpolate(
          frame,
          [wallFrame + 5, wallFrame + TIMING.wallDuration + 5],
          [0, 0.3],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );

        return (
          <React.Fragment key={wall.label}>
            {/* Wall icon — a small rectangle */}
            <div
              style={{
                position: 'absolute',
                left: wall.x - 4,
                top: TEST_WALL_Y,
                width: 8,
                height: 24,
                backgroundColor: COLORS.amber,
                opacity: 0.5,
                borderRadius: 2,
                transform: `scale(${scale})`,
                transformOrigin: 'center bottom',
              }}
            />
            {/* Label below wall */}
            <div
              style={{
                position: 'absolute',
                left: wall.x,
                top: TEST_WALL_Y + 30,
                transform: 'translateX(-50%)',
                fontFamily: '"JetBrains Mono", monospace',
                fontSize: 7,
                color: COLORS.amber,
                opacity: labelOpacity,
                whiteSpace: 'nowrap',
              }}
            >
              {wall.label}
            </div>
          </React.Fragment>
        );
      })}
    </>
  );
};

export default TestWalls;

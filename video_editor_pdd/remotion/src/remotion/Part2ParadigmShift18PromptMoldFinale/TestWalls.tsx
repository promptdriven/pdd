import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  TEST_WALL_COLOR,
  CAVITY_X,
  CAVITY_Y,
  CAVITY_WIDTH,
  CAVITY_HEIGHT,
  WALLS_START,
  WALL_DRAW_DURATION,
  WALL_LABELS,
} from './constants';

interface WallFlashState {
  active: boolean;
  intensity: number;
}

interface TestWallsProps {
  wallFlash: WallFlashState;
}

/**
 * Four glowing test walls surrounding the code cavity.
 * Walls draw sequentially starting at WALLS_START.
 * Each wall has a label: "assert", "expect", "verify", "test".
 */
export const TestWalls: React.FC<TestWallsProps> = ({ wallFlash }) => {
  const frame = useCurrentFrame();
  const localFrame = frame - WALLS_START;

  if (localFrame < 0) return null;

  // Each wall draws in sequence, 20 frames each, staggered by 8 frames
  const wallStagger = 8;
  const wallProgresses = [0, 1, 2, 3].map((i) => {
    const wallStart = i * wallStagger;
    return interpolate(localFrame, [wallStart, wallStart + WALL_DRAW_DURATION], [0, 1], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    });
  });

  // Flash intensity for all walls
  const flashGlow = wallFlash.active ? wallFlash.intensity : 0;
  const baseGlowOpacity = 0.2;
  const glowOpacity = baseGlowOpacity + flashGlow * 0.4;
  const glowBlur = 15 + flashGlow * 15;

  const wallThickness = 3;

  // Wall definitions: top, right, bottom, left
  const walls = [
    // Top wall
    {
      left: CAVITY_X,
      top: CAVITY_Y,
      width: CAVITY_WIDTH * wallProgresses[0],
      height: wallThickness,
      labelX: CAVITY_X + CAVITY_WIDTH / 2,
      labelY: CAVITY_Y - 18,
      progress: wallProgresses[0],
    },
    // Right wall
    {
      left: CAVITY_X + CAVITY_WIDTH - wallThickness,
      top: CAVITY_Y,
      width: wallThickness,
      height: CAVITY_HEIGHT * wallProgresses[1],
      labelX: CAVITY_X + CAVITY_WIDTH + 14,
      labelY: CAVITY_Y + CAVITY_HEIGHT / 2,
      progress: wallProgresses[1],
    },
    // Bottom wall
    {
      left: CAVITY_X + CAVITY_WIDTH * (1 - wallProgresses[2]),
      top: CAVITY_Y + CAVITY_HEIGHT - wallThickness,
      width: CAVITY_WIDTH * wallProgresses[2],
      height: wallThickness,
      labelX: CAVITY_X + CAVITY_WIDTH / 2,
      labelY: CAVITY_Y + CAVITY_HEIGHT + 20,
      progress: wallProgresses[2],
    },
    // Left wall
    {
      left: CAVITY_X,
      top: CAVITY_Y + CAVITY_HEIGHT * (1 - wallProgresses[3]),
      width: wallThickness,
      height: CAVITY_HEIGHT * wallProgresses[3],
      labelX: CAVITY_X - 14,
      labelY: CAVITY_Y + CAVITY_HEIGHT / 2,
      progress: wallProgresses[3],
    },
  ];

  return (
    <>
      {/* Glow behind walls */}
      <div
        style={{
          position: 'absolute',
          left: CAVITY_X - 20,
          top: CAVITY_Y - 20,
          width: CAVITY_WIDTH + 40,
          height: CAVITY_HEIGHT + 40,
          borderRadius: 8,
          border: `2px solid ${TEST_WALL_COLOR}`,
          opacity: glowOpacity * Math.min(wallProgresses[0], 0.5) * 2,
          filter: `blur(${glowBlur}px)`,
          boxShadow: `0 0 ${glowBlur}px ${TEST_WALL_COLOR}`,
          pointerEvents: 'none',
        }}
      />

      {/* Individual walls */}
      {walls.map((wall, i) => (
        <React.Fragment key={i}>
          {/* Wall line */}
          <div
            style={{
              position: 'absolute',
              left: wall.left,
              top: wall.top,
              width: Math.max(wall.width, 0),
              height: Math.max(wall.height, 0),
              backgroundColor: TEST_WALL_COLOR,
              boxShadow: `0 0 ${glowBlur}px ${TEST_WALL_COLOR}`,
              opacity: wall.progress,
            }}
          />

          {/* Wall label */}
          {wall.progress > 0.5 && (
            <div
              style={{
                position: 'absolute',
                left: wall.labelX,
                top: wall.labelY,
                transform: 'translate(-50%, -50%)',
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 11,
                color: TEST_WALL_COLOR,
                opacity: interpolate(
                  wall.progress,
                  [0.5, 1],
                  [0, 0.78],
                  { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
                ),
                letterSpacing: 1,
                whiteSpace: 'nowrap',
              }}
            >
              {WALL_LABELS[i]}
            </div>
          )}
        </React.Fragment>
      ))}
    </>
  );
};

export default TestWalls;

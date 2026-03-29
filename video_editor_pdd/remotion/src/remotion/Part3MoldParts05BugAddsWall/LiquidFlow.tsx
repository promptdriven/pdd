import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CAVITY_X,
  CAVITY_Y,
  CAVITY_WIDTH,
  CAVITY_HEIGHT,
  LIQUID_FROM,
  LIQUID_TO,
  NOZZLE_X,
  NOZZLE_WIDTH,
  MOLD_Y,
  MOLD_WALL_THICKNESS,
  EXISTING_WALLS,
  NEW_WALL,
} from './constants';

interface LiquidFlowProps {
  /** Whether to include the new wall in the liquid mask */
  includeNewWall: boolean;
}

/**
 * Liquid inside the mold cavity. When filling, it flows from the nozzle
 * opening downward. It masks around internal walls.
 */
export const LiquidFlow: React.FC<LiquidFlowProps> = ({ includeNewWall }) => {
  const frame = useCurrentFrame();

  // Fill progress: 0 → 1 over 40 frames with custom easing
  const fillProgress = interpolate(
    frame,
    [0, 40],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.bezier(0.25, 0.1, 0.25, 1),
    }
  );

  // The liquid fills from top to bottom
  const liquidHeight = fillProgress * CAVITY_HEIGHT;
  const liquidTop = CAVITY_Y;

  // Nozzle stream (visible during early fill)
  const nozzleStreamOpacity = interpolate(
    frame,
    [0, 5, 30, 40],
    [0, 1, 1, 0.3],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const allWalls = includeNewWall ? [...EXISTING_WALLS, NEW_WALL] : EXISTING_WALLS;

  // Build clip path to cut out walls from the liquid
  // The liquid rectangle is the full cavity, clipped to fillProgress height
  const liquidClipTop = 0;
  const liquidClipBottom = fillProgress * 100;

  return (
    <>
      {/* Nozzle stream */}
      <div
        style={{
          position: 'absolute',
          left: NOZZLE_X + NOZZLE_WIDTH / 2 - 4,
          top: MOLD_Y,
          width: 8,
          height: MOLD_WALL_THICKNESS + liquidHeight,
          opacity: nozzleStreamOpacity,
          background: `linear-gradient(to bottom, ${LIQUID_FROM}, ${LIQUID_TO})`,
          borderRadius: 4,
        }}
      />

      {/* Main liquid body inside cavity */}
      <div
        style={{
          position: 'absolute',
          left: CAVITY_X,
          top: liquidTop,
          width: CAVITY_WIDTH,
          height: liquidHeight,
          background: `linear-gradient(180deg, ${LIQUID_FROM}B0 0%, ${LIQUID_TO}B0 100%)`,
          borderRadius: 2,
          overflow: 'hidden',
        }}
      >
        {/* Cut-outs for internal walls */}
        {allWalls.map((wall, i) => (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: wall.x - CAVITY_X - 2,
              top: wall.y - liquidTop - 2,
              width: wall.width + 4,
              height: wall.height + 4,
              backgroundColor: '#0D1117',
              borderRadius: 3,
            }}
          />
        ))}

        {/* Shimmer / surface highlight */}
        <div
          style={{
            position: 'absolute',
            left: 0,
            top: 0,
            width: '100%',
            height: 4,
            background: `linear-gradient(90deg, transparent, ${LIQUID_FROM}60, transparent)`,
            opacity: fillProgress > 0.05 ? 0.8 : 0,
          }}
        />
      </div>
    </>
  );
};

/**
 * Liquid drain animation — existing liquid fades out top-to-bottom.
 */
export const LiquidDrain: React.FC = () => {
  const frame = useCurrentFrame();

  // Drain: top fades first, bottom last — 20 frames
  const drainProgress = interpolate(
    frame,
    [0, 20],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  // Overall opacity fades out
  const opacity = 1 - drainProgress;

  // The liquid "surface" drops
  const visibleHeight = CAVITY_HEIGHT * (1 - drainProgress);

  return (
    <div
      style={{
        position: 'absolute',
        left: CAVITY_X,
        top: CAVITY_Y + (CAVITY_HEIGHT - visibleHeight),
        width: CAVITY_WIDTH,
        height: visibleHeight,
        background: `linear-gradient(180deg, ${LIQUID_FROM}B0 0%, ${LIQUID_TO}B0 100%)`,
        borderRadius: 2,
        opacity,
        overflow: 'hidden',
      }}
    >
      {/* Wall cut-outs for existing walls only */}
      {EXISTING_WALLS.map((wall, i) => (
        <div
          key={i}
          style={{
            position: 'absolute',
            left: wall.x - CAVITY_X - 2,
            top: wall.y - (CAVITY_Y + (CAVITY_HEIGHT - visibleHeight)) - 2,
            width: wall.width + 4,
            height: wall.height + 4,
            backgroundColor: '#0D1117',
            borderRadius: 3,
          }}
        />
      ))}
    </div>
  );
};

import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS, GRID_CONFIG, ICONS_DATA, TIMING } from './constants';
import { IconCell } from './IconCell';

/**
 * AnimationSection06IconGridAnimation
 *
 * A 3x3 grid of animated icons with staggered entry animations,
 * synchronized pulse effects, and labels. Icons scale in row-by-row
 * with slight rotation and overshoot, then pulse together.
 */
export const AnimationSection06IconGridAnimation: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(to bottom, ${COLORS.backgroundStart}, ${COLORS.backgroundEnd})`,
      }}
    >
      {/* Icon Grid Container */}
      <div
        style={{
          position: 'absolute',
          left: '50%',
          top: '50%',
          transform: 'translate(-50%, -50%)',
          display: 'grid',
          gridTemplateColumns: `repeat(${GRID_CONFIG.columns}, ${GRID_CONFIG.cellSize}px)`,
          gridTemplateRows: `repeat(${GRID_CONFIG.rows}, ${GRID_CONFIG.cellSize}px)`,
          gap: `${GRID_CONFIG.gapVertical}px ${GRID_CONFIG.gapHorizontal}px`,
          justifyItems: 'center',
          alignItems: 'center',
        }}
      >
        {ICONS_DATA.map((iconData) => {
          // Calculate delay based on row and column
          const rowDelay = iconData.row * TIMING.rowStagger;
          const colDelay = iconData.col * TIMING.iconStagger;
          const totalDelay = rowDelay + colDelay;

          return (
            <div
              key={iconData.id}
              style={{
                gridColumn: iconData.col + 1,
                gridRow: iconData.row + 1,
              }}
            >
              <IconCell
                icon={iconData.icon}
                color={iconData.color}
                label={iconData.label}
                delay={totalDelay}
              />
            </div>
          );
        })}
      </div>
    </AbsoluteFill>
  );
};

export const defaultAnimationSection06IconGridAnimationProps = {};

export default AnimationSection06IconGridAnimation;

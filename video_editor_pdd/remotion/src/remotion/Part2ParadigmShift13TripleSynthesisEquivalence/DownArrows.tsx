import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  ARROW_COLOR,
  CANVAS_WIDTH,
  CODE_Y,
  CODE_HEIGHT,
  COLUMN_POSITIONS,
  COLUMN_Y,
  ARROWS_DURATION,
} from './constants';

/**
 * Three arrows drawn from the code block down to each netlist column.
 * Animate over ARROWS_DURATION frames with easeInOut cubic.
 */
const DownArrows: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(frame, [0, ARROWS_DURATION], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });

  const startY = CODE_Y + CODE_HEIGHT + 5;
  const endY = COLUMN_Y - 35;
  const centerX = CANVAS_WIDTH / 2;

  return (
    <svg
      width={CANVAS_WIDTH}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
    >
      {COLUMN_POSITIONS.map((colX, i) => {
        // Arrow line from center-bottom of code block to top of each column
        const currentEndY = startY + (endY - startY) * drawProgress;
        const currentEndX = centerX + (colX - centerX) * drawProgress;

        // Arrowhead at the tip
        const arrowHeadSize = 8;
        const opacity = interpolate(drawProgress, [0, 0.1], [0, 0.85], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        });

        return (
          <g key={i} opacity={opacity}>
            <line
              x1={centerX}
              y1={startY}
              x2={currentEndX}
              y2={currentEndY}
              stroke={ARROW_COLOR}
              strokeWidth={2}
              strokeDasharray="4 3"
            />
            {drawProgress > 0.9 && (
              <polygon
                points={`${colX},${endY} ${colX - arrowHeadSize},${endY - arrowHeadSize * 1.5} ${colX + arrowHeadSize},${endY - arrowHeadSize * 1.5}`}
                fill={ARROW_COLOR}
                opacity={interpolate(drawProgress, [0.9, 1], [0, 1], {
                  extrapolateLeft: 'clamp',
                  extrapolateRight: 'clamp',
                })}
              />
            )}
          </g>
        );
      })}
    </svg>
  );
};

export default DownArrows;

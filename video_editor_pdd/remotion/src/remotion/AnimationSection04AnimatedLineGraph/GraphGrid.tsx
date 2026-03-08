import React from 'react';
import { interpolate, useCurrentFrame } from 'remotion';
import { COLORS, GRAPH_AREA, DIMENSIONS } from './constants';

interface GraphGridProps {
  verticalLines: number;
  horizontalLines: number;
  fadeInDuration: number;
}

export const GraphGrid: React.FC<GraphGridProps> = ({
  verticalLines,
  horizontalLines,
  fadeInDuration,
}) => {
  const frame = useCurrentFrame();
  const opacity = interpolate(frame, [0, fadeInDuration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const verticalSpacing = DIMENSIONS.graphWidth / (verticalLines - 1);
  const horizontalSpacing = DIMENSIONS.graphHeight / (horizontalLines - 1);

  return (
    <svg
      width={DIMENSIONS.canvasWidth}
      height={DIMENSIONS.canvasHeight}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <g opacity={opacity}>
        {/* Vertical grid lines */}
        {Array.from({ length: verticalLines }).map((_, i) => {
          const x = GRAPH_AREA.left + i * verticalSpacing;
          return (
            <line
              key={`v-${i}`}
              x1={x}
              y1={GRAPH_AREA.top}
              x2={x}
              y2={GRAPH_AREA.bottom}
              stroke={COLORS.gridLine}
              strokeWidth={1}
            />
          );
        })}

        {/* Horizontal grid lines */}
        {Array.from({ length: horizontalLines }).map((_, i) => {
          const y = GRAPH_AREA.top + i * horizontalSpacing;
          return (
            <line
              key={`h-${i}`}
              x1={GRAPH_AREA.left}
              y1={y}
              x2={GRAPH_AREA.right}
              y2={y}
              stroke={COLORS.gridLine}
              strokeWidth={1}
            />
          );
        })}
      </g>
    </svg>
  );
};

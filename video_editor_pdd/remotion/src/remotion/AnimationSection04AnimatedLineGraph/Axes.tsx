import React from 'react';
import { interpolate, useCurrentFrame } from 'remotion';
import { COLORS, GRAPH_AREA, DIMENSIONS, DATA, TYPOGRAPHY } from './constants';

interface AxesProps {
  fadeInDuration: number;
}

export const Axes: React.FC<AxesProps> = ({ fadeInDuration }) => {
  const frame = useCurrentFrame();
  const opacity = interpolate(frame, [0, fadeInDuration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const yLabels = [0, 25, 50, 75, 100];
  const yLabelSpacing = DIMENSIONS.graphHeight / (yLabels.length - 1);

  const xLabelSpacing = DIMENSIONS.graphWidth / (DATA.xLabels.length - 1);

  return (
    <div style={{ position: 'absolute', top: 0, left: 0, opacity }}>
      {/* Y-axis labels */}
      {yLabels.map((label, i) => {
        const y = GRAPH_AREA.bottom - i * yLabelSpacing;
        return (
          <div
            key={`y-${label}`}
            style={{
              position: 'absolute',
              left: 260,
              top: y - 7,
              fontFamily: TYPOGRAPHY.axisLabel.fontFamily,
              fontWeight: TYPOGRAPHY.axisLabel.fontWeight,
              fontSize: TYPOGRAPHY.axisLabel.fontSize,
              color: COLORS.axisLabel,
              textAlign: 'right',
              width: 40,
            }}
          >
            {label}
          </div>
        );
      })}

      {/* X-axis labels */}
      {DATA.xLabels.map((label, i) => {
        const x = GRAPH_AREA.left + i * xLabelSpacing;
        return (
          <div
            key={`x-${label}`}
            style={{
              position: 'absolute',
              left: x - 20,
              top: 890,
              fontFamily: TYPOGRAPHY.axisLabel.fontFamily,
              fontWeight: TYPOGRAPHY.axisLabel.fontWeight,
              fontSize: TYPOGRAPHY.axisLabel.fontSize,
              color: COLORS.axisLabel,
              textAlign: 'center',
              width: 40,
            }}
          >
            {label}
          </div>
        );
      })}
    </div>
  );
};

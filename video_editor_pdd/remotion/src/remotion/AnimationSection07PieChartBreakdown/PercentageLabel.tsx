import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { CHART, LABEL } from './constants';

interface PercentageLabelProps {
  angle: number;
  percentage: number;
  color: string;
  index: number;
}

export const PercentageLabel: React.FC<PercentageLabelProps> = ({
  angle,
  percentage,
  color,
  index,
}) => {
  const frame = useCurrentFrame();

  // Stagger fade-in for each label
  const fadeProgress = interpolate(
    frame,
    [index * 5, index * 5 + 10],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.ease),
    }
  );

  // Calculate label position outside the pie
  const angleRad = (angle * Math.PI) / 180;
  const labelDistance = CHART.RADIUS + LABEL.LINE_LENGTH;

  const lineStartX = CHART.CENTER_X + CHART.RADIUS * Math.cos(angleRad);
  const lineStartY = CHART.CENTER_Y + CHART.RADIUS * Math.sin(angleRad);

  const lineEndX = CHART.CENTER_X + labelDistance * Math.cos(angleRad);
  const lineEndY = CHART.CENTER_Y + labelDistance * Math.sin(angleRad);

  const labelX = CHART.CENTER_X + (labelDistance + 40) * Math.cos(angleRad);
  const labelY = CHART.CENTER_Y + (labelDistance + 40) * Math.sin(angleRad);

  const text = `${percentage}%`;

  return (
    <g opacity={fadeProgress}>
      {/* Connecting line */}
      <line
        x1={lineStartX}
        y1={lineStartY}
        x2={lineEndX}
        y2={lineEndY}
        stroke={color}
        strokeWidth={LABEL.LINE_WIDTH}
      />

      {/* Label background */}
      <rect
        x={labelX - 35}
        y={labelY - 20}
        width={70}
        height={40}
        rx={8}
        fill="#1E293B"
        opacity={LABEL.BACKGROUND_OPACITY}
      />

      {/* Percentage text */}
      <text
        x={labelX}
        y={labelY}
        textAnchor="middle"
        dominantBaseline="middle"
        fill={LABEL.COLOR}
        fontSize={LABEL.FONT_SIZE}
        fontWeight="bold"
        fontFamily="Inter, sans-serif"
      >
        {text}
      </text>
    </g>
  );
};

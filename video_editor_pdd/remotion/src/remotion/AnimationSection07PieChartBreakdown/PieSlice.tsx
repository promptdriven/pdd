import React from 'react';
import { interpolate, spring, useCurrentFrame, useVideoConfig, Easing } from 'remotion';
import { CHART } from './constants';

interface PieSliceProps {
  startAngle: number;
  endAngle: number;
  color: string;
  explode: boolean;
}

export const PieSlice: React.FC<PieSliceProps> = ({
  startAngle,
  endAngle,
  color,
  explode,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Draw animation with easeOutCubic
  const drawProgress = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Pop-out animation with easeOutBack (slight overshoot)
  const popProgress = spring({
    frame,
    fps,
    config: {
      damping: 10,
      mass: 0.5,
      stiffness: 100,
    },
  });

  const currentEndAngle = startAngle + (endAngle - startAngle) * drawProgress;

  // Calculate explode offset if needed
  let offsetX = 0;
  let offsetY = 0;

  if (explode) {
    const midAngle = (startAngle + endAngle) / 2;
    const midRad = (midAngle * Math.PI) / 180;
    offsetX = Math.cos(midRad) * CHART.EXPLODE_OFFSET * popProgress;
    offsetY = Math.sin(midRad) * CHART.EXPLODE_OFFSET * popProgress;
  }

  // Create SVG path for pie slice
  const createPiePath = () => {
    const centerX = CHART.CENTER_X + offsetX;
    const centerY = CHART.CENTER_Y + offsetY;
    const radius = CHART.RADIUS;

    const startRad = (startAngle * Math.PI) / 180;
    const endRad = (currentEndAngle * Math.PI) / 180;

    const x1 = centerX + radius * Math.cos(startRad);
    const y1 = centerY + radius * Math.sin(startRad);
    const x2 = centerX + radius * Math.cos(endRad);
    const y2 = centerY + radius * Math.sin(endRad);

    const largeArcFlag = currentEndAngle - startAngle > 180 ? 1 : 0;

    return `
      M ${centerX} ${centerY}
      L ${x1} ${y1}
      A ${radius} ${radius} 0 ${largeArcFlag} 1 ${x2} ${y2}
      Z
    `;
  };

  return (
    <svg
      width={CHART.CENTER_X * 2}
      height={CHART.CENTER_Y * 2}
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
      }}
    >
      <path d={createPiePath()} fill={color} />
    </svg>
  );
};

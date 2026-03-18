import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { CONNECTION_COLOR, SYNOPSYS_Y, PDD_Y } from './constants';

interface DashedConnectionProps {
  x: number;
  delay: number;
  drawDuration: number;
}

export const DashedConnection: React.FC<DashedConnectionProps> = ({
  x,
  delay,
  drawDuration,
}) => {
  // useCurrentFrame() is already relative to the parent <Sequence>
  const frame = useCurrentFrame();
  const relFrame = frame - delay;

  // The connection runs from below the top row icons to above the bottom row icons
  const topY = SYNOPSYS_Y + 55;
  const bottomY = PDD_Y - 55;
  const lineHeight = bottomY - topY;

  const progress = interpolate(
    relFrame,
    [0, drawDuration],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  if (progress <= 0) return null;

  const drawnHeight = lineHeight * progress;

  return (
    <svg
      style={{
        position: 'absolute',
        left: x - 1,
        top: topY,
        width: 2,
        height: lineHeight,
        overflow: 'visible',
      }}
    >
      <line
        x1={1}
        y1={0}
        x2={1}
        y2={drawnHeight}
        stroke={CONNECTION_COLOR}
        strokeWidth={1}
        strokeDasharray="6 4"
        opacity={0.15}
      />
    </svg>
  );
};

export default DashedConnection;

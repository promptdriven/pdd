import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';

const SplitDivider: React.FC<{
  x: number;
  color: string;
  drawDuration: number;
}> = ({ x, color, drawDuration }) => {
  const frame = useCurrentFrame();

  const height = interpolate(frame, [0, drawDuration], [0, 1080], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: x - 1,
        top: 0,
        width: 2,
        height,
        backgroundColor: color,
        opacity: 0.25,
      }}
    />
  );
};

export default SplitDivider;

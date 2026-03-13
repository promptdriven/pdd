import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, type EndCardLayout } from './constants';

export const CheckmarkIcon: React.FC<{ layout: EndCardLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  const { checkmarkSize, checkmarkStrokeWidth, ringCenterX, ringCenterY } = layout.dimensions;

  // Scale in from 0 → 1 with back(1.5) bounce (frames 40-55)
  const scale = interpolate(
    frame,
    [ANIMATION.checkmarkStart, ANIMATION.checkmarkEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.5)),
    },
  );

  const svgSize = checkmarkSize * 1.5;

  return (
    <div
      style={{
        position: 'absolute',
        left: ringCenterX - svgSize / 2,
        top: ringCenterY - svgSize / 2,
        width: svgSize,
        height: svgSize,
        transform: `scale(${scale})`,
        opacity: frame >= ANIMATION.checkmarkStart ? 1 : 0,
      }}
    >
      <svg
        width={svgSize}
        height={svgSize}
        viewBox="0 0 40 40"
        fill="none"
      >
        <path
          d="M 10 20 L 17 27 L 30 13"
          stroke={COLORS.checkmark}
          strokeWidth={checkmarkStrokeWidth}
          strokeLinecap="round"
          strokeLinejoin="round"
        />
      </svg>
    </div>
  );
};

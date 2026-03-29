import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { ARROW_THICKNESS, ARROW_LENGTH, ARROW_DRAW_DURATION } from './constants';

interface FlowArrowProps {
  color: string;
  appearFrame: number;
}

export const FlowArrow: React.FC<FlowArrowProps> = ({ color, appearFrame }) => {
  const frame = useCurrentFrame();

  // Arrow draws in after step appears (5 frames after step)
  const drawStart = appearFrame + 5;
  const progress = interpolate(
    frame,
    [drawStart, drawStart + ARROW_DRAW_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const lineHeight = (ARROW_LENGTH - 6) * progress;
  const arrowHeadOpacity = progress > 0.7 ? interpolate(progress, [0.7, 1], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }) : 0;

  return (
    <div
      style={{
        width: 20,
        height: ARROW_LENGTH,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        justifyContent: 'flex-start',
      }}
    >
      {/* Vertical line */}
      <div
        style={{
          width: ARROW_THICKNESS,
          height: lineHeight,
          backgroundColor: color,
          borderRadius: 1,
        }}
      />
      {/* Arrow head */}
      <svg
        width={10}
        height={8}
        viewBox="0 0 10 8"
        style={{ opacity: arrowHeadOpacity, marginTop: -1 }}
      >
        <path d="M5 8 L0 0 L10 0 Z" fill={color} />
      </svg>
    </div>
  );
};

export default FlowArrow;

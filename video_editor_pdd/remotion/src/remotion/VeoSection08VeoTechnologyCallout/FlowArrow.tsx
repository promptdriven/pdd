import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface FlowArrowProps {
  drawStartFrame: number;
  drawEndFrame: number;
}

export const FlowArrow: React.FC<FlowArrowProps> = ({
  drawStartFrame,
  drawEndFrame,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [drawStartFrame, drawEndFrame],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(2)),
    },
  );

  const lineWidth = 60;
  const arrowHeadSize = 8;
  const totalWidth = lineWidth + arrowHeadSize;

  return (
    <div
      style={{
        width: totalWidth,
        height: 80,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        flexShrink: 0,
      }}
    >
      <svg
        width={totalWidth}
        height="20"
        viewBox={`0 0 ${totalWidth} 20`}
      >
        {/* Line that draws left to right */}
        <line
          x1={0}
          y1={10}
          x2={lineWidth * progress}
          y2={10}
          stroke="rgba(255, 255, 255, 0.4)"
          strokeWidth={2}
        />
        {/* Arrowhead — appears after line is mostly drawn */}
        {progress > 0.7 && (
          <polygon
            points={`${lineWidth},${10 - arrowHeadSize / 2} ${lineWidth + arrowHeadSize},10 ${lineWidth},${10 + arrowHeadSize / 2}`}
            fill="rgba(255, 255, 255, 0.4)"
            opacity={interpolate(
              progress,
              [0.7, 1],
              [0, 1],
              { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
            )}
          />
        )}
      </svg>
    </div>
  );
};

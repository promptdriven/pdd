import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface ConnectingArrowProps {
  fromX: number;
  toX: number;
  y: number;
  animStartFrame: number;
  animDuration: number;
  label?: string;
}

/**
 * Horizontal arrow between stage columns with optional label.
 */
const ConnectingArrow: React.FC<ConnectingArrowProps> = ({
  fromX,
  toX,
  y,
  animStartFrame,
  animDuration,
  label,
}) => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [animStartFrame, animStartFrame + animDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const arrowLen = toX - fromX;
  const currentLen = arrowLen * drawProgress;
  const arrowHeadSize = 8;

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
        pointerEvents: 'none',
      }}
    >
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {/* Arrow line */}
        <line
          x1={fromX}
          y1={y}
          x2={fromX + currentLen}
          y2={y}
          stroke="#334155"
          strokeWidth={2}
          opacity={0.3}
        />

        {/* Arrowhead */}
        {drawProgress > 0.8 && (
          <polygon
            points={`${fromX + currentLen},${y} ${fromX + currentLen - arrowHeadSize},${y - arrowHeadSize / 2} ${fromX + currentLen - arrowHeadSize},${y + arrowHeadSize / 2}`}
            fill="#334155"
            opacity={0.3 * interpolate(drawProgress, [0.8, 1], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
          />
        )}
      </svg>

      {/* Label above arrow */}
      {label && (
        <div
          style={{
            position: 'absolute',
            left: fromX,
            top: y - 20,
            width: arrowLen,
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 9,
            color: '#64748B',
            opacity: 0.3 * drawProgress,
            whiteSpace: 'nowrap',
          }}
        >
          {label}
        </div>
      )}
    </div>
  );
};

export default ConnectingArrow;

import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';

interface DashedCircleProps {
  cx: number;
  cy: number;
  radius: number;
  color: string;
  strokeOpacity: number;
  strokeWidth: number;
  drawDuration: number;
  label: string;
  labelColor: string;
  labelOpacity: number;
  startFrame: number;
}

export const DashedCircle: React.FC<DashedCircleProps> = ({
  cx,
  cy,
  radius,
  color,
  strokeOpacity,
  strokeWidth,
  drawDuration,
  label,
  labelColor,
  labelOpacity,
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  const circumference = 2 * Math.PI * radius;

  // Animate the circle drawing clockwise
  const drawProgress = interpolate(
    localFrame,
    [0, drawDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const dashOffset = circumference * (1 - drawProgress);

  // Label fades in slightly after circle starts
  const labelAlpha = interpolate(
    localFrame,
    [drawDuration * 0.5, drawDuration],
    [0, labelOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: '100%',
        height: '100%',
        pointerEvents: 'none',
      }}
    >
      <svg
        width="1920"
        height="1080"
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', left: 0, top: 0 }}
      >
        <circle
          cx={cx}
          cy={cy}
          r={radius}
          fill="none"
          stroke={color}
          strokeOpacity={strokeOpacity}
          strokeWidth={strokeWidth}
          strokeDasharray={`8 6`}
          strokeDashoffset={dashOffset}
          style={{
            // Rotate so drawing starts from top
            transformOrigin: `${cx}px ${cy}px`,
            transform: 'rotate(-90deg)',
          }}
        />
      </svg>
      {/* Label below circle */}
      <div
        style={{
          position: 'absolute',
          left: cx - 120,
          top: cy + radius + 12,
          width: 240,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 10,
          fontWeight: 500,
          color: labelColor,
          opacity: labelAlpha,
        }}
      >
        {label}
      </div>
    </div>
  );
};

export default DashedCircle;

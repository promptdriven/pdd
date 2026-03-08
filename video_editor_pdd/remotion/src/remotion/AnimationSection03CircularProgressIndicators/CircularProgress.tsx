/**
 * CircularProgress component - renders an animated circular progress indicator
 */

import React from 'react';
import { interpolate, useCurrentFrame, useVideoConfig, Easing } from 'remotion';
import { TYPOGRAPHY } from './constants';

interface CircularProgressProps {
  center: [number, number];
  radius: number;
  thickness: number;
  progress: number;
  color: string;
  label: string;
  duration: number;
}

export const CircularProgress: React.FC<CircularProgressProps> = ({
  center,
  radius,
  thickness,
  progress,
  color,
  label,
  duration,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Arc animation: 0° → target degrees (easeOutCubic)
  const targetDegrees = (progress / 100) * 360;
  const currentDegrees = interpolate(
    frame,
    [0, duration],
    [0, targetDegrees],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // Number counting: 0 → target value (easeOutQuart)
  const currentValue = Math.round(
    interpolate(
      frame,
      [0, duration],
      [0, progress],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.poly(4)),
      }
    )
  );

  const [cx, cy] = center;

  // Create SVG path for arc
  const createArcPath = (degrees: number): string => {
    if (degrees <= 0) return '';
    if (degrees >= 360) degrees = 359.99; // Prevent full circle issues

    const startAngle = -90; // Start at 12 o'clock
    const endAngle = startAngle + degrees;

    const startRad = (startAngle * Math.PI) / 180;
    const endRad = (endAngle * Math.PI) / 180;

    const r = radius - thickness / 2;
    const startX = r * Math.cos(startRad);
    const startY = r * Math.sin(startRad);
    const endX = r * Math.cos(endRad);
    const endY = r * Math.sin(endRad);

    const largeArcFlag = degrees > 180 ? 1 : 0;

    return `M ${startX} ${startY} A ${r} ${r} 0 ${largeArcFlag} 1 ${endX} ${endY}`;
  };

  const arcPath = createArcPath(currentDegrees);

  return (
    <>
      {/* Progress arc */}
      <svg
        width={radius * 2 + 20}
        height={radius * 2 + 20}
        style={{
          position: 'absolute',
          left: cx - radius - 10,
          top: cy - radius - 10,
        }}
      >
        <g transform={`translate(${radius + 10}, ${radius + 10})`}>
          <path
            d={arcPath}
            fill="none"
            stroke={color}
            strokeWidth={thickness}
            strokeLinecap="round"
          />
        </g>
      </svg>

      {/* Center percentage text */}
      <div
        style={{
          position: 'absolute',
          left: cx,
          top: cy,
          transform: 'translate(-50%, -50%)',
          fontFamily: TYPOGRAPHY.percentage.fontFamily,
          fontWeight: TYPOGRAPHY.percentage.fontWeight,
          fontSize: TYPOGRAPHY.percentage.fontSize,
          color: color,
          textAlign: 'center',
        }}
      >
        {currentValue}%
      </div>
    </>
  );
};

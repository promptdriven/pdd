// RadialFlash.tsx — Bright radial glow that appears at a point and fades out
import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface RadialFlashProps {
  /** X position in pixels */
  cx: number;
  /** Y position in pixels */
  cy: number;
  /** Maximum radius of the glow */
  maxRadius: number;
  /** Frame when the flash starts */
  startFrame: number;
  /** Duration of the flash in frames */
  duration: number;
  /** Flash color */
  color: string;
}

export const RadialFlash: React.FC<RadialFlashProps> = ({
  cx,
  cy,
  maxRadius,
  startFrame,
  duration,
  color,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [startFrame, startFrame + Math.floor(duration * 0.2), startFrame + duration],
    [0, 1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.exp),
    }
  );

  const radius = interpolate(
    frame,
    [startFrame, startFrame + duration],
    [maxRadius * 0.3, maxRadius],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.exp),
    }
  );

  if (frame < startFrame || frame > startFrame + duration + 10) {
    return null;
  }

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
    >
      <defs>
        <radialGradient id={`flash-grad-${startFrame}`}>
          <stop offset="0%" stopColor={color} stopOpacity={1} />
          <stop offset="50%" stopColor={color} stopOpacity={0.5} />
          <stop offset="100%" stopColor={color} stopOpacity={0} />
        </radialGradient>
      </defs>
      <circle
        cx={cx}
        cy={cy}
        r={radius}
        fill={`url(#flash-grad-${startFrame})`}
        opacity={opacity}
      />
      {/* Bright center dot */}
      <circle
        cx={cx}
        cy={cy}
        r={4}
        fill={color}
        opacity={opacity * 0.9}
      />
    </svg>
  );
};

export default RadialFlash;

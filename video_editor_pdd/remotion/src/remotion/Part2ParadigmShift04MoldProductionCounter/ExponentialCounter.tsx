import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';

/**
 * ExponentialCounter renders a large animated number that accelerates
 * exponentially from `start` to `end` over the total duration.
 */

interface ExponentialCounterProps {
  start: number;
  end: number;
  fontSize: number;
  color: string;
  labelColor: string;
  labelOpacity: number;
  x: number;
  y: number;
  totalFrames: number;
}

export const ExponentialCounter: React.FC<ExponentialCounterProps> = ({
  start,
  end,
  fontSize,
  color,
  labelColor,
  labelOpacity,
  x,
  y,
  totalFrames,
}) => {
  const frame = useCurrentFrame();

  // Exponential interpolation: interpolate in log space
  const logStart = Math.log(start);
  const logEnd = Math.log(end);

  const easedProgress = interpolate(frame, [0, totalFrames], [0, 1], {
    easing: Easing.in(Easing.exp),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const logValue = logStart + (logEnd - logStart) * easedProgress;
  const rawValue = Math.exp(logValue);
  const value = Math.min(Math.round(rawValue), end);

  // Format number with commas
  const formattedValue = value.toLocaleString('en-US');

  // Subtle pulse when crossing milestones
  const milestones = [10, 100, 1000, 10000];
  let pulseScale = 1;
  for (const m of milestones) {
    // Find the frame at which we cross this milestone
    const mProgress = (Math.log(m) - logStart) / (logEnd - logStart);
    const mFrame = interpolate(mProgress, [0, 1], [0, totalFrames], {
      easing: Easing.in(Easing.exp),
    });
    const distFromMilestone = Math.abs(frame - mFrame);
    if (distFromMilestone < 10) {
      const pulseT = 1 - distFromMilestone / 10;
      pulseScale = Math.max(pulseScale, 1 + pulseT * 0.08);
    }
  }

  // Glow intensity increases with value
  const glowIntensity = interpolate(frame, [0, totalFrames], [0, 0.8], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        transform: `scale(${pulseScale})`,
        transformOrigin: 'center center',
      }}
    >
      {/* Counter number */}
      <div
        style={{
          fontFamily: 'JetBrains Mono, monospace',
          fontSize,
          fontWeight: 700,
          color,
          textShadow: `0 0 ${20 + glowIntensity * 30}px rgba(74,144,217,${glowIntensity}), 0 0 60px rgba(74,144,217,${glowIntensity * 0.3})`,
          lineHeight: 1,
          letterSpacing: '-0.02em',
          width: 360,
          textAlign: 'center',
        }}
      >
        {formattedValue}
      </div>

      {/* Label */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 18,
          fontWeight: 400,
          color: labelColor,
          opacity: labelOpacity,
          marginTop: 12,
          letterSpacing: '0.08em',
          textTransform: 'uppercase',
          textAlign: 'center',
        }}
      >
        parts produced
      </div>
    </div>
  );
};

export default ExponentialCounter;

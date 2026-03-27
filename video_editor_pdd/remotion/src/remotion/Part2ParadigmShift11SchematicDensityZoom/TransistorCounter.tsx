// ============================================================
// TransistorCounter.tsx – Exponentially-increasing counter
// shown in the lower-right corner.
// ============================================================
import React from 'react';
import { interpolate, Easing } from 'remotion';

interface TransistorCounterProps {
  frame: number;
  totalFrames: number;
  startValue: number;
  endValue: number;
  counterColor: string;
  labelColor: string;
  counterFontSize: number;
  labelFontSize: number;
  x: number;
  y: number;
}

export const TransistorCounter: React.FC<TransistorCounterProps> = ({
  frame,
  totalFrames,
  startValue,
  endValue,
  counterColor,
  labelColor,
  counterFontSize,
  labelFontSize,
  x,
  y,
}) => {
  // Exponential counter using log interpolation
  // easeIn(expo) equivalent: Easing.in(Easing.exp)
  // But we'll use log-space interpolation for smooth exponential feel
  const progress = interpolate(frame, [0, totalFrames], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.exp),
  });

  // Exponential interpolation in log-space
  const logStart = Math.log(startValue);
  const logEnd = Math.log(endValue);
  const currentValue = Math.round(Math.exp(logStart + progress * (logEnd - logStart)));

  // Format with commas
  const formatted = currentValue.toLocaleString('en-US');

  return (
    <div
      style={{
        position: x === 0 && y === 0 ? 'relative' : 'absolute',
        left: x || undefined,
        top: y || undefined,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'flex-end',
        zIndex: 1,
      }}
    >
      <span
        style={{
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: counterFontSize,
          fontWeight: 400,
          color: counterColor,
          lineHeight: 1.2,
          letterSpacing: '-0.02em',
        }}
      >
        {formatted}
      </span>
      <span
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: labelFontSize,
          fontWeight: 400,
          color: labelColor,
          marginTop: 2,
        }}
      >
        transistors
      </span>
    </div>
  );
};

import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface ComparisonBarProps {
  centerX: number;
  y: number;
  totalWidth: number;
  leftWidth: number;
  rightWidth: number;
  leftColor: string;
  rightColor: string;
  label: string;
  callout: string;
  calloutColor: string;
  labelColor: string;
  appearStart: number;
  appearDuration: number;
}

const ComparisonBar: React.FC<ComparisonBarProps> = ({
  centerX,
  y,
  totalWidth,
  leftWidth,
  rightWidth,
  leftColor,
  rightColor,
  label,
  callout,
  calloutColor,
  labelColor,
  appearStart,
  appearDuration,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [appearStart, appearStart + appearDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const barLeft = centerX - totalWidth / 2;
  const barHeight = 14;
  const gap = 6;

  const animatedLeftWidth = leftWidth * progress;
  const animatedRightWidth = rightWidth * progress;

  return (
    <div
      style={{
        position: 'absolute',
        left: barLeft,
        top: y,
        width: totalWidth,
        opacity: progress,
      }}
    >
      {/* Label above bar */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          color: labelColor,
          textAlign: 'center',
          marginBottom: 10,
        }}
      >
        {label}
      </div>

      {/* Bar segments */}
      <div
        style={{
          display: 'flex',
          alignItems: 'center',
          gap,
          justifyContent: 'center',
        }}
      >
        {/* Left segment (50 lines) */}
        <div
          style={{
            width: animatedLeftWidth,
            height: barHeight,
            backgroundColor: leftColor,
            opacity: 0.3,
            borderRadius: 4,
          }}
        />

        {/* Right segment (10 lines) */}
        <div
          style={{
            width: animatedRightWidth,
            height: barHeight,
            backgroundColor: rightColor,
            opacity: 0.3,
            borderRadius: 4,
          }}
        />

        {/* Callout */}
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 14,
            fontWeight: 700,
            color: calloutColor,
            marginLeft: 12,
            whiteSpace: 'nowrap',
          }}
        >
          {callout}
        </div>
      </div>
    </div>
  );
};

export default ComparisonBar;

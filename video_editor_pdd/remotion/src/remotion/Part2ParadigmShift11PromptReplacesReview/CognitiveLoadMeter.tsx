import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

export const CognitiveLoadMeter: React.FC<{
  x: number;
  y: number;
  width: number;
  fillPercent: number;
  color: string;
  label: string;
  status: string;
  appearStart: number;
}> = ({ x, y, width, fillPercent, color, label, status, appearStart }) => {
  const frame = useCurrentFrame();

  const meterOpacity = interpolate(
    frame,
    [appearStart, appearStart + 15],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const fillWidth = interpolate(
    frame,
    [appearStart, appearStart + 30],
    [0, (fillPercent / 100) * width],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const statusOpacity = interpolate(
    frame,
    [appearStart + 15, appearStart + 30],
    [0, 0.6],
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
        left: x - width / 2,
        top: y - 20,
        width,
        opacity: meterOpacity,
      }}
    >
      {/* Label */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 10,
          color,
          opacity: 0.4,
          marginBottom: 4,
          textAlign: 'center',
        }}
      >
        {label}
      </div>

      {/* Bar background */}
      <div
        style={{
          width,
          height: 16,
          backgroundColor: 'rgba(255, 255, 255, 0.05)',
          borderRadius: 8,
          overflow: 'hidden',
        }}
      >
        {/* Bar fill */}
        <div
          style={{
            width: fillWidth,
            height: '100%',
            backgroundColor: color,
            opacity: 0.5,
            borderRadius: 8,
          }}
        />
      </div>

      {/* Status label */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 10,
          fontWeight: 700,
          color,
          opacity: statusOpacity,
          marginTop: 4,
          textAlign: 'center',
        }}
      >
        {status}
      </div>
    </div>
  );
};

import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface CardHeaderProps {
  text: string;
}

export const CardHeader: React.FC<CardHeaderProps> = ({ text }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [0, 20],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  return (
    <div
      style={{
        textAlign: 'center',
        marginBottom: 24,
        opacity,
      }}
    >
      <span
        style={{
          color: '#FFFFFF',
          fontSize: 22,
          fontFamily: 'Inter, sans-serif',
          fontWeight: 700,
          letterSpacing: '1px',
        }}
      >
        {text}
      </span>
    </div>
  );
};

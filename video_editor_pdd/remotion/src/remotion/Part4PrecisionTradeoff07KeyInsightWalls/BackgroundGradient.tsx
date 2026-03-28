import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface BackgroundGradientProps {
  leftColor: string;
  rightColor: string;
  baseOpacity: number;
  fadeInDuration: number;
}

export const BackgroundGradient: React.FC<BackgroundGradientProps> = ({
  leftColor,
  rightColor,
  baseOpacity,
  fadeInDuration,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, fadeInDuration], [0, baseOpacity], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
        background: `radial-gradient(ellipse at 25% 50%, ${leftColor} 0%, transparent 60%), radial-gradient(ellipse at 75% 50%, ${rightColor} 0%, transparent 60%)`,
        opacity,
      }}
    />
  );
};

export default BackgroundGradient;

import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface RadialGlowProps {
  startFrame: number;
  fadeDuration: number;
  centerX: number;
  centerY: number;
  radius: number;
  color: string;
  glowOpacity: number;
}

export const RadialGlow: React.FC<RadialGlowProps> = ({
  startFrame,
  fadeDuration,
  centerX,
  centerY,
  radius,
  color,
  glowOpacity,
}) => {
  const frame = useCurrentFrame();
  const elapsed = frame - startFrame;

  if (elapsed < 0) return null;

  const opacity = interpolate(elapsed, [0, fadeDuration], [0, glowOpacity], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: centerX - radius,
        top: centerY - radius,
        width: radius * 2,
        height: radius * 2,
        borderRadius: '50%',
        background: `radial-gradient(circle, ${color} 0%, transparent 70%)`,
        opacity,
        pointerEvents: 'none',
      }}
    />
  );
};

export default RadialGlow;

/**
 * TotalTime - Total time display at bottom of each workflow
 */

import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface TotalTimeProps {
  text: string;
  x: number;
  y: number;
  color: string;
  startFrame?: number;
}

export const TotalTime: React.FC<TotalTimeProps> = ({
  text,
  x,
  y,
  color,
  startFrame = 90,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame - startFrame,
    [0, 20],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.ease),
    }
  );

  const scale = interpolate(
    frame - startFrame,
    [0, 20],
    [0.8, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        transform: `translate(-50%, 0) scale(${scale})`,
        opacity,
        fontFamily: 'Inter, sans-serif',
        fontWeight: 900,
        fontSize: 28,
        color,
        textAlign: 'center',
        textTransform: 'uppercase',
        letterSpacing: '0.05em',
      }}
    >
      {text}
    </div>
  );
};

import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface HorizontalRuleProps {
  y: number;
  maxWidth: number;
  color: string;
  opacity: number;
  thickness: number;
  drawStart: number;
  drawDuration: number;
}

export const HorizontalRule: React.FC<HorizontalRuleProps> = ({
  y,
  maxWidth,
  color,
  opacity,
  thickness,
  drawStart,
  drawDuration,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [drawStart, drawStart + drawDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  const currentWidth = maxWidth * progress;

  return (
    <div
      style={{
        position: 'absolute',
        top: y - thickness / 2,
        left: '50%',
        transform: 'translateX(-50%)',
        width: currentWidth,
        height: thickness,
        backgroundColor: color,
        opacity,
      }}
    />
  );
};

export default HorizontalRule;

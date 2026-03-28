import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface HorizontalRuleProps {
  startFrame: number;
  drawDuration: number;
  centerX: number;
  centerY: number;
  halfWidth: number;
  color: string;
  ruleOpacity: number;
}

export const HorizontalRule: React.FC<HorizontalRuleProps> = ({
  startFrame,
  drawDuration,
  centerX,
  centerY,
  halfWidth,
  color,
  ruleOpacity,
}) => {
  const frame = useCurrentFrame();
  const elapsed = frame - startFrame;

  if (elapsed < 0) return null;

  const progress = interpolate(elapsed, [0, drawDuration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.quad),
  });

  const currentHalfWidth = halfWidth * progress;

  return (
    <div
      style={{
        position: 'absolute',
        left: centerX - currentHalfWidth,
        top: centerY,
        width: currentHalfWidth * 2,
        height: 2,
        backgroundColor: color,
        opacity: ruleOpacity,
      }}
    />
  );
};

export default HorizontalRule;

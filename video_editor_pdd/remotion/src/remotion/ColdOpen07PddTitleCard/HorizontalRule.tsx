import React from 'react';
import { Easing, interpolate, useCurrentFrame } from 'remotion';
import { CANVAS, COLORS, RULE, TIMING } from './constants';

/**
 * Horizontal rule that draws from center outward.
 * Appears at TIMING.RULE_START and takes TIMING.RULE_DURATION frames to draw.
 */
export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < TIMING.RULE_START) return null;

  const localFrame = frame - TIMING.RULE_START;

  // Draw progress: 0 → 1 over RULE_DURATION frames
  const progress = interpolate(
    localFrame,
    [0, TIMING.RULE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const currentWidth = RULE.WIDTH * progress;
  const centerX = CANVAS.WIDTH / 2;

  return (
    <div
      style={{
        position: 'absolute',
        top: RULE.Y,
        left: centerX - currentWidth / 2,
        width: currentWidth,
        height: RULE.HEIGHT,
        backgroundColor: COLORS.TITLE,
        opacity: RULE.OPACITY,
      }}
    />
  );
};

import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, LAYOUT, ANIMATION } from './constants';

interface WaveTextProps {
  text: string;
}

export const WaveText: React.FC<WaveTextProps> = ({ text }) => {
  const frame = useCurrentFrame();
  const relativeFrame = frame - ANIMATION.wave.startFrame;

  const chars = text.split('');

  return (
    <div
      style={{
        position: 'absolute',
        top: LAYOUT.emphasis.y,
        left: LAYOUT.emphasis.x,
        transform: 'translate(-50%, -50%)',
        display: 'flex',
        alignItems: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: TYPOGRAPHY.emphasis.fontSize,
        fontWeight: TYPOGRAPHY.emphasis.fontWeight,
        letterSpacing: TYPOGRAPHY.emphasis.letterSpacing,
        color: COLORS.emphasis,
        whiteSpace: 'nowrap',
        textTransform: TYPOGRAPHY.emphasis.textTransform,
      }}
    >
      {chars.map((char, index) => {
        const charStartFrame = index * ANIMATION.wave.stagger;
        const charEndFrame = charStartFrame + ANIMATION.wave.durationPerChar;

        // Scale animation with back easing (overshoot)
        const scale = interpolate(
          relativeFrame,
          [charStartFrame, charStartFrame + ANIMATION.wave.durationPerChar / 2, charEndFrame],
          [ANIMATION.wave.scaleMin, ANIMATION.wave.scaleMax, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.bezier(0.68, -0.55, 0.265, 1.55), // easeInOutBack
          }
        );

        // Vertical shift with easeOutQuad
        const translateY = interpolate(
          relativeFrame,
          [charStartFrame, charEndFrame],
          [-ANIMATION.wave.verticalShift, 0],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.bezier(0.25, 0.46, 0.45, 0.94), // easeOutQuad
          }
        );

        return (
          <span
            key={index}
            style={{
              display: 'inline-block',
              transform: `scale(${scale}) translateY(${translateY}px)`,
              transformOrigin: 'center center',
            }}
          >
            {char === ' ' ? '\u00A0' : char}
          </span>
        );
      })}
    </div>
  );
};

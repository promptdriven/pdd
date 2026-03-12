import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, DIMENSIONS, ANIMATION_TIMING, TITLE_TEXT } from './constants';

export const StaggeredText: React.FC = () => {
  const frame = useCurrentFrame();
  const characters = TITLE_TEXT.split('');

  // Float animation after hold starts (frame 60+)
  const floatY = frame >= ANIMATION_TIMING.holdStart
    ? Math.sin((frame - ANIMATION_TIMING.holdStart) * 0.1) * DIMENSIONS.floatAmplitude
    : 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        right: 0,
        top: 0,
        bottom: 0,
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
        transform: `translateY(${floatY}px)`,
      }}
    >
      <div style={{ display: 'flex' }}>
        {characters.map((char, i) => {
          const charStart = ANIMATION_TIMING.titleStaggerStart + i * ANIMATION_TIMING.letterStaggerFrames;
          const charEnd = charStart + 8; // ~267ms fade per letter

          const opacity = interpolate(
            frame,
            [charStart, charEnd],
            [0, 1],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.quad),
            }
          );

          const translateY = interpolate(
            frame,
            [charStart, charEnd],
            [ANIMATION_TIMING.letterTranslateY, 0],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.quad),
            }
          );

          return (
            <span
              key={i}
              style={{
                fontFamily: TYPOGRAPHY.title.fontFamily,
                fontSize: TYPOGRAPHY.title.fontSize,
                fontWeight: TYPOGRAPHY.title.fontWeight,
                color: COLORS.titleText,
                opacity,
                transform: `translateY(${translateY}px)`,
                display: 'inline-block',
                whiteSpace: 'pre',
              }}
            >
              {char}
            </span>
          );
        })}
      </div>
    </div>
  );
};

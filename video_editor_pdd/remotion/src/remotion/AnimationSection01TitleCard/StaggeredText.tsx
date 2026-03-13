import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, DIMENSIONS, ANIMATION_TIMING, TITLE_TEXT } from './constants';
import { resolveBoundedStagger } from '../_shared/staggered-reveal';

export const StaggeredText: React.FC = () => {
  const frame = useCurrentFrame();
  const characters = TITLE_TEXT.split('');
  const stagger = resolveBoundedStagger({
    itemCount: characters.length,
    startFrame: ANIMATION_TIMING.titleStaggerStart,
    endFrame: ANIMATION_TIMING.dividerExpandStart,
    desiredStepFrames: ANIMATION_TIMING.framesPerChar,
    defaultFadeFrames: 5,
  });

  // Gentle floating after frame 25: ±2px sinusoidal
  const floatY = frame >= ANIMATION_TIMING.holdStart
    ? Math.sin((frame - ANIMATION_TIMING.holdStart) * 0.3) * DIMENSIONS.floatAmplitude
    : 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        right: 0,
        top: '50%',
        transform: `translateY(calc(-50% + ${DIMENSIONS.titleOffsetY + floatY}px))`,
        display: 'flex',
        justifyContent: 'center',
      }}
    >
      <div style={{ display: 'flex' }}>
        {characters.map((char, i) => {
          const charStart = ANIMATION_TIMING.titleStaggerStart + i * stagger.stepFrames;
          const charEnd = charStart + stagger.fadeFrames;

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
            [DIMENSIONS.letterTranslateY, 0],
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
                letterSpacing: TYPOGRAPHY.title.letterSpacing,
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

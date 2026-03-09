import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION } from './constants';

const TITLE_TEXT = 'VEO SECTION';

export const LetterRevealTitle: React.FC = () => {
  const frame = useCurrentFrame();
  const letters = TITLE_TEXT.split('');

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        right: 0,
        bottom: 0,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
      }}
    >
      <div
        style={{
          display: 'flex',
          flexDirection: 'row',
          alignItems: 'center',
        }}
      >
        {letters.map((letter, index) => {
          const letterStart =
            ANIMATION.letterRevealStart +
            index * ANIMATION.letterStaggerFrames;
          const letterEnd = letterStart + 8;

          const opacity = interpolate(
            frame,
            [letterStart, letterEnd],
            [0, 1],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.cubic),
            },
          );

          return (
            <span
              key={index}
              style={{
                fontFamily: TYPOGRAPHY.title.fontFamily,
                fontSize: TYPOGRAPHY.title.fontSize,
                fontWeight: TYPOGRAPHY.title.fontWeight,
                letterSpacing: TYPOGRAPHY.title.letterSpacing,
                color: COLORS.titleText,
                textTransform: 'uppercase',
                opacity,
                display: 'inline-block',
                minWidth: letter === ' ' ? 20 : undefined,
              }}
            >
              {letter}
            </span>
          );
        })}
      </div>
    </div>
  );
};

import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { NARRATION, COLORS, TYPOGRAPHY, ANIMATION } from './constants';

export const WordByWordReveal: React.FC = () => {
  const frame = useCurrentFrame();

  const { words, framesPerWord, wordFadeDuration } = NARRATION;

  return (
    <div
      style={{
        position: 'absolute',
        left: NARRATION.centerX - NARRATION.maxWidth / 2,
        top: NARRATION.centerY - 30,
        width: NARRATION.maxWidth,
        display: 'flex',
        flexWrap: 'wrap',
        justifyContent: 'center',
        gap: '0 12px',
      }}
    >
      {words.map((word, i) => {
        const wordStartFrame =
          ANIMATION.wordRevealStart + i * framesPerWord;

        // Each word fades from inactive to active over wordFadeDuration frames
        const wordOpacity = interpolate(
          frame,
          [wordStartFrame, wordStartFrame + wordFadeDuration],
          [0.4, 1.0],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          },
        );

        // Subtle scale pop on reveal
        const wordScale = interpolate(
          frame,
          [wordStartFrame, wordStartFrame + wordFadeDuration],
          [0.97, 1.0],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          },
        );

        // Initial appearance: words before reveal start are dim but visible
        const isBeforeReveal = frame < ANIMATION.wordRevealStart;
        const displayOpacity = isBeforeReveal ? 0.4 : wordOpacity;

        return (
          <span
            key={i}
            style={{
              fontFamily: TYPOGRAPHY.narration.fontFamily,
              fontSize: TYPOGRAPHY.narration.fontSize,
              fontWeight: TYPOGRAPHY.narration.fontWeight,
              lineHeight: TYPOGRAPHY.narration.lineHeight,
              color:
                displayOpacity >= 0.95
                  ? COLORS.activeWord
                  : COLORS.inactiveWord,
              opacity: displayOpacity,
              transform: `scale(${isBeforeReveal ? 1 : wordScale})`,
              display: 'inline-block',
              whiteSpace: 'nowrap',
            }}
          >
            {word}
          </span>
        );
      })}
    </div>
  );
};

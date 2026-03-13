import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { NARRATION, COLORS, TYPOGRAPHY, ANIMATION } from './constants';

export const WordByWordReveal: React.FC = () => {
  const frame = useCurrentFrame();

  const { words, framesPerWord, wordFadeDuration } = NARRATION;

  // Which word index is currently being highlighted
  const activeWordIndex = Math.floor(
    (frame - ANIMATION.wordRevealStart) / framesPerWord,
  );

  // All words fully revealed once the last word's reveal completes
  const allRevealed =
    frame >= ANIMATION.wordRevealStart + words.length * framesPerWord;

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

        const isBeforeReveal = frame < ANIMATION.wordRevealStart;

        let wordOpacity: number;
        let wordScale = 1.0;

        if (allRevealed) {
          // Frame 34+: all narration text fully visible
          wordOpacity = 1.0;
        } else if (isBeforeReveal) {
          // Before frame 6: all words dim
          wordOpacity = 0.4;
        } else if (i === activeWordIndex) {
          // Current word: crossfade from dim (0.4) to bright (1.0)
          wordOpacity = interpolate(
            frame,
            [wordStartFrame, wordStartFrame + wordFadeDuration],
            [0.4, 1.0],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.quad),
            },
          );
          // Subtle scale pop on current word
          wordScale = interpolate(
            frame,
            [wordStartFrame, wordStartFrame + wordFadeDuration],
            [0.97, 1.0],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.quad),
            },
          );
        } else if (i < activeWordIndex) {
          // Past words stay bright after being highlighted
          wordOpacity = 1.0;
        } else {
          // Future words stay dim
          wordOpacity = 0.4;
        }

        return (
          <span
            key={i}
            style={{
              fontFamily: TYPOGRAPHY.narration.fontFamily,
              fontSize: TYPOGRAPHY.narration.fontSize,
              fontWeight: TYPOGRAPHY.narration.fontWeight,
              lineHeight: TYPOGRAPHY.narration.lineHeight,
              color:
                wordOpacity >= 0.95
                  ? COLORS.activeWord
                  : COLORS.inactiveWord,
              opacity: wordOpacity,
              transform: `scale(${wordScale})`,
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

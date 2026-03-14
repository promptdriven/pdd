import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { NARRATION_WORDS, COLORS, TYPOGRAPHY, ANIMATION, DIMENSIONS } from './constants';

export const WordByWordText: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <div
      style={{
        position: 'absolute',
        top: DIMENSIONS.textY,
        left: '50%',
        transform: 'translateX(-50%)',
        maxWidth: DIMENSIONS.textMaxWidth,
        display: 'flex',
        flexWrap: 'wrap',
        justifyContent: 'center',
        gap: '0 12px',
      }}
    >
      {NARRATION_WORDS.map((word, i) => {
        // Each word starts appearing at wordStart + i * framesPerWord
        const wordStartFrame = ANIMATION.wordStart + i * ANIMATION.framesPerWord;
        const wordEndFrame = wordStartFrame + ANIMATION.framesPerWord;

        // Opacity: 0→1 over framesPerWord duration, easeOutCubic
        const wordOpacity = interpolate(
          frame,
          [wordStartFrame, wordEndFrame],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.cubic),
          },
        );

        // Slide up: +8px → 0px over framesPerWord duration, easeOutCubic
        const wordTranslateY = interpolate(
          frame,
          [wordStartFrame, wordEndFrame],
          [ANIMATION.wordShiftPx, 0],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.cubic),
          },
        );

        return (
          <span
            key={i}
            style={{
              fontFamily: TYPOGRAPHY.narration.fontFamily,
              fontSize: TYPOGRAPHY.narration.fontSize,
              fontWeight: TYPOGRAPHY.narration.fontWeight,
              lineHeight: TYPOGRAPHY.narration.lineHeight,
              color: COLORS.narrationText,
              opacity: wordOpacity,
              transform: `translateY(${wordTranslateY}px)`,
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

import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, LAYOUT, ANIMATION, TEXT_CONTENT } from './constants';

interface WordFadeTextProps {
  words: readonly string[];
  separator: string;
}

export const WordFadeText: React.FC<WordFadeTextProps> = ({ words, separator }) => {
  const frame = useCurrentFrame();
  const relativeFrame = frame - ANIMATION.subtitle.startFrame;

  const renderWord = (word: string, index: number) => {
    const wordStartFrame = index * ANIMATION.subtitle.wordStagger;
    const wordEndFrame = wordStartFrame + ANIMATION.subtitle.fadeDuration;

    const opacity = interpolate(
      relativeFrame,
      [wordStartFrame, wordEndFrame],
      [0, 1],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.bezier(0.42, 0, 0.58, 1), // easeInOutQuad
      }
    );

    return (
      <span key={`word-${index}`} style={{ opacity }}>
        {word}
      </span>
    );
  };

  const renderSeparator = (index: number) => {
    // Separator appears slightly before the next word
    const sepStartFrame = index * ANIMATION.subtitle.wordStagger + ANIMATION.subtitle.fadeDuration;
    const sepEndFrame = sepStartFrame + 3;

    const opacity = interpolate(
      relativeFrame,
      [sepStartFrame, sepEndFrame],
      [0, 1],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.bezier(0.42, 0, 0.58, 1),
      }
    );

    return (
      <span
        key={`sep-${index}`}
        style={{
          opacity,
          color: COLORS.separator,
          margin: '0 12px',
        }}
      >
        {separator}
      </span>
    );
  };

  return (
    <div
      style={{
        position: 'absolute',
        top: LAYOUT.subtitle.y,
        left: LAYOUT.subtitle.x,
        transform: 'translate(-50%, -50%)',
        display: 'flex',
        alignItems: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: TYPOGRAPHY.subtitle.fontSize,
        fontWeight: TYPOGRAPHY.subtitle.fontWeight,
        letterSpacing: TYPOGRAPHY.subtitle.letterSpacing,
        color: COLORS.subtitle,
        whiteSpace: 'nowrap',
      }}
    >
      {words.map((word, index) => (
        <React.Fragment key={index}>
          {renderWord(word, index)}
          {index < words.length - 1 && renderSeparator(index)}
        </React.Fragment>
      ))}
    </div>
  );
};

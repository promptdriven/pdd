import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { COLORS, HIGHLIGHTED_PHRASES, TIMING, type HighlightedPhrase } from './constants';

interface WordByWordProps {
  text: string;
  startFrame: number;
  highlightStartFrame: number;
}

/**
 * Splits text into words, fades each in sequentially, then applies
 * color highlights to matched phrases after highlightStartFrame.
 */
export const WordByWord: React.FC<WordByWordProps> = ({
  text,
  startFrame,
  highlightStartFrame,
}) => {
  const frame = useCurrentFrame();
  const words = text.split(' ');

  /**
   * Check if a word at a given index is part of a highlighted phrase.
   * Returns the highlight config if found, or null.
   */
  const getHighlightForWordIndex = (
    wordIndex: number
  ): (HighlightedPhrase & { phraseWordStart: number; phraseWordEnd: number }) | null => {
    const joinedWords = words.join(' ');
    for (const phrase of HIGHLIGHTED_PHRASES) {
      const phraseIndex = joinedWords.indexOf(phrase.text);
      if (phraseIndex === -1) continue;

      // Count which word index this phrase starts and ends at
      const before = joinedWords.slice(0, phraseIndex);
      const phraseWordStart = before === '' ? 0 : before.trim().split(/\s+/).length;
      const phraseWordCount = phrase.text.split(/\s+/).length;
      const phraseWordEnd = phraseWordStart + phraseWordCount - 1;

      if (wordIndex >= phraseWordStart && wordIndex <= phraseWordEnd) {
        return { ...phrase, phraseWordStart, phraseWordEnd };
      }
    }
    return null;
  };

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: 460,
        transform: 'translateX(-50%)',
        maxWidth: 1000,
        textAlign: 'center',
        lineHeight: 1.6,
        fontFamily: 'Inter, sans-serif',
        fontSize: 32,
        fontWeight: 400,
      }}
    >
      {words.map((word, i) => {
        // Each word appears at startFrame + i * framesPerWord
        const wordAppearFrame = startFrame + i * TIMING.framesPerWord;

        // Word fade-in opacity
        const wordOpacity = interpolate(
          frame,
          [wordAppearFrame, wordAppearFrame + TIMING.wordFadeDuration],
          [0, 0.85],
          {
            easing: Easing.out(Easing.quad),
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }
        );

        const highlight = getHighlightForWordIndex(i);

        // If this word is part of a highlighted phrase, transition its color
        let color = COLORS.quoteText;
        let fontWeight: number = 400;
        let fontStyle: 'normal' | 'italic' = 'normal';
        let textShadow = 'none';
        let finalOpacity = wordOpacity;

        if (highlight) {
          const highlightProgress = interpolate(
            frame,
            [
              highlightStartFrame,
              highlightStartFrame + TIMING.highlightTransitionDuration,
            ],
            [0, 1],
            {
              easing: Easing.inOut(Easing.cubic),
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
            }
          );

          if (highlightProgress > 0) {
            color = highlight.color;
            fontWeight = highlight.weight ?? 400;
            fontStyle = highlight.italic ? 'italic' : 'normal';

            const highlightOpacity = highlight.opacity ?? 1.0;
            // Blend from base 0.85 to target opacity
            finalOpacity = interpolate(
              highlightProgress,
              [0, 1],
              [wordOpacity, wordOpacity > 0 ? highlightOpacity : 0]
            );

            if (highlight.glowBlur && highlight.glowOpacity) {
              const glowAlpha = interpolate(
                frame,
                [highlightStartFrame, highlightStartFrame + 15],
                [0, highlight.glowOpacity],
                {
                  easing: Easing.out(Easing.quad),
                  extrapolateLeft: 'clamp',
                  extrapolateRight: 'clamp',
                }
              );
              textShadow = `0 0 ${highlight.glowBlur}px ${highlight.color}${Math.round(glowAlpha * 255)
                .toString(16)
                .padStart(2, '0')}`;
            }
          }
        }

        return (
          <span
            key={i}
            style={{
              display: 'inline',
              color,
              opacity: finalOpacity,
              fontWeight,
              fontStyle,
              textShadow,
              transition: 'none',
            }}
          >
            {word}
            {i < words.length - 1 ? ' ' : ''}
          </span>
        );
      })}
    </div>
  );
};

export default WordByWord;

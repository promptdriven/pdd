import React from 'react';
import { interpolate, Easing } from 'remotion';
import { WORD_STAGGER_FRAMES } from './constants';

interface StaggeredLineProps {
  /** Frame relative to the start of this line's Sequence */
  localFrame: number;
  /** The words/segments to render — each item is a React node */
  children: React.ReactNode[];
}

/**
 * Fades in each child element (word) with a stagger.
 * `localFrame` starts at 0 when the line's Sequence begins.
 */
export const StaggeredLine: React.FC<StaggeredLineProps> = ({
  localFrame,
  children,
}) => {
  return (
    <>
      {React.Children.map(children, (child, i) => {
        const wordStart = i * WORD_STAGGER_FRAMES;
        const wordOpacity = interpolate(
          localFrame,
          [wordStart, wordStart + 10],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          },
        );
        const wordY = interpolate(
          localFrame,
          [wordStart, wordStart + 10],
          [6, 0],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          },
        );
        return (
          <span
            style={{
              opacity: wordOpacity,
              transform: `translateY(${wordY}px)`,
              display: 'inline-block',
            }}
          >
            {child}
          </span>
        );
      })}
    </>
  );
};

export default StaggeredLine;

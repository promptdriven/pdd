import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  TEXT_FADE_START,
  TEXT_FADE_END,
  TEXT_COLOR,
  TEXT_OPACITY,
  ACCENT_COLOR,
  ACCENT_OPACITY,
  TEXT_SIZE,
  TEXT_WEIGHT,
  LETTER_SPACING,
} from './constants';

/**
 * The central question: "So why are we still patching?"
 * Fades in over 30 frames (frame 30–60).
 * "patching?" is rendered in a warm amber accent color.
 */
export const QuestionText: React.FC = () => {
  const frame = useCurrentFrame();

  const textOpacity = interpolate(
    frame,
    [TEXT_FADE_START, TEXT_FADE_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        opacity: textOpacity,
      }}
    >
      <span
        style={{
          fontFamily: '"Inter", "Helvetica Neue", Arial, sans-serif',
          fontSize: TEXT_SIZE,
          fontWeight: TEXT_WEIGHT,
          letterSpacing: LETTER_SPACING,
          lineHeight: 1.4,
        }}
      >
        <span style={{ color: TEXT_COLOR, opacity: TEXT_OPACITY }}>
          So why are we still{' '}
        </span>
        <span style={{ color: ACCENT_COLOR, opacity: ACCENT_OPACITY }}>
          patching?
        </span>
      </span>
    </div>
  );
};

export default QuestionText;

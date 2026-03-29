import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  INSIGHT_TEXT,
  TEXT_COLOR,
  TEXT_OPACITY,
  TEXT_FONT_SIZE,
  TEXT_FONT_WEIGHT,
  TEXT_Y,
  TEXT_FADE_IN_START,
  TEXT_FADE_IN_END,
  TEXT_FADE_OUT_START,
  TEXT_FADE_OUT_END,
} from './constants';

/**
 * The insight text that fades in slowly, holds, then fades out.
 */
export const InsightText: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in: TEXT_FADE_IN_START..TEXT_FADE_IN_END with easeOut(quad)
  const fadeIn = interpolate(
    frame,
    [TEXT_FADE_IN_START, TEXT_FADE_IN_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Fade out: TEXT_FADE_OUT_START..TEXT_FADE_OUT_END with easeIn(quad)
  const fadeOut = interpolate(
    frame,
    [TEXT_FADE_OUT_START, TEXT_FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  const opacity = fadeIn * fadeOut * TEXT_OPACITY;

  if (frame < TEXT_FADE_IN_START) return null;

  return (
    <div
      style={{
        position: 'absolute',
        top: TEXT_Y,
        left: 0,
        width: '100%',
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
        transform: 'translateY(-50%)',
      }}
    >
      <span
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: TEXT_FONT_SIZE,
          fontWeight: TEXT_FONT_WEIGHT,
          color: TEXT_COLOR,
          opacity,
          letterSpacing: '0.02em',
          textAlign: 'center',
        }}
      >
        {INSIGHT_TEXT}
      </span>
    </div>
  );
};

export default InsightText;

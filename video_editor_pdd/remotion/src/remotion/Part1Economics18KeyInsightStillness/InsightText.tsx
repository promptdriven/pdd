import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  INSIGHT_TEXT,
  TEXT_COLOR,
  TEXT_OPACITY,
  TEXT_Y,
  TEXT_FONT_SIZE,
  TEXT_FONT_WEIGHT,
  TEXT_FONT_FAMILY,
  CANVAS_WIDTH,
  TEXT_FADE_IN_START,
  TEXT_FADE_IN_DURATION,
  TEXT_FADE_OUT_START,
  TEXT_FADE_OUT_DURATION,
} from './constants';

/**
 * The quiet insight text that fades in, holds, then fades out.
 */
export const InsightText: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in: 90 → 150
  const fadeIn = interpolate(
    frame,
    [TEXT_FADE_IN_START, TEXT_FADE_IN_START + TEXT_FADE_IN_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Fade out: 300 → 330
  const fadeOut = interpolate(
    frame,
    [TEXT_FADE_OUT_START, TEXT_FADE_OUT_START + TEXT_FADE_OUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  const opacity = fadeIn * fadeOut * TEXT_OPACITY;

  if (opacity <= 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        top: TEXT_Y,
        left: 0,
        width: CANVAS_WIDTH,
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
      }}
    >
      <span
        style={{
          fontFamily: TEXT_FONT_FAMILY,
          fontSize: TEXT_FONT_SIZE,
          fontWeight: TEXT_FONT_WEIGHT,
          color: TEXT_COLOR,
          opacity,
          textAlign: 'center',
          lineHeight: 1.5,
        }}
      >
        {INSIGHT_TEXT}
      </span>
    </div>
  );
};

export default InsightText;

import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  TITLE_TEXT,
  TITLE_Y,
  TITLE_FONT_SIZE,
  TITLE_COLOR,
  TITLE_OPACITY,
  TITLE_LETTER_SPACING,
  TITLE_FADE_START,
  TITLE_FADE_DURATION,
} from './constants';

export const TitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [TITLE_FADE_START, TITLE_FADE_START + TITLE_FADE_DURATION],
    [0, TITLE_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'flex-start',
        alignItems: 'center',
        zIndex: 1,
      }}
    >
      <div
        style={{
          position: 'absolute',
          top: TITLE_Y - TITLE_FONT_SIZE / 2,
          fontFamily: 'Inter, sans-serif',
          fontSize: TITLE_FONT_SIZE,
          fontWeight: 700,
          color: TITLE_COLOR,
          opacity,
          letterSpacing: TITLE_LETTER_SPACING,
          textAlign: 'center',
          whiteSpace: 'nowrap',
        }}
      >
        {TITLE_TEXT}
      </div>
    </AbsoluteFill>
  );
};

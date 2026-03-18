import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  URL_TEXT,
  URL_Y,
  URL_FONT_SIZE,
  URL_COLOR,
  URL_OPACITY,
  URL_UNDERLINE_OPACITY,
  URL_FADE_START,
  URL_FADE_DURATION,
} from './constants';

export const UrlText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [URL_FADE_START, URL_FADE_START + URL_FADE_DURATION],
    [0, 1],
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
        zIndex: 3,
      }}
    >
      <div
        style={{
          position: 'absolute',
          top: URL_Y - URL_FONT_SIZE / 2,
          opacity,
          textAlign: 'center',
        }}
      >
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: URL_FONT_SIZE,
            fontWeight: 600,
            color: URL_COLOR,
            opacity: URL_OPACITY,
          }}
        >
          {URL_TEXT}
        </span>
        {/* Subtle underline */}
        <div
          style={{
            width: '100%',
            height: 1,
            backgroundColor: URL_COLOR,
            opacity: URL_UNDERLINE_OPACITY,
            marginTop: 4,
          }}
        />
      </div>
    </AbsoluteFill>
  );
};

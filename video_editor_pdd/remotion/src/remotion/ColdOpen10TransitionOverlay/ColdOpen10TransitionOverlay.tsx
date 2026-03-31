import React from 'react';
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from 'remotion';

import {
  BG_OVERLAY_COLOR,
  BG_FINAL_BLACK,
  TEXT_COLOR_MAIN,
  TEXT_COLOR_EMPHASIS,
  TEXT_FONT_SIZE,
  TEXT_FONT_WEIGHT_MAIN,
  TEXT_FONT_WEIGHT_EMPHASIS,
  TEXT_FONT_FAMILY,
  TEXT_CONTENT_BEFORE,
  TEXT_CONTENT_EMPHASIS,
  TEXT_CONTENT_AFTER,
  OVERLAY_RAMP_START,
  OVERLAY_RAMP_END,
  OVERLAY_MAX_OPACITY,
  TEXT_FADE_START,
  TEXT_FADE_END,
  FADE_TO_BLACK_START,
  FADE_TO_BLACK_END,
} from './constants';

export const defaultColdOpen10TransitionOverlayProps = {};

export const ColdOpen10TransitionOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  // Dark overlay ramp: 0→0.85 over frames 0-20, easeOut(quad)
  const overlayOpacity = interpolate(
    frame,
    [OVERLAY_RAMP_START, OVERLAY_RAMP_END],
    [0, OVERLAY_MAX_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Text fade-in: 0→1 over frames 20-40, easeOut(quad)
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

  // Fade-to-black: 0→1 over frames 70-90, easeIn(quad)
  const fadeToBlackOpacity = interpolate(
    frame,
    [FADE_TO_BLACK_START, FADE_TO_BLACK_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  // Text fades out together with the fade-to-black
  const textFinalOpacity = interpolate(
    frame,
    [FADE_TO_BLACK_START, FADE_TO_BLACK_END],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  const combinedTextOpacity = textOpacity * textFinalOpacity;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_OVERLAY_COLOR,
      }}
    >
      {/* Dark overlay that ramps up to obscure previous content */}
      <AbsoluteFill
        style={{
          backgroundColor: BG_OVERLAY_COLOR,
          opacity: overlayOpacity,
        }}
      />

      {/* Centered transition text */}
      <AbsoluteFill
        style={{
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
          opacity: combinedTextOpacity,
        }}
      >
        <span
          style={{
            fontFamily: TEXT_FONT_FAMILY,
            fontSize: TEXT_FONT_SIZE,
            fontWeight: TEXT_FONT_WEIGHT_MAIN,
            color: TEXT_COLOR_MAIN,
            lineHeight: 1.4,
            textAlign: 'center',
            maxWidth: 800,
          }}
        >
          {TEXT_CONTENT_BEFORE}
          <span
            style={{
              fontWeight: TEXT_FONT_WEIGHT_EMPHASIS,
              color: TEXT_COLOR_EMPHASIS,
            }}
          >
            {TEXT_CONTENT_EMPHASIS}
          </span>
          {TEXT_CONTENT_AFTER}
        </span>
      </AbsoluteFill>

      {/* Fade to full black for clean transition */}
      <AbsoluteFill
        style={{
          backgroundColor: BG_FINAL_BLACK,
          opacity: fadeToBlackOpacity,
        }}
      />
    </AbsoluteFill>
  );
};

export default ColdOpen10TransitionOverlay;

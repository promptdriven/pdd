import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CALLOUT_BG,
  CALLOUT_NUMBER_COLOR,
  CALLOUT_SUBTITLE_COLOR,
  CALLOUT_SOURCE_COLOR,
  CALLOUT_FADE_START,
  CALLOUT_FADE_DURATION,
  NUMBER_SCALE_START,
  NUMBER_SCALE_DURATION,
} from './constants';

export const CISQCallout: React.FC = () => {
  const frame = useCurrentFrame();

  // Card fade-in
  const cardOpacity = interpolate(
    frame,
    [CALLOUT_FADE_START, CALLOUT_FADE_START + CALLOUT_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // "$1.52T" scale emphasis with back easing
  const numberScale = interpolate(
    frame,
    [
      NUMBER_SCALE_START,
      NUMBER_SCALE_START + NUMBER_SCALE_DURATION,
    ],
    [0.6, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.4)),
    },
  );

  const numberOpacity = interpolate(
    frame,
    [NUMBER_SCALE_START, NUMBER_SCALE_START + 10],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  if (cardOpacity <= 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: 1100,
        top: 450,
        transform: 'translate(-50%, -50%)',
        opacity: cardOpacity,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        padding: '24px 32px',
        backgroundColor: CALLOUT_BG,
        borderRadius: 12,
        // Subtle bg opacity effect
      }}
    >
      {/* $1.52T number */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 48,
          fontWeight: 700,
          color: CALLOUT_NUMBER_COLOR,
          textAlign: 'center',
          transform: `scale(${numberScale})`,
          opacity: numberOpacity,
          lineHeight: 1.2,
        }}
      >
        $1.52T
      </div>

      {/* Subtitle */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 16,
          color: CALLOUT_SUBTITLE_COLOR,
          opacity: 0.5,
          textAlign: 'center',
          marginTop: 4,
        }}
      >
        /year in US tech debt
      </div>

      {/* Source */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 10,
          color: CALLOUT_SOURCE_COLOR,
          opacity: 0.3,
          textAlign: 'center',
          marginTop: 8,
        }}
      >
        CISQ, 2022
      </div>
    </div>
  );
};

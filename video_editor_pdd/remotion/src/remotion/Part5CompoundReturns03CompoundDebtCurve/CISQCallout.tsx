import React from 'react';
import { useCurrentFrame, interpolate, Easing, spring } from 'remotion';
import {
  CALLOUT_X,
  CALLOUT_Y,
  CALLOUT_BG,
  TEXT_PRIMARY,
  TEXT_SECONDARY,
  TEXT_MUTED,
  CALLOUT_FADE_DURATION,
  STAT_SCALE_START,
  STAT_SCALE_DURATION,
} from './constants';

export const CISQCallout: React.FC = () => {
  const frame = useCurrentFrame();

  // Card fade-in
  const cardOpacity = interpolate(frame, [0, CALLOUT_FADE_DURATION], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const cardTranslateY = interpolate(frame, [0, CALLOUT_FADE_DURATION], [15, 0], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Stat emphasis scale — starts at frame STAT_SCALE_START (relative to callout sequence start at 210)
  // So relative frame for scale = frame - (STAT_SCALE_START - 210) = frame - 60
  const relativeScaleFrame = frame - 60; // 270 - 210 = 60 frames into this sequence

  const statScale = relativeScaleFrame < 0
    ? 1
    : interpolate(
        relativeScaleFrame,
        [0, STAT_SCALE_DURATION * 0.4, STAT_SCALE_DURATION * 0.7, STAT_SCALE_DURATION],
        [1, 1.15, 0.97, 1.05],
        {
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.poly(4)),
        }
      );

  // Stat number color pulse during emphasis
  const statBrightness = relativeScaleFrame >= 0
    ? interpolate(relativeScaleFrame, [0, STAT_SCALE_DURATION], [1.2, 1], {
        extrapolateRight: 'clamp',
      })
    : 1;

  return (
    <div
      style={{
        position: 'absolute',
        left: CALLOUT_X,
        top: CALLOUT_Y,
        transform: `translate(-50%, -50%) translateY(${cardTranslateY}px)`,
        opacity: cardOpacity,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        backgroundColor: CALLOUT_BG,
        borderRadius: 12,
        padding: '24px 32px',
        // Subtle background
        boxShadow: `0 0 40px rgba(30, 41, 59, 0.3)`,
      }}
    >
      {/* Main stat */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 48,
          fontWeight: 700,
          color: TEXT_PRIMARY,
          lineHeight: 1,
          transform: `scale(${statScale})`,
          filter: `brightness(${statBrightness})`,
          marginBottom: 6,
        }}
      >
        $1.52T
      </div>

      {/* Subtitle */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 16,
          color: TEXT_SECONDARY,
          opacity: 0.5,
          lineHeight: 1.3,
        }}
      >
        /year in US tech debt
      </div>

      {/* Source */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 10,
          color: TEXT_MUTED,
          opacity: 0.3,
          marginTop: 8,
        }}
      >
        CISQ, 2022
      </div>
    </div>
  );
};

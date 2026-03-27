import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  BUG_RED,
  BUG_LOCATION_X,
  BUG_LOCATION_Y,
  PULSE_RING_COUNT,
  PULSE_RING_DELAY,
  PULSE_RING_EXPAND_DURATION,
  PULSE_RING_MAX_RADIUS,
  BUG_PULSE_START,
  BUG_PULSE_END,
  BUG_TEXT_FADE_IN_START,
  BUG_TEXT_FADE_IN_DURATION,
  BUG_TEXT_FADE_OUT_START,
  BUG_TEXT_FADE_OUT_DURATION,
} from './constants';

export const BugPulse: React.FC = () => {
  const frame = useCurrentFrame();

  // Bug text opacity: fade in then fade out
  const bugTextOpacity = (() => {
    if (frame < BUG_TEXT_FADE_IN_START) return 0;
    if (frame < BUG_TEXT_FADE_IN_START + BUG_TEXT_FADE_IN_DURATION) {
      return interpolate(
        frame,
        [BUG_TEXT_FADE_IN_START, BUG_TEXT_FADE_IN_START + BUG_TEXT_FADE_IN_DURATION],
        [0, 1],
        { easing: Easing.out(Easing.quad), extrapolateRight: 'clamp' }
      );
    }
    if (frame < BUG_TEXT_FADE_OUT_START) return 1;
    return interpolate(
      frame,
      [BUG_TEXT_FADE_OUT_START, BUG_TEXT_FADE_OUT_START + BUG_TEXT_FADE_OUT_DURATION],
      [1, 0],
      { easing: Easing.in(Easing.quad), extrapolateRight: 'clamp' }
    );
  })();

  // Only show pulse rings during bug discovery phase
  const showPulse = frame >= BUG_PULSE_START && frame < BUG_PULSE_END;

  const rings: React.ReactNode[] = [];
  if (showPulse) {
    for (let i = 0; i < PULSE_RING_COUNT; i++) {
      const ringStart = BUG_PULSE_START + i * PULSE_RING_DELAY;
      const ringEnd = ringStart + PULSE_RING_EXPAND_DURATION;

      if (frame >= ringStart && frame < ringEnd + 20) {
        const expandProgress = interpolate(
          frame,
          [ringStart, ringEnd],
          [0, 1],
          { easing: Easing.out(Easing.quad), extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );

        const ringOpacity = interpolate(
          frame,
          [ringStart, ringEnd, ringEnd + 20],
          [0.7, 0.4, 0],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );

        const radius = expandProgress * PULSE_RING_MAX_RADIUS;

        rings.push(
          <circle
            key={`ring-${i}`}
            cx={BUG_LOCATION_X}
            cy={BUG_LOCATION_Y}
            r={radius}
            fill="none"
            stroke={BUG_RED}
            strokeWidth={3}
            opacity={ringOpacity}
          />
        );
      }
    }

    // Central glow
    const centralGlowOpacity = interpolate(
      frame,
      [BUG_PULSE_START, BUG_PULSE_START + 10, BUG_PULSE_END - 10, BUG_PULSE_END],
      [0, 0.6, 0.6, 0],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
    );

    rings.push(
      <circle
        key="central-glow"
        cx={BUG_LOCATION_X}
        cy={BUG_LOCATION_Y}
        r={20}
        fill={BUG_RED}
        opacity={centralGlowOpacity}
        filter="url(#bugGlow)"
      />
    );
  }

  return (
    <>
      <svg
        width={1920}
        height={1080}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <defs>
          <filter id="bugGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="10" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>
        {rings}
      </svg>

      {/* BUG text */}
      {bugTextOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            left: BUG_LOCATION_X - 40,
            top: BUG_LOCATION_Y - 55,
            width: 80,
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 28,
            fontWeight: 700,
            color: BUG_RED,
            opacity: bugTextOpacity,
            textShadow: `0 0 12px ${BUG_RED}`,
          }}
        >
          BUG
        </div>
      )}
    </>
  );
};

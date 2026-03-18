import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, FONT, TIMING } from './constants';

export const VisualEquation: React.FC = () => {
  const frame = useCurrentFrame();
  const localFrame = frame - TIMING.equationStart;

  if (localFrame < 0) return null;

  // Left side (red) fades in
  const leftOpacity = interpolate(localFrame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });
  const leftTranslateY = interpolate(localFrame, [0, 20], [12, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // "vs." appears
  const vsLocalFrame = localFrame - 30;
  const vsOpacity = interpolate(vsLocalFrame, [0, 12], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Right side (green) fades in
  const rightLocalFrame = localFrame - 50;
  const rightOpacity = interpolate(rightLocalFrame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });
  const rightTranslateY = interpolate(rightLocalFrame, [0, 20], [12, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Bracket / differentiator label
  const bracketLocalFrame = localFrame - 80;
  const bracketOpacity = interpolate(bracketLocalFrame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const yBase = 850;

  return (
    <div
      style={{
        position: 'absolute',
        top: yBase,
        left: 0,
        width: 1920,
        height: 120,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        gap: 8,
      }}
    >
      {/* Equation row */}
      <div
        style={{
          display: 'flex',
          alignItems: 'center',
          gap: 24,
          justifyContent: 'center',
          width: '100%',
        }}
      >
        {/* LEFT side — red */}
        <div
          style={{
            fontFamily: FONT.family,
            fontSize: 14,
            color: COLORS.red,
            opacity: leftOpacity * 0.6,
            transform: `translateY(${leftTranslateY}px)`,
            textAlign: 'right',
            minWidth: 340,
          }}
        >
          <span style={{ opacity: 0.5 }}>[</span>AI code
          <span style={{ opacity: 0.5 }}>]</span>
          {' + '}
          <span style={{ opacity: 0.5 }}>[</span>No tests
          <span style={{ opacity: 0.5 }}>]</span>
          {' = '}
          <span style={{ fontWeight: 700 }}>1.7× issues</span>
        </div>

        {/* vs. */}
        <div
          style={{
            fontFamily: FONT.family,
            fontSize: 14,
            color: COLORS.muted,
            opacity: vsOpacity * 0.3,
            fontWeight: 600,
          }}
        >
          vs.
        </div>

        {/* RIGHT side — green */}
        <div
          style={{
            fontFamily: FONT.family,
            fontSize: 14,
            color: COLORS.green,
            opacity: rightOpacity * 0.6,
            transform: `translateY(${rightTranslateY}px)`,
            textAlign: 'left',
            minWidth: 380,
          }}
        >
          <span style={{ opacity: 0.5 }}>[</span>AI code
          <span style={{ opacity: 0.5 }}>]</span>
          {' + '}
          <span style={{ opacity: 0.5 }}>[</span>Strong tests
          <span style={{ opacity: 0.5 }}>]</span>
          {' = '}
          <span style={{ fontWeight: 700 }}>Amplified delivery</span>
        </div>
      </div>

      {/* Differentiator bracket pointing to mold walls */}
      <div
        style={{
          display: 'flex',
          flexDirection: 'column',
          alignItems: 'center',
          opacity: bracketOpacity * 0.5,
          marginTop: 6,
        }}
      >
        {/* Upward-pointing bracket */}
        <svg width={120} height={20} viewBox="0 0 120 20">
          <path
            d="M 10 18 L 60 4 L 110 18"
            fill="none"
            stroke={COLORS.amber}
            strokeWidth={1.5}
            strokeLinecap="round"
            strokeLinejoin="round"
          />
        </svg>
        <div
          style={{
            fontFamily: FONT.family,
            fontSize: 12,
            color: COLORS.amber,
            fontWeight: 600,
            letterSpacing: 1,
          }}
        >
          The walls
        </div>
      </div>
    </div>
  );
};

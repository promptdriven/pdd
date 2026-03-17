import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, FONTS, TIMING } from './constants';

export const VisualEquation: React.FC = () => {
  const frame = useCurrentFrame();
  const startFrame = TIMING.equationStart;
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  // Left side fades in (red)
  const leftOpacity = interpolate(localFrame, [0, TIMING.equationLeftDur], [0, 0.6], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });
  const leftTranslate = interpolate(localFrame, [0, TIMING.equationLeftDur], [15, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // "vs." appears
  const vsOpacity = interpolate(
    localFrame,
    [TIMING.equationVsDelay, TIMING.equationVsDelay + 15],
    [0, 0.3],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Right side fades in (green)
  const rightOpacity = interpolate(
    localFrame,
    [TIMING.equationRightDelay, TIMING.equationRightDelay + TIMING.equationLeftDur],
    [0, 0.6],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );
  const rightTranslate = interpolate(
    localFrame,
    [TIMING.equationRightDelay, TIMING.equationRightDelay + TIMING.equationLeftDur],
    [15, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Bracket / differentiator
  const bracketOpacity = interpolate(
    localFrame,
    [TIMING.equationBracketDelay, TIMING.equationBracketDelay + 20],
    [0, 0.5],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );
  const bracketScale = interpolate(
    localFrame,
    [TIMING.equationBracketDelay, TIMING.equationBracketDelay + 20],
    [0.9, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const y = 850;
  const textStyle: React.CSSProperties = {
    fontFamily: FONTS.family,
    fontSize: 14,
    fontWeight: 500,
    whiteSpace: 'nowrap' as const,
  };

  return (
    <div
      style={{
        position: 'absolute',
        top: y,
        left: 0,
        width: 1920,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        gap: 12,
      }}
    >
      {/* Equation row */}
      <div
        style={{
          display: 'flex',
          alignItems: 'center',
          gap: 24,
        }}
      >
        {/* Left: red side */}
        <div
          style={{
            ...textStyle,
            color: COLORS.red,
            opacity: leftOpacity,
            transform: `translateY(${leftTranslate}px)`,
          }}
        >
          [AI code] + [No tests] = 1.7× issues
        </div>

        {/* Divider */}
        <div
          style={{
            ...textStyle,
            color: COLORS.label,
            opacity: vsOpacity,
            fontSize: 14,
          }}
        >
          vs.
        </div>

        {/* Right: green side */}
        <div
          style={{
            ...textStyle,
            color: COLORS.green,
            opacity: rightOpacity,
            transform: `translateY(${rightTranslate}px)`,
          }}
        >
          [AI code] + [Strong tests] = Amplified delivery
        </div>
      </div>

      {/* Differentiator bracket */}
      <div
        style={{
          display: 'flex',
          flexDirection: 'column',
          alignItems: 'center',
          opacity: bracketOpacity,
          transform: `scale(${bracketScale})`,
        }}
      >
        {/* Bracket SVG pointing upward */}
        <svg width={120} height={20} viewBox="0 0 120 20">
          <path
            d="M10,18 L60,4 L110,18"
            fill="none"
            stroke={COLORS.amber}
            strokeWidth={1.5}
            opacity={0.5}
          />
        </svg>
        <div
          style={{
            fontFamily: FONTS.family,
            fontSize: 12,
            fontWeight: 600,
            color: COLORS.amber,
            opacity: 0.5,
            marginTop: 2,
          }}
        >
          The walls
        </div>
      </div>
    </div>
  );
};

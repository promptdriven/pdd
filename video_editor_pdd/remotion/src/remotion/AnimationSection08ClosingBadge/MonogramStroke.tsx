import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  DIMENSIONS,
  POSITIONS,
  ANIMATION_TIMING,
  MONOGRAM_R_PATH,
  MONOGRAM_VIEWBOX,
} from './constants';

const ESTIMATED_PATH_LENGTH = 520;

export const MonogramStroke: React.FC = () => {
  const frame = useCurrentFrame();

  const strokeProgress = interpolate(
    frame,
    [ANIMATION_TIMING.strokeDrawStart, ANIMATION_TIMING.strokeDrawEnd],
    [ESTIMATED_PATH_LENGTH, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const fillOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.fillStart, ANIMATION_TIMING.fillEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // Glow pulse animation
  const glowOpacity = useMemo(() => {
    if (frame < ANIMATION_TIMING.glowPulseStart) return DIMENSIONS.glowOpacity;
    if (frame > ANIMATION_TIMING.glowPulseEnd) return DIMENSIONS.glowOpacity;

    const mid =
      (ANIMATION_TIMING.glowPulseStart + ANIMATION_TIMING.glowPulseEnd) / 2;

    if (frame <= mid) {
      return interpolate(
        frame,
        [ANIMATION_TIMING.glowPulseStart, mid],
        [DIMENSIONS.glowOpacity, 0.6],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.inOut(Easing.sin),
        }
      );
    }
    return interpolate(
      frame,
      [mid, ANIMATION_TIMING.glowPulseEnd],
      [0.6, DIMENSIONS.glowOpacity],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      }
    );
  }, [frame]);

  const svgWidth = (DIMENSIONS.monogramHeight * 120) / 160; // aspect ratio from viewbox
  const svgHeight = DIMENSIONS.monogramHeight;

  return (
    <div
      style={{
        position: 'absolute',
        left: POSITIONS.monogramCenterX - svgWidth / 2,
        top: POSITIONS.monogramCenterY - svgHeight / 2,
        width: svgWidth,
        height: svgHeight,
      }}
    >
      {/* Glow behind monogram */}
      <div
        style={{
          position: 'absolute',
          left: '50%',
          top: '50%',
          width: svgWidth + 60,
          height: svgHeight + 60,
          transform: 'translate(-50%, -50%)',
          borderRadius: '50%',
          backgroundColor: COLORS.glowColor,
          opacity: glowOpacity,
          filter: `blur(${DIMENSIONS.glowBlurRadius}px)`,
        }}
      />

      <svg
        width={svgWidth}
        height={svgHeight}
        viewBox={MONOGRAM_VIEWBOX}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <defs>
          <linearGradient id="monogramGradient" x1="0%" y1="0%" x2="100%" y2="100%">
            <stop offset="0%" stopColor={COLORS.gradientStart} />
            <stop offset="100%" stopColor={COLORS.gradientEnd} />
          </linearGradient>
        </defs>

        {/* Filled path (appears with fillOpacity) */}
        <path
          d={MONOGRAM_R_PATH}
          fill="none"
          stroke="url(#monogramGradient)"
          strokeWidth={DIMENSIONS.strokeWidth + 2}
          strokeLinecap="round"
          strokeLinejoin="round"
          opacity={fillOpacity}
          strokeDasharray="none"
        />

        {/* Stroke-draw path */}
        <path
          d={MONOGRAM_R_PATH}
          fill="none"
          stroke={COLORS.strokeColor}
          strokeWidth={DIMENSIONS.strokeWidth}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={ESTIMATED_PATH_LENGTH}
          strokeDashoffset={strokeProgress}
        />
      </svg>
    </div>
  );
};

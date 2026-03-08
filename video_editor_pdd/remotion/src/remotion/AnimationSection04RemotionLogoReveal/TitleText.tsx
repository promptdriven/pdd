import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, TEXT, TIMING } from './constants';

export const TitleText: React.FC = () => {
  const frame = useCurrentFrame();

  // Title
  const titleOpacity = interpolate(
    frame,
    [TIMING.titleStart, TIMING.titleEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  const titleY = interpolate(
    frame,
    [TIMING.titleStart, TIMING.titleEnd],
    [TEXT.titleY + 20, TEXT.titleY],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(3)) },
  );

  // Subtitle
  const subtitleOpacity = interpolate(
    frame,
    [TIMING.subtitleStart, TIMING.subtitleEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  const subtitleY = interpolate(
    frame,
    [TIMING.subtitleStart, TIMING.subtitleEnd],
    [TEXT.subtitleY + 15, TEXT.subtitleY],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(3)) },
  );

  return (
    <svg
      width={CANVAS.width}
      height={CANVAS.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <text
        x={CANVAS.width / 2}
        y={titleY}
        textAnchor="middle"
        fill={COLORS.white}
        fontSize={TEXT.titleSize}
        fontFamily="Inter, system-ui, sans-serif"
        fontWeight={700}
        letterSpacing="2"
        opacity={titleOpacity}
      >
        {TEXT.title}
      </text>
      <text
        x={CANVAS.width / 2}
        y={subtitleY}
        textAnchor="middle"
        fill={COLORS.subtitleGray}
        fontSize={TEXT.subtitleSize}
        fontFamily="Inter, system-ui, sans-serif"
        fontWeight={400}
        letterSpacing="4"
        opacity={subtitleOpacity}
      >
        {TEXT.subtitle}
      </text>
    </svg>
  );
};

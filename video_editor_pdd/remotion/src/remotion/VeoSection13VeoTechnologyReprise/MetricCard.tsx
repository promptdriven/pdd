import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { LAYOUT, TYPOGRAPHY, COLORS, ANIMATION } from './constants';
import { MetricIcon } from './MetricIcon';

interface MetricCardProps {
  icon: 'film' | 'clock' | 'sparkle';
  value: string;
  label: string;
  accentColor: string;
  animStart: number;
  animEnd: number;
}

export const MetricCard: React.FC<MetricCardProps> = ({
  icon,
  value,
  label,
  accentColor,
  animStart,
  animEnd,
}) => {
  const frame = useCurrentFrame();

  // Slide up animation
  const slideY = interpolate(
    frame,
    [animStart, animEnd],
    [ANIMATION.cardSlideDistance, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  const cardOpacity = interpolate(
    frame,
    [animStart, animEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // Fade out
  const fadeOut = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.poly(2)),
    },
  );

  // Number animation
  const numberProgress = interpolate(
    frame,
    [animStart, animEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(2)),
    },
  );

  // Compute the displayed value
  let displayValue = value;
  if (value === '2') {
    const num = Math.round(numberProgress * 2);
    displayValue = String(num);
  } else if (value === '100%') {
    const num = Math.round(numberProgress * 100);
    displayValue = `${num}%`;
  } else {
    // "~6s" — type in progressively
    if (numberProgress < 0.33) {
      displayValue = '~';
    } else if (numberProgress < 0.66) {
      displayValue = '~6';
    } else {
      displayValue = '~6s';
    }
  }

  // Sparkle rotation during hold phase
  const sparkleRotation =
    icon === 'sparkle' && frame >= ANIMATION.holdStart
      ? ((frame - ANIMATION.holdStart) * 4) % 360
      : 0;

  // Film icon pulse during hold
  const filmPulseScale =
    icon === 'film' && frame >= ANIMATION.holdStart
      ? 1 + 0.05 * Math.sin((frame - ANIMATION.holdStart) * 0.15)
      : 1;

  return (
    <div
      style={{
        width: LAYOUT.cardWidth,
        height: LAYOUT.cardHeight,
        backgroundColor: COLORS.cardBg,
        borderRadius: LAYOUT.cardBorderRadius,
        borderLeft: `${LAYOUT.cardBorderLeft}px solid ${accentColor}`,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        justifyContent: 'center',
        gap: 12,
        opacity: cardOpacity * fadeOut,
        transform: `translateY(${slideY}px)`,
      }}
    >
      {/* Icon */}
      <div style={{ transform: `scale(${filmPulseScale})` }}>
        <MetricIcon
          icon={icon}
          color={accentColor}
          size={LAYOUT.iconSize}
          rotation={sparkleRotation}
        />
      </div>

      {/* Number */}
      <div
        style={{
          fontFamily: TYPOGRAPHY.metricNumber.fontFamily,
          fontSize: TYPOGRAPHY.metricNumber.fontSize,
          fontWeight: TYPOGRAPHY.metricNumber.fontWeight,
          color: COLORS.metricNumber,
          lineHeight: 1,
        }}
      >
        {displayValue}
      </div>

      {/* Label */}
      <div
        style={{
          fontFamily: TYPOGRAPHY.metricLabel.fontFamily,
          fontSize: TYPOGRAPHY.metricLabel.fontSize,
          fontWeight: TYPOGRAPHY.metricLabel.fontWeight,
          color: COLORS.metricLabel,
          lineHeight: 1,
        }}
      >
        {label}
      </div>
    </div>
  );
};

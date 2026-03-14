import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, BADGE_LAYOUT, type WaveOverlayLayout } from './constants';

/** Simple SVG icon glyphs rendered inline */
const WaveIcon: React.FC<{ size: number }> = ({ size }) => (
  <svg width={size} height={size} viewBox="0 0 24 24" fill="none">
    <path
      d="M2 12c2-4 4-4 6 0s4 4 6 0 4-4 6 0"
      stroke={COLORS.waveStroke}
      strokeWidth={2}
      strokeLinecap="round"
    />
  </svg>
);

const ClockIcon: React.FC<{ size: number }> = ({ size }) => (
  <svg width={size} height={size} viewBox="0 0 24 24" fill="none">
    <circle cx={12} cy={12} r={9} stroke={COLORS.waveStroke} strokeWidth={2} />
    <path d="M12 7v5l3 3" stroke={COLORS.waveStroke} strokeWidth={2} strokeLinecap="round" />
  </svg>
);

const ThermometerIcon: React.FC<{ size: number }> = ({ size }) => (
  <svg width={size} height={size} viewBox="0 0 24 24" fill="none">
    <path
      d="M14 14.76V3.5a2.5 2.5 0 0 0-5 0v11.26a4.5 4.5 0 1 0 5 0Z"
      stroke={COLORS.waveStroke}
      strokeWidth={2}
      strokeLinecap="round"
    />
    <circle cx={11.5} cy={17.5} r={1.5} fill={COLORS.waveStroke} />
  </svg>
);

const ICON_MAP = {
  wave: WaveIcon,
  clock: ClockIcon,
  thermometer: ThermometerIcon,
} as const;

interface StatBadgeProps {
  layout: WaveOverlayLayout;
  label: string;
  value: string;
  icon: keyof typeof ICON_MAP;
  /** Y position in base canvas coordinates */
  y: number;
  /** Animation start frame */
  animStart: number;
  /** Animation end frame */
  animEnd: number;
}

export const StatBadge: React.FC<StatBadgeProps> = ({
  layout,
  label,
  value,
  icon,
  y,
  animStart,
  animEnd,
}) => {
  const frame = useCurrentFrame();

  // Slide in from right: translateX +40 → 0, opacity 0 → 1
  const slideX = interpolate(
    frame,
    [animStart, animEnd],
    [BADGE_LAYOUT.slideOffset * layout.scaleX, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const opacity = interpolate(
    frame,
    [animStart, animEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const IconComponent = ICON_MAP[icon];
  const iconSize = Math.max(16, 20 * layout.uniformScale);

  return (
    <div
      style={{
        position: 'absolute',
        left: layout.badge.x,
        top: y * layout.scaleY,
        width: layout.badge.width,
        height: layout.badge.height,
        borderRadius: BADGE_LAYOUT.borderRadius * layout.uniformScale,
        backgroundColor: COLORS.badgeBg,
        border: `${BADGE_LAYOUT.borderWidth}px solid ${COLORS.badgeBorder}`,
        display: 'flex',
        alignItems: 'center',
        gap: 12 * layout.uniformScale,
        paddingLeft: 16 * layout.scaleX,
        paddingRight: 16 * layout.scaleX,
        opacity,
        transform: `translateX(${slideX}px)`,
        boxSizing: 'border-box',
      }}
    >
      <IconComponent size={iconSize} />
      <div style={{ display: 'flex', flexDirection: 'column', gap: 2 }}>
        <span
          style={{
            fontFamily: layout.typography.badgeLabel.fontFamily,
            fontSize: layout.typography.badgeLabel.fontSize,
            fontWeight: layout.typography.badgeLabel.fontWeight,
            color: COLORS.badgeLabel,
            lineHeight: 1.2,
          }}
        >
          {label}
        </span>
        <span
          style={{
            fontFamily: layout.typography.badgeValue.fontFamily,
            fontSize: layout.typography.badgeValue.fontSize,
            fontWeight: layout.typography.badgeValue.fontWeight,
            color: COLORS.badgeValue,
            lineHeight: 1.2,
          }}
        >
          {value}
        </span>
      </div>
    </div>
  );
};

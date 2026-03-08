import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { ICON_CONFIG, LABEL_CONFIG, TIMING } from './constants';

interface IconCellProps {
  icon: string;
  color: string;
  label: string;
  delay: number;
}

/**
 * Individual icon cell with entry animation and label
 */
export const IconCell: React.FC<IconCellProps> = ({ icon, color, label, delay }) => {
  const frame = useCurrentFrame();
  const adjustedFrame = frame - delay;

  // Entry animation (0-20 frames after delay)
  const scale = interpolate(
    adjustedFrame,
    [0, TIMING.entryDuration * 0.7, TIMING.entryDuration],
    [0, 1.1, 1.0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.5)),
    }
  );

  const rotation = interpolate(
    adjustedFrame,
    [0, TIMING.entryDuration],
    [-15, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const opacity = interpolate(
    adjustedFrame,
    [0, TIMING.entryDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Label animation
  const labelOpacity = interpolate(
    frame,
    [TIMING.labelFadeStart, TIMING.labelFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const labelDrift = interpolate(
    frame,
    [TIMING.labelFadeStart, TIMING.labelFadeEnd],
    [10, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // Pulse effect (starts at frame 60)
  const pulseFrame = frame - 60;
  const pulseGlow = interpolate(
    pulseFrame,
    [0, TIMING.pulseDuration / 2, TIMING.pulseDuration],
    [0, 0.6, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  const pulseScale = interpolate(
    pulseFrame,
    [0, TIMING.pulseDuration / 2, TIMING.pulseDuration],
    [1.0, 1.05, 1.0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  return (
    <div
      style={{
        position: 'relative',
        width: ICON_CONFIG.containerSize,
        height: ICON_CONFIG.containerSize,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
      }}
    >
      {/* Icon container */}
      <div
        style={{
          width: ICON_CONFIG.containerSize,
          height: ICON_CONFIG.containerSize,
          borderRadius: '50%',
          backgroundColor: ICON_CONFIG.iconBackground,
          border: `${ICON_CONFIG.borderWidth}px solid ${color}`,
          boxShadow: ICON_CONFIG.shadow,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
          transform: `scale(${scale * pulseScale}) rotate(${rotation}deg)`,
          opacity,
          position: 'relative',
        }}
      >
        {/* Pulse glow effect */}
        <div
          style={{
            position: 'absolute',
            inset: -4,
            borderRadius: '50%',
            border: `3px solid ${color}`,
            opacity: pulseGlow,
            pointerEvents: 'none',
          }}
        />

        {/* Icon SVG */}
        <IconSVG icon={icon} color={color} size={ICON_CONFIG.iconSize} />
      </div>

      {/* Label text */}
      <div
        style={{
          position: 'absolute',
          top: LABEL_CONFIG.offsetY,
          left: '50%',
          transform: `translate(-50%, ${labelDrift}px)`,
          fontFamily: LABEL_CONFIG.fontFamily,
          fontWeight: LABEL_CONFIG.fontWeight,
          fontSize: LABEL_CONFIG.fontSize,
          color: LABEL_CONFIG.offsetY,
          opacity: labelOpacity,
          whiteSpace: 'nowrap',
        }}
      >
        {label}
      </div>
    </div>
  );
};

/**
 * Simple icon SVG renderer
 */
const IconSVG: React.FC<{ icon: string; color: string; size: number }> = ({ icon, color, size }) => {
  const commonProps = {
    width: size,
    height: size,
    viewBox: '0 0 24 24',
    fill: 'none',
    stroke: color,
    strokeWidth: 2,
    strokeLinecap: 'round' as const,
    strokeLinejoin: 'round' as const,
  };

  switch (icon) {
    case 'ChartBar':
      return (
        <svg {...commonProps}>
          <rect x="3" y="3" width="18" height="18" rx="2" />
          <path d="M8 10v7M12 7v10M16 11v6" />
        </svg>
      );
    case 'Lightning':
      return (
        <svg {...commonProps}>
          <path d="M13 2L3 14h8l-1 8 10-12h-8l1-8z" fill={color} stroke="none" />
        </svg>
      );
    case 'Shield':
      return (
        <svg {...commonProps}>
          <path d="M12 22s8-4 8-10V5l-8-3-8 3v7c0 6 8 10 8 10z" />
          <path d="M9 12l2 2 4-4" />
        </svg>
      );
    case 'Code':
      return (
        <svg {...commonProps}>
          <path d="M16 18l6-6-6-6M8 6l-6 6 6 6" />
        </svg>
      );
    case 'Sparkles':
      return (
        <svg {...commonProps}>
          <path d="M12 3v18M3 12h18M6 6l12 12M6 18L18 6" />
        </svg>
      );
    case 'Rocket':
      return (
        <svg {...commonProps}>
          <path d="M4.5 16.5c-1.5 1.26-2 5-2 5s3.74-.5 5-2c.71-.84.7-2.13-.09-2.91a2.18 2.18 0 0 0-2.91-.09z" />
          <path d="m12 15-3-3a22 22 0 0 1 2-3.95A12.88 12.88 0 0 1 22 2c0 2.72-.78 7.5-6 11a22.35 22.35 0 0 1-4 2z" />
          <path d="M9 12H4s.55-3.03 2-4c1.62-1.08 5 0 5 0M12 15v5s3.03-.55 4-2c1.08-1.62 0-5 0-5" />
        </svg>
      );
    case 'Layers':
      return (
        <svg {...commonProps}>
          <polygon points="12 2 2 7 12 12 22 7 12 2" />
          <polyline points="2 17 12 22 22 17" />
          <polyline points="2 12 12 17 22 12" />
        </svg>
      );
    case 'Zap':
      return (
        <svg {...commonProps}>
          <polygon points="13 2 3 14 12 14 11 22 21 10 12 10 13 2" fill={color} stroke="none" />
        </svg>
      );
    case 'Heart':
      return (
        <svg {...commonProps}>
          <path d="M20.84 4.61a5.5 5.5 0 0 0-7.78 0L12 5.67l-1.06-1.06a5.5 5.5 0 0 0-7.78 7.78l1.06 1.06L12 21.23l7.78-7.78 1.06-1.06a5.5 5.5 0 0 0 0-7.78z" fill={color} stroke="none" />
        </svg>
      );
    default:
      return (
        <svg {...commonProps}>
          <circle cx="12" cy="12" r="10" />
        </svg>
      );
  }
};

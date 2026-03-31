import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface CyclePhaseIconProps {
  label: string;
  color: string;
  glowColor: string;
  angleDeg: number;
  centerX: number;
  centerY: number;
  radius: number;
  iconSize: number;
  frameStart: number;
  frameEnd: number;
  isActive: boolean;
  loopProgress: number;
}

const CyclePhaseIcon: React.FC<CyclePhaseIconProps> = ({
  label,
  color,
  glowColor,
  angleDeg,
  centerX,
  centerY,
  radius,
  iconSize,
  frameStart,
  frameEnd,
  isActive,
  loopProgress,
}) => {
  const frame = useCurrentFrame();

  const angleRad = (angleDeg * Math.PI) / 180;
  const x = centerX + radius * Math.cos(angleRad) - iconSize / 2;
  const y = centerY + radius * Math.sin(angleRad) - iconSize / 2;

  // Entrance animation
  const entranceProgress = interpolate(frame, [frameStart, frameStart + 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.poly(3)),
  });

  const scale = interpolate(entranceProgress, [0, 1], [0.3, 1]);
  const opacity = interpolate(entranceProgress, [0, 1], [0, 1]);

  // Active pulse
  const activeScale = isActive
    ? interpolate(
        frame,
        [frameStart, frameStart + 10, frameEnd - 10, frameEnd],
        [1, 1.15, 1.15, 1],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
      )
    : 1;

  // Glow intensity
  const glowOpacity = isActive ? 0.8 : 0.25 + loopProgress * 0.4;

  // Label position below icon
  const labelY = y + iconSize + 14;
  const labelX = centerX + radius * Math.cos(angleRad);

  // Icon shape based on label
  const renderIcon = () => {
    if (label === 'TEST') {
      // Magnifying glass / checkmark
      return (
        <svg width={iconSize} height={iconSize} viewBox="0 0 80 80">
          <circle
            cx="35"
            cy="35"
            r="20"
            fill="none"
            stroke={color}
            strokeWidth="4"
          />
          <line
            x1="50"
            y1="50"
            x2="68"
            y2="68"
            stroke={color}
            strokeWidth="4"
            strokeLinecap="round"
          />
          <polyline
            points="25,36 33,44 47,28"
            fill="none"
            stroke={color}
            strokeWidth="3.5"
            strokeLinecap="round"
            strokeLinejoin="round"
          />
        </svg>
      );
    }
    if (label === 'FIX') {
      // Wrench
      return (
        <svg width={iconSize} height={iconSize} viewBox="0 0 80 80">
          <path
            d="M55 15 a18 18 0 0 0-25 25 l-15 15 a5 5 0 0 0 7 7 l15-15 a18 18 0 0 0 25-25 l-8 8-6-6z"
            fill="none"
            stroke={color}
            strokeWidth="3.5"
            strokeLinejoin="round"
          />
        </svg>
      );
    }
    // REGENERATE — circular arrows
    return (
      <svg width={iconSize} height={iconSize} viewBox="0 0 80 80">
        <path
          d="M40 16 A24 24 0 0 1 62 44"
          fill="none"
          stroke={color}
          strokeWidth="4"
          strokeLinecap="round"
        />
        <polygon points="66,42 58,50 62,36" fill={color} />
        <path
          d="M40 64 A24 24 0 0 1 18 36"
          fill="none"
          stroke={color}
          strokeWidth="4"
          strokeLinecap="round"
        />
        <polygon points="14,38 22,30 18,44" fill={color} />
      </svg>
    );
  };

  return (
    <>
      {/* Glow behind icon */}
      <div
        style={{
          position: 'absolute',
          left: x - 20,
          top: y - 20,
          width: iconSize + 40,
          height: iconSize + 40,
          borderRadius: '50%',
          background: glowColor,
          filter: `blur(${isActive ? 24 : 14}px)`,
          opacity: glowOpacity * opacity,
          transform: `scale(${scale * activeScale})`,
        }}
      />
      {/* Icon container */}
      <div
        style={{
          position: 'absolute',
          left: x,
          top: y,
          width: iconSize,
          height: iconSize,
          borderRadius: '50%',
          border: `3px solid ${color}`,
          background: isActive ? `${color}22` : 'rgba(10, 22, 40, 0.9)',
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
          opacity,
          transform: `scale(${scale * activeScale})`,
          boxShadow: isActive ? `0 0 20px ${glowColor}` : 'none',
        }}
      >
        {renderIcon()}
      </div>
      {/* Label */}
      <div
        style={{
          position: 'absolute',
          left: labelX - 80,
          top: labelY,
          width: 160,
          textAlign: 'center',
          fontFamily: 'Inter, system-ui, sans-serif',
          fontWeight: 700,
          fontSize: 22,
          letterSpacing: '0.12em',
          color: isActive ? color : 'rgba(255,255,255,0.82)',
          opacity: opacity * 0.9,
          transform: `scale(${scale})`,
          textShadow: isActive ? `0 0 12px ${glowColor}` : 'none',
        }}
      >
        {label}
      </div>
    </>
  );
};

export default CyclePhaseIcon;

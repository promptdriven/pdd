import React from 'react';
import { useCurrentFrame, interpolate, spring, Easing } from 'remotion';
import { FONT_MONO, FONT_SANS, RED, GREEN, AMBER, ROW_HEIGHT, FPS } from './constants';

interface PddRowProps {
  text: string;
  icon: 'alert' | 'wall' | 'check';
  color: string;
  isMono?: boolean;
  appearFrame: number;
  y: number;
}

export const PddRow: React.FC<PddRowProps> = ({
  text,
  icon,
  color,
  isMono,
  appearFrame,
  y,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(frame, [appearFrame, appearFrame + 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  if (progress <= 0) return null;

  const translateX = interpolate(progress, [0, 1], [-20, 0]);
  const opacity = progress;

  // For the check icon, use spring for a bouncy scale effect
  const checkScale =
    icon === 'check'
      ? spring({
          frame: frame - appearFrame,
          fps: FPS,
          config: { stiffness: 180, damping: 10 },
        })
      : 1;

  const iconChar =
    icon === 'alert' ? '⚠' : icon === 'wall' ? '🧱' : '✓';
  const iconColor =
    icon === 'alert' ? RED : icon === 'wall' ? AMBER : GREEN;

  // Green glow for check row
  const isCheckRow = icon === 'check';
  const glowOpacity = isCheckRow
    ? interpolate(frame, [appearFrame + 15, appearFrame + 30], [0, 0.3], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      })
    : 0;

  return (
    <div
      style={{
        position: 'absolute',
        top: y,
        left: 20,
        right: 20,
        height: ROW_HEIGHT,
        display: 'flex',
        alignItems: 'center',
        gap: 12,
        opacity,
        transform: `translateX(${translateX}px)`,
        borderRadius: 6,
        backgroundColor: isCheckRow ? `rgba(90, 170, 110, ${glowOpacity})` : 'transparent',
      }}
    >
      {/* Status icon */}
      <div
        style={{
          width: 28,
          height: 28,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
          fontSize: icon === 'wall' ? 16 : 18,
          color: iconColor,
          flexShrink: 0,
          transform: icon === 'check' ? `scale(${checkScale})` : undefined,
        }}
      >
        {iconChar}
      </div>

      {/* Text */}
      <div
        style={{
          fontFamily: isMono ? FONT_MONO : FONT_SANS,
          fontSize: 12,
          color: color,
          whiteSpace: 'nowrap',
          overflow: 'hidden',
          textOverflow: 'ellipsis',
        }}
      >
        {text}
      </div>
    </div>
  );
};

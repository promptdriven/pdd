import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';

/**
 * ProgressBar renders a horizontal track with an animated gradient fill
 * that progresses over the total duration using easeInOut cubic easing.
 */

interface ProgressBarProps {
  barWidth: number;
  barHeight: number;
  x: number;
  y: number;
  trackColor: string;
  fillStartColor: string;
  fillEndColor: string;
  totalFrames: number;
}

export const ProgressBar: React.FC<ProgressBarProps> = ({
  barWidth,
  barHeight,
  x,
  y,
  trackColor,
  fillStartColor,
  fillEndColor,
  totalFrames,
}) => {
  const frame = useCurrentFrame();

  const fillProgress = interpolate(frame, [0, totalFrames], [0, 1], {
    easing: Easing.inOut(Easing.cubic),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const fillWidth = fillProgress * barWidth;

  // Glow when nearly full
  const glowOpacity = interpolate(fillProgress, [0.7, 1], [0, 0.6], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width: barWidth,
        height: barHeight,
      }}
    >
      {/* Track */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: barWidth,
          height: barHeight,
          background: trackColor,
          borderRadius: barHeight / 2,
        }}
      />

      {/* Fill */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: Math.max(fillWidth, barHeight),
          height: barHeight,
          background: `linear-gradient(90deg, ${fillStartColor}, ${fillEndColor})`,
          borderRadius: barHeight / 2,
          boxShadow: glowOpacity > 0
            ? `0 0 12px rgba(90,170,110,${glowOpacity})`
            : 'none',
        }}
      />

      {/* Leading dot indicator */}
      {fillProgress > 0.02 && (
        <div
          style={{
            position: 'absolute',
            left: fillWidth - 4,
            top: -2,
            width: 8,
            height: 8,
            borderRadius: '50%',
            background: fillEndColor,
            boxShadow: `0 0 6px ${fillEndColor}`,
            opacity: interpolate(fillProgress, [0, 0.05, 1], [0, 1, 1], {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
            }),
          }}
        />
      )}
    </div>
  );
};

export default ProgressBar;

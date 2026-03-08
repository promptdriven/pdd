import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION } from './constants';

interface PipelineBarProps {
  label: string;
  progress: number;
  color: string;
  index: number;
}

export const PipelineBar: React.FC<PipelineBarProps> = ({
  label,
  progress,
  color,
  index,
}) => {
  const frame = useCurrentFrame();

  const startFrame = ANIMATION.pipelineStart + index * ANIMATION.pipelineStagger;
  const endFrame = startFrame + ANIMATION.pipelineGrowDuration;

  // Row fade in
  const opacity = interpolate(
    frame,
    [startFrame, startFrame + 8],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(2)),
    },
  );

  // Bar width growth
  const barWidth = interpolate(
    frame,
    [startFrame, endFrame],
    [0, progress],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // Percentage counter
  const displayPercent = Math.round(barWidth);

  return (
    <div
      style={{
        opacity,
        display: 'flex',
        alignItems: 'center',
        gap: 16,
        width: '100%',
        marginBottom: 10,
      }}
    >
      {/* Label */}
      <span
        style={{
          color: COLORS.labelText,
          fontSize: TYPOGRAPHY.pipelineLabel.fontSize,
          fontFamily: TYPOGRAPHY.pipelineLabel.fontFamily,
          fontWeight: TYPOGRAPHY.pipelineLabel.fontWeight,
          letterSpacing: TYPOGRAPHY.pipelineLabel.letterSpacing,
          width: 180,
          flexShrink: 0,
          whiteSpace: 'nowrap',
        }}
      >
        {label}
      </span>

      {/* Bar track */}
      <div
        style={{
          flex: 1,
          height: 8,
          borderRadius: 4,
          backgroundColor: COLORS.barTrack,
          overflow: 'hidden',
          position: 'relative',
        }}
      >
        {/* Bar fill */}
        <div
          style={{
            width: `${barWidth}%`,
            height: '100%',
            borderRadius: 4,
            backgroundColor: color,
            boxShadow: `0 0 10px ${color}44`,
            position: 'relative',
          }}
        >
          {/* Shimmer highlight */}
          <div
            style={{
              position: 'absolute',
              right: 0,
              top: 0,
              width: 30,
              height: '100%',
              background: `linear-gradient(90deg, transparent, ${color}66, transparent)`,
              opacity: barWidth >= progress ? 0 : 0.8,
            }}
          />
        </div>
      </div>

      {/* Percentage */}
      <span
        style={{
          color: COLORS.valueText,
          fontSize: 14,
          fontFamily: 'Inter, sans-serif',
          fontWeight: 600,
          width: 48,
          textAlign: 'right',
          flexShrink: 0,
        }}
      >
        {displayPercent}%
      </span>
    </div>
  );
};

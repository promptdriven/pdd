import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  TRACK,
  COLORS,
  DIMENSIONS,
  TYPOGRAPHY,
  ANIMATION_TIMING,
} from './constants';

interface MilestoneDotProps {
  x: number;
  y: number;
  color: string;
  label: string;
  index: number;
  playheadX: number;
}

export const MilestoneDot: React.FC<MilestoneDotProps> = ({
  x,
  y,
  color,
  label,
  index,
  playheadX,
}) => {
  const frame = useCurrentFrame();

  // Pop-in timing: staggered by 4 frames starting at frame 20
  const popInStart =
    ANIMATION_TIMING.milestonePopStart +
    index * ANIMATION_TIMING.milestoneStagger;
  const popInEnd = popInStart + 10;

  // Scale with easeOutBack for pop effect
  const scale = interpolate(frame, [popInStart, popInEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.back(2.5)),
  });

  // Opacity fade in with the dot
  const opacity = interpolate(frame, [popInStart, popInStart + 6], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Highlight pulse when playhead passes over this milestone
  const isPlayheadActive = frame >= ANIMATION_TIMING.playheadStart;
  const distanceFromPlayhead = Math.abs(playheadX - x);
  const isNearPlayhead = isPlayheadActive && distanceFromPlayhead < 30;

  // Calculate highlight based on proximity to playhead
  const highlightScale = isNearPlayhead
    ? interpolate(distanceFromPlayhead, [0, 30], [1.5, 1.0], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.quad),
      })
    : 1.0;

  // Once playhead has passed, check if we should show post-pass highlight
  const hasPlayheadPassed = isPlayheadActive && playheadX > x;

  const glowOpacity = isNearPlayhead
    ? interpolate(distanceFromPlayhead, [0, 30], [0.8, 0.4], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      })
    : hasPlayheadPassed
      ? 0.6
      : 0.4;

  const finalScale = scale * highlightScale;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        transform: 'translate(-50%, -50%)',
        opacity,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
      }}
    >
      {/* Vertical tick */}
      <div
        style={{
          width: DIMENSIONS.tickWidth,
          height: DIMENSIONS.tickHeight,
          backgroundColor: COLORS.tickStroke,
          marginBottom: 4,
          transform: `scaleY(${scale})`,
          transformOrigin: 'bottom center',
        }}
      />

      {/* Dot */}
      <div
        style={{
          width: DIMENSIONS.dotDiameter,
          height: DIMENSIONS.dotDiameter,
          borderRadius: '50%',
          backgroundColor: color,
          transform: `scale(${finalScale})`,
          boxShadow: `0 0 ${DIMENSIONS.playheadGlowSize}px ${color}`,
          opacity: glowOpacity + 0.2,
        }}
      />

      {/* Label below */}
      <div
        style={{
          marginTop: 12,
          fontSize: TYPOGRAPHY.label.fontSize,
          fontFamily: TYPOGRAPHY.label.fontFamily,
          fontWeight: TYPOGRAPHY.label.fontWeight,
          color: COLORS.labelText,
          whiteSpace: 'nowrap',
          transform: `scale(${scale})`,
        }}
      >
        {label}
      </div>
    </div>
  );
};

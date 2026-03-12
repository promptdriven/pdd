import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, type NarrationOverlayLayout } from './constants';
import { TypeOnText } from './TypeOnText';
import { GradientBar } from './GradientBar';

export const FrostedPill: React.FC<{ text: string; layout: NarrationOverlayLayout }> = ({
  text,
  layout,
}) => {
  const frame = useCurrentFrame();

  // Frame 0-20: Pill slides in from left with easeOutCubic
  const slideX = interpolate(
    frame,
    [ANIMATION.pillSlideStart, ANIMATION.pillSlideEnd],
    [ANIMATION.pillSlideOffset, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const pillOpacity = interpolate(
    frame,
    [ANIMATION.pillSlideStart, ANIMATION.pillSlideEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: layout.pill.x,
        top: layout.pill.y,
        width: layout.pill.width,
        height: layout.pill.height,
        borderRadius: layout.pill.borderRadius,
        backgroundColor: COLORS.pillFill,
        backdropFilter: `blur(${layout.pill.backdropBlur}px)`,
        WebkitBackdropFilter: `blur(${layout.pill.backdropBlur}px)`,
        border: `1px solid ${COLORS.pillBorder}`,
        transform: `translateX(${slideX}px)`,
        opacity: pillOpacity,
        overflow: 'hidden',
      }}
    >
      <TypeOnText text={text} layout={layout} />
      <GradientBar layout={layout} />
    </div>
  );
};

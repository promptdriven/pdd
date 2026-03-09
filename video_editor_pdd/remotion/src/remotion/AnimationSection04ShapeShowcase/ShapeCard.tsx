import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

interface ShapeCardProps {
  shape: 'circle' | 'square';
  color: string;
  centerX: number;
  centerY: number;
  direction: 'left' | 'right';
}

export const ShapeCard: React.FC<ShapeCardProps> = ({
  shape,
  color,
  centerX,
  centerY,
  direction,
}) => {
  const frame = useCurrentFrame();

  const slideStart =
    direction === 'left'
      ? ANIMATION_TIMING.leftCardStart
      : ANIMATION_TIMING.rightCardStart;
  const slideEnd =
    direction === 'left'
      ? ANIMATION_TIMING.leftCardEnd
      : ANIMATION_TIMING.rightCardEnd;

  const slideOffset = direction === 'left' ? -200 : 200;

  const translateX = interpolate(
    frame,
    [slideStart, slideEnd],
    [slideOffset, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const cardOpacity = interpolate(
    frame,
    [slideStart, slideStart + 15],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Shape scales in slightly after card starts
  const shapeScaleStart = slideStart + 10;
  const shapeScaleEnd = slideEnd;

  const shapeScale = interpolate(
    frame,
    [shapeScaleStart, shapeScaleEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    }
  );

  const cardLeft = centerX - DIMENSIONS.cardSize / 2;
  const cardTop = centerY - DIMENSIONS.cardSize / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: cardLeft,
        top: cardTop,
        width: DIMENSIONS.cardSize,
        height: DIMENSIONS.cardSize,
        borderRadius: DIMENSIONS.cardBorderRadius,
        backgroundColor: COLORS.cardBackground,
        border: `1px solid ${COLORS.cardBorder}`,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        opacity: cardOpacity,
        transform: `translateX(${translateX}px)`,
      }}
    >
      <div
        style={{
          width: DIMENSIONS.shapeSize,
          height: DIMENSIONS.shapeSize,
          backgroundColor: color,
          borderRadius: shape === 'circle' ? '50%' : 0,
          transform: `scale(${shapeScale})`,
        }}
      />
    </div>
  );
};

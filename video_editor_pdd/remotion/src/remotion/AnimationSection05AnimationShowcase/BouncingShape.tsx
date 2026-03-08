import React from 'react';
import { useCurrentFrame, spring, interpolate, Easing } from 'remotion';
import { ShapeRenderer } from './ShapeRenderer';
import { ANIMATION } from './constants';
import type { ShapeType } from './constants';

interface BouncingShapeProps {
  type: ShapeType;
  color: string;
  size: number;
  index: number;
}

export const BouncingShape: React.FC<BouncingShapeProps> = ({
  type,
  color,
  size,
  index,
}) => {
  const frame = useCurrentFrame();
  const staggerOffset = index * ANIMATION.staggerDelay;

  // Drop animation with spring
  const dropProgress = spring({
    frame: frame - staggerOffset,
    fps: 30,
    config: {
      damping: 10,
      stiffness: 150,
      mass: 0.8,
    },
  });

  const translateY = interpolate(dropProgress, [0, 1], [-ANIMATION.dropDistance, 0]);

  // Squash & stretch on landing
  const squashProgress = spring({
    frame: Math.max(0, frame - staggerOffset - 8),
    fps: 30,
    config: {
      damping: 8,
      stiffness: 200,
      mass: 0.8,
    },
  });

  // Before landing: elongate vertically. At landing: squash. Then normalize.
  const landingFrame = frame - staggerOffset;
  let scaleX = 1;
  let scaleY = 1;

  if (landingFrame >= 0 && landingFrame < 20) {
    // Squash effect: compress Y, expand X at the moment of "landing"
    const squashAmount = interpolate(
      squashProgress,
      [0, 0.5, 1],
      [0, 1, 0],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
    );
    scaleX = 1 + squashAmount * 0.3;
    scaleY = 1 - squashAmount * 0.3;
  }

  // Synchronized pulse (Frame 55-65)
  let pulseScale = 1;
  let hueRotation = 0;
  if (frame >= ANIMATION.pulseStart && frame <= ANIMATION.pulseEnd) {
    const pulseProgress = interpolate(
      frame,
      [ANIMATION.pulseStart, (ANIMATION.pulseStart + ANIMATION.pulseEnd) / 2, ANIMATION.pulseEnd],
      [0, 1, 0],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
    );
    pulseScale = 1 + pulseProgress * (ANIMATION.pulseScale - 1);
    hueRotation = pulseProgress * ANIMATION.hueShift;
  }

  // Idle breathing (Frame 65-75)
  let breatheScale = 1;
  if (frame >= ANIMATION.breatheStart) {
    const breatheProgress = interpolate(
      frame,
      [ANIMATION.breatheStart, ANIMATION.breatheEnd],
      [0, Math.PI],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
    );
    breatheScale = 1 + (ANIMATION.breatheScale - 1) * Math.sin(breatheProgress);
  }

  const totalScaleX = scaleX * pulseScale * breatheScale;
  const totalScaleY = scaleY * pulseScale * breatheScale;

  // Opacity: visible from the moment the shape starts dropping
  const opacity = frame >= staggerOffset ? 1 : 0;

  return (
    <div
      style={{
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        width: '100%',
        height: '100%',
        opacity,
        transform: `translateY(${translateY}px) scaleX(${totalScaleX}) scaleY(${totalScaleY})`,
        filter: hueRotation > 0 ? `hue-rotate(${hueRotation}deg)` : undefined,
        willChange: 'transform, opacity, filter',
      }}
    >
      <ShapeRenderer type={type} color={color} size={size} />
    </div>
  );
};

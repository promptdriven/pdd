import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  DIMENSIONS,
  ANIMATION,
  CHECKMARK_PATH,
  CHECKMARK_PATH_LENGTH,
  CIRCLE_CIRCUMFERENCE,
} from './constants';

/**
 * easeOutBack: overshoot bounce on scale-in.
 * t => 1 + c3 * (t-1)^3 + c1 * (t-1)^2
 */
const easeOutBack = (t: number): number => {
  const c1 = 1.70158;
  const c3 = c1 + 1;
  return 1 + c3 * Math.pow(t - 1, 3) + c1 * Math.pow(t - 1, 2);
};

export const AnimatedCheckmark: React.FC = () => {
  const frame = useCurrentFrame();

  const { checkmarkCenterX, checkmarkCenterY, checkmarkSize, checkmarkStrokeWidth } =
    DIMENSIONS;
  const radius = checkmarkSize / 2;

  // Frame 0-8: Scale from 0.15 to 1 with easeOutBack (bounce overshoot)
  // Starts at 0.15 so the element is visible from frame 0
  const scale = interpolate(
    frame,
    [ANIMATION.checkmarkScaleStart, ANIMATION.checkmarkScaleEnd],
    [0.15, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: easeOutBack,
    },
  );

  // Frame 0-8: Checkmark path draws via strokeDashoffset (easeInOutQuad)
  const drawProgress = interpolate(
    frame,
    [ANIMATION.checkmarkScaleStart, ANIMATION.checkmarkScaleEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  const checkDashOffset = CHECKMARK_PATH_LENGTH * (1 - drawProgress);

  // Frame 22-24: Fade out with all elements
  const fadeOutOpacity = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  // SVG viewBox matches checkmarkSize
  const viewBox = `0 0 ${checkmarkSize} ${checkmarkSize}`;

  return (
    <div
      style={{
        position: 'absolute',
        left: checkmarkCenterX - checkmarkSize / 2,
        top: checkmarkCenterY - checkmarkSize / 2,
        width: checkmarkSize,
        height: checkmarkSize,
        transform: `scale(${scale})`,
        transformOrigin: 'center',
        opacity: fadeOutOpacity,
      }}
    >
      <svg width={checkmarkSize} height={checkmarkSize} viewBox={viewBox} fill="none">
        {/* Circle outline */}
        <circle
          cx={radius}
          cy={radius}
          r={radius - checkmarkStrokeWidth}
          fill="none"
          stroke={COLORS.checkmark}
          strokeWidth={checkmarkStrokeWidth}
        />
        {/* Checkmark path with draw animation */}
        <path
          d={CHECKMARK_PATH}
          stroke={COLORS.checkmark}
          strokeWidth={checkmarkStrokeWidth}
          strokeLinecap="round"
          strokeLinejoin="round"
          fill="none"
          strokeDasharray={CHECKMARK_PATH_LENGTH}
          strokeDashoffset={checkDashOffset}
        />
      </svg>
    </div>
  );
};

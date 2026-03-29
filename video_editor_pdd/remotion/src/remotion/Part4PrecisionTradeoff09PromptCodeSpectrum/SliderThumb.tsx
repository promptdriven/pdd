import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  BAR_X,
  BAR_Y,
  BAR_WIDTH,
  BAR_HEIGHT,
  BAR_BORDER_RADIUS,
  SLIDER_SIZE,
  SLIDER_START_X,
  SLIDER_END_X,
  SLIDER_Y,
  SLIDER_COLOR,
  LEFT_COLOR,
  ZONE_FILL_OPACITY,
  PHASE_SLIDER_START,
  PHASE_SLIDER_SLIDE_DURATION,
} from './constants';

/**
 * The slider thumb that slides from left edge to ~20% position,
 * plus the blue zone-fill overlay that tracks behind it.
 */
export const SliderThumb: React.FC = () => {
  const frame = useCurrentFrame();
  const localFrame = frame - PHASE_SLIDER_START;

  if (localFrame < 0) return null;

  // Main slide animation
  const slideProgress = interpolate(
    localFrame,
    [0, PHASE_SLIDER_SLIDE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  // Subtle elastic settle: overshoot to 1.02 then back to 1.0
  const settleOvershoot = interpolate(
    localFrame,
    [
      PHASE_SLIDER_SLIDE_DURATION,
      PHASE_SLIDER_SLIDE_DURATION + 8,
      PHASE_SLIDER_SLIDE_DURATION + 16,
    ],
    [1.02, 0.99, 1.0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const effectiveProgress =
    localFrame <= PHASE_SLIDER_SLIDE_DURATION
      ? slideProgress
      : slideProgress * settleOvershoot;

  const currentX =
    SLIDER_START_X + (SLIDER_END_X - SLIDER_START_X) * effectiveProgress;

  // Zone fill width: from BAR_X to currentX
  const zoneWidth = Math.max(0, currentX - BAR_X);

  // Fade in the slider itself
  const sliderOpacity = interpolate(localFrame, [0, 8], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <>
      {/* Zone fill overlay (blue tint behind slider) */}
      {zoneWidth > 0 && (
        <div
          style={{
            position: 'absolute',
            left: BAR_X,
            top: BAR_Y,
            width: zoneWidth,
            height: BAR_HEIGHT,
            backgroundColor: LEFT_COLOR,
            opacity: ZONE_FILL_OPACITY,
            borderTopLeftRadius: BAR_BORDER_RADIUS,
            borderBottomLeftRadius: BAR_BORDER_RADIUS,
            borderTopRightRadius: zoneWidth >= BAR_WIDTH ? BAR_BORDER_RADIUS : 0,
            borderBottomRightRadius:
              zoneWidth >= BAR_WIDTH ? BAR_BORDER_RADIUS : 0,
            pointerEvents: 'none',
          }}
        />
      )}

      {/* Slider thumb */}
      <div
        style={{
          position: 'absolute',
          left: currentX - SLIDER_SIZE / 2,
          top: SLIDER_Y - SLIDER_SIZE / 2,
          width: SLIDER_SIZE,
          height: SLIDER_SIZE,
          borderRadius: '50%',
          backgroundColor: SLIDER_COLOR,
          opacity: sliderOpacity,
          boxShadow: `0 0 16px rgba(255, 255, 255, 0.15), 0 2px 4px rgba(0, 0, 0, 0.3)`,
        }}
      />
    </>
  );
};

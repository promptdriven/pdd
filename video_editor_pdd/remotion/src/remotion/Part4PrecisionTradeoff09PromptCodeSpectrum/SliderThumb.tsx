import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  SLIDER_START,
  SLIDER_SLIDE_DURATION,
  SLIDER_START_X,
  SLIDER_END_X,
  SLIDER_Y,
  SLIDER_SIZE,
  SLIDER_COLOR,
  SLIDER_GLOW_COLOR,
  SLIDER_GLOW_OPACITY,
  SLIDER_GLOW_BLUR,
  SLIDER_SHADOW_COLOR,
  SLIDER_SHADOW_BLUR,
  SLIDER_SHADOW_OFFSET,
} from './constants';

export const SliderThumb: React.FC = () => {
  const frame = useCurrentFrame();

  // Slider only visible after SLIDER_START
  const localFrame = frame - SLIDER_START;
  if (localFrame < 0) return null;

  // ── Slide from left edge to rest position ──
  const slideProgress = interpolate(
    localFrame,
    [0, SLIDER_SLIDE_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  const currentX = interpolate(slideProgress, [0, 1], [SLIDER_START_X, SLIDER_END_X]);

  // ── Elastic settle (subtle overshoot 1.02 → 1.0) ──
  // Apply a scale bounce at the end of the slide
  const settleScale = interpolate(
    localFrame,
    [SLIDER_SLIDE_DURATION, SLIDER_SLIDE_DURATION + 8, SLIDER_SLIDE_DURATION + 20],
    [1.02, 0.98, 1.0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // ── Appear opacity ──
  const appearOpacity = interpolate(
    localFrame,
    [0, 6],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const radius = SLIDER_SIZE / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: currentX - radius,
        top: SLIDER_Y - radius,
        width: SLIDER_SIZE,
        height: SLIDER_SIZE,
        borderRadius: '50%',
        backgroundColor: SLIDER_COLOR,
        opacity: appearOpacity,
        transform: `scale(${settleScale})`,
        boxShadow: [
          `0 0 ${SLIDER_GLOW_BLUR}px rgba(255, 255, 255, ${SLIDER_GLOW_OPACITY})`,
          `0 ${SLIDER_SHADOW_OFFSET}px ${SLIDER_SHADOW_BLUR}px rgba(0, 0, 0, 0.3)`,
        ].join(', '),
        zIndex: 10,
      }}
    />
  );
};

export default SliderThumb;

import React from 'react';
import { useCurrentFrame, spring, interpolate, Easing } from 'remotion';
import {
  SLIDER_X,
  SLIDER_HEIGHT,
  SLIDER_WIDTH,
  BAR_Y,
  BAR_HEIGHT,
  TEXT_PRIMARY,
  SLIDER_GLOW_COLOR,
  GRAY,
  NOTCH_POSITIONS,
  NOTCH_SIZE,
  ANIM,
} from './constants';

const FPS = 30;

/**
 * The slider/thumb indicator on the spectrum bar, plus the
 * code-dip notch marks on the right side.
 */
export const SpectrumSlider: React.FC = () => {
  const frame = useCurrentFrame();

  // Spring animation for slider appearance
  const sliderScale = spring({
    frame: Math.max(0, frame - ANIM.sliderStart),
    fps: FPS,
    config: { stiffness: 150, damping: 12 },
  });

  // Gentle pulse on the slider starting from line2 appearance (frame 200)
  const pulsePhase = Math.max(0, frame - 200);
  const pulse = frame >= 200
    ? interpolate(
        pulsePhase % 40,
        [0, 20, 40],
        [1, 1.15, 1],
        { extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
      )
    : 1;

  const sliderTop = BAR_Y - 10; // extends 10px above the bar
  const sliderVisible = frame >= ANIM.sliderStart;

  return (
    <>
      {/* Slider glow */}
      {sliderVisible && (
        <div
          style={{
            position: 'absolute',
            left: SLIDER_X - 8,
            top: sliderTop,
            width: SLIDER_WIDTH + 16,
            height: SLIDER_HEIGHT,
            borderRadius: 4,
            backgroundColor: SLIDER_GLOW_COLOR,
            filter: 'blur(16px)',
            opacity: 0.3 * sliderScale * pulse,
            transform: `scaleY(${sliderScale})`,
            transformOrigin: 'center',
          }}
        />
      )}

      {/* Slider bar */}
      {sliderVisible && (
        <div
          style={{
            position: 'absolute',
            left: SLIDER_X - SLIDER_WIDTH / 2,
            top: sliderTop,
            width: SLIDER_WIDTH,
            height: SLIDER_HEIGHT,
            borderRadius: 2,
            backgroundColor: TEXT_PRIMARY,
            opacity: 0.9 * sliderScale,
            transform: `scaleY(${sliderScale})`,
            transformOrigin: 'center',
          }}
        />
      )}

      {/* Code-dip notches (small triangular indicators below the bar) */}
      {NOTCH_POSITIONS.map((notchX, i) => {
        const notchEntry = ANIM.notchStart + i * ANIM.notchStagger;
        const notchOpacity = interpolate(
          frame,
          [notchEntry, notchEntry + ANIM.notchFadeDuration],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: notchX - NOTCH_SIZE / 2,
              top: BAR_Y + BAR_HEIGHT,
              width: 0,
              height: 0,
              borderLeft: `${NOTCH_SIZE / 2}px solid transparent`,
              borderRight: `${NOTCH_SIZE / 2}px solid transparent`,
              borderTop: `${NOTCH_SIZE}px solid ${GRAY}`,
              opacity: 0.3 * notchOpacity,
            }}
          />
        );
      })}
    </>
  );
};

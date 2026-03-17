import React, { useMemo } from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  CURVE_COLOR,
  SLIDER_COLOR,
  ANIM,
  generateCurvePoints,
} from './constants';

export const CurveSlider: React.FC = () => {
  const frame = useCurrentFrame();
  const points = useMemo(() => generateCurvePoints(200), []);

  // During curve draw (60-180), slider follows the drawing edge
  const drawProgress = interpolate(
    frame,
    [ANIM.CURVE_START, ANIM.CURVE_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // During slider travel (300-390), slider moves along entire curve
  const sliderTravelProgress = interpolate(
    frame,
    [ANIM.SLIDER_START, ANIM.SLIDER_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Determine current slider position
  let sliderX: number;
  let sliderY: number;
  let visible = false;

  if (frame >= ANIM.CURVE_START && frame < ANIM.CURVE_END) {
    // Follow drawing edge
    const idx = Math.min(
      Math.floor(drawProgress * (points.length - 1)),
      points.length - 1
    );
    sliderX = points[idx][0];
    sliderY = points[idx][1];
    visible = true;
  } else if (frame >= ANIM.SLIDER_START && frame <= ANIM.HOLD_END) {
    // Travel along completed curve
    const progress =
      frame < ANIM.SLIDER_END ? sliderTravelProgress : 1;
    const idx = Math.min(
      Math.floor(progress * (points.length - 1)),
      points.length - 1
    );
    sliderX = points[idx][0];
    sliderY = points[idx][1];
    visible = true;
  } else if (frame >= ANIM.CURVE_END && frame < ANIM.SLIDER_START) {
    // Hold at end of curve after draw, before travel
    sliderX = points[points.length - 1][0];
    sliderY = points[points.length - 1][1];
    visible = true;
  }

  if (!visible) return null;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id="slider-glow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="8" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Glow */}
      <circle
        cx={sliderX!}
        cy={sliderY!}
        r={8}
        fill={CURVE_COLOR}
        fillOpacity={0.3}
        filter="url(#slider-glow)"
      />

      {/* Main slider dot */}
      <circle
        cx={sliderX!}
        cy={sliderY!}
        r={5}
        fill={SLIDER_COLOR}
      />
    </svg>
  );
};

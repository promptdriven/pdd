import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, TIMING, curvePoint } from './constants';

export const CurveSlider: React.FC = () => {
  const frame = useCurrentFrame();

  // During curve draw (60-180): slider follows drawing edge
  const drawT = interpolate(
    frame,
    [TIMING.curveStart, TIMING.curveEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  // During slider travel (300-390): slider moves left to right on completed curve
  const travelT = interpolate(
    frame,
    [TIMING.sliderStart, TIMING.sliderEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  let testCount: number;
  let visible = false;

  if (frame >= TIMING.curveStart && frame < TIMING.curveEnd) {
    // Following the draw edge
    testCount = drawT * 50;
    visible = true;
  } else if (frame >= TIMING.curveEnd && frame < TIMING.sliderStart) {
    // Parked at right end after draw
    testCount = 50;
    visible = true;
  } else if (frame >= TIMING.sliderStart) {
    // Traveling left to right
    testCount = travelT * 50;
    visible = true;
  } else {
    testCount = 0;
  }

  if (!visible) return null;

  const pos = curvePoint(testCount);

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id="sliderGlow" x="-100%" y="-100%" width="300%" height="300%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="8" />
        </filter>
      </defs>

      {/* Glow */}
      <circle
        cx={pos.x}
        cy={pos.y}
        r={16}
        fill={COLORS.curve}
        fillOpacity={0.3}
        filter="url(#sliderGlow)"
      />

      {/* Slider dot */}
      <circle
        cx={pos.x}
        cy={pos.y}
        r={5}
        fill={COLORS.slider}
      />
    </svg>
  );
};

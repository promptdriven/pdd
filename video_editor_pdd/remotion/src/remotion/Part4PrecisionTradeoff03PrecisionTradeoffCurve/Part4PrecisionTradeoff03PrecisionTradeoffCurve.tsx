import React from 'react';
import { AbsoluteFill, useCurrentFrame, Easing, interpolate } from 'remotion';
import { BG_COLOR, TITLE_COLOR } from './constants';
import { ChartAxes } from './ChartAxes';
import { InverseCurve } from './InverseCurve';
import { AnnotationZones } from './AnnotationZones';
import { CurveSlider } from './CurveSlider';

export const defaultPart4PrecisionTradeoff03PrecisionTradeoffCurveProps = {};

export const Part4PrecisionTradeoff03PrecisionTradeoffCurve: React.FC = () => {
  const frame = useCurrentFrame();

  // Title fade-in (frames 0-20)
  const titleOpacity = interpolate(frame, [0, 20], [0, 0.8], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* Title */}
      <div
        style={{
          position: 'absolute',
          top: 60,
          left: 0,
          right: 0,
          textAlign: 'center',
          opacity: titleOpacity,
        }}
      >
        <span
          style={{
            fontSize: 20,
            fontWeight: 700,
            color: TITLE_COLOR,
            letterSpacing: '0.1em',
          }}
        >
          THE PRECISION TRADEOFF
        </span>
      </div>

      {/* Chart Axes */}
      <ChartAxes />

      {/* Inverse Curve */}
      <InverseCurve />

      {/* Annotation Zones */}
      <AnnotationZones />

      {/* Curve Slider */}
      <CurveSlider />
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff03PrecisionTradeoffCurve;

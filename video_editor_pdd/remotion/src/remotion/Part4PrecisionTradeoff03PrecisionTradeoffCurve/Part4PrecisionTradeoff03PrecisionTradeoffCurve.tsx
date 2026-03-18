import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, TIMING } from './constants';
import { ChartAxes } from './ChartAxes';
import { InverseCurve } from './InverseCurve';
import { HighlightZones } from './HighlightZones';
import { CurveSlider } from './CurveSlider';

export const defaultPart4PrecisionTradeoff03PrecisionTradeoffCurveProps = {};

export const Part4PrecisionTradeoff03PrecisionTradeoffCurve: React.FC = () => {
  const frame = useCurrentFrame();

  // Title fade in (frames 0-20)
  const titleOpacity = interpolate(frame, [0, 20], [0, 0.8], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Background is always visible from frame 0
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* Title — visible from frame 0 with fade */}
      <div
        style={{
          position: 'absolute',
          top: 60,
          left: 0,
          width: 1920,
          textAlign: 'center',
          opacity: titleOpacity,
          fontSize: 20,
          fontWeight: 700,
          color: COLORS.title,
          letterSpacing: 2,
        }}
      >
        THE PRECISION TRADEOFF
      </div>

      {/* Chart axes — draw from frame 0 */}
      <ChartAxes />

      {/* Inverse curve — draws from frame 60 */}
      <InverseCurve />

      {/* Highlight zones — left from 180, right from 240 */}
      <HighlightZones />

      {/* Slider dot — follows curve draw, then travels */}
      <CurveSlider />
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff03PrecisionTradeoffCurve;

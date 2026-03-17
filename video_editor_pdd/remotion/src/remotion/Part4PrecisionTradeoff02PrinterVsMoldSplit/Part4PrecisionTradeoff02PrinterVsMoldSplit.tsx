import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  Easing,
  interpolate,
  Sequence,
} from 'remotion';
import {
  BG_COLOR,
  LEFT_BG,
  RIGHT_BG,
  SPLIT_X,
  SPLIT_LINE_COLOR,
  SPLIT_LINE_WIDTH,
  LEFT_ACCENT,
  RIGHT_ACCENT,
  TEXT_COLOR,
  SPLIT_DRAW_END,
  CALLOUT_START,
  CALLOUT_FADE_FRAMES,
  TOTAL_FRAMES,
  HEIGHT,
} from './constants';
import { CoordinateGrid } from './CoordinateGrid';
import { MoldCavity } from './MoldCavity';

export const defaultPart4PrecisionTradeoff02PrinterVsMoldSplitProps = {};

export const Part4PrecisionTradeoff02PrinterVsMoldSplit: React.FC = () => {
  const frame = useCurrentFrame();

  // Split line draw animation (vertical line from center outward)
  const splitLineProgress = interpolate(
    frame,
    [0, SPLIT_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );
  const splitLineHeight = splitLineProgress * HEIGHT;
  const splitLineTop = (HEIGHT - splitLineHeight) / 2;

  // Panel header fade-in
  const headerOpacity = interpolate(
    frame,
    [5, SPLIT_DRAW_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Bottom callout fade
  const calloutOpacity = interpolate(
    frame,
    [CALLOUT_START, CALLOUT_START + CALLOUT_FADE_FRAMES],
    [0, 0.6],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Left Panel — 3D Printing */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: SPLIT_X - SPLIT_LINE_WIDTH / 2,
          height: HEIGHT,
          backgroundColor: LEFT_BG,
          overflow: 'hidden',
        }}
      >
        {/* Panel header */}
        <div
          style={{
            position: 'absolute',
            top: 40,
            left: 0,
            width: '100%',
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 14,
            fontWeight: 600,
            letterSpacing: 2,
            color: LEFT_ACCENT,
            opacity: headerOpacity * 0.5,
            zIndex: 10,
          }}
        >
          3D PRINTING
        </div>

        {/* Coordinate Grid with nozzle */}
        <CoordinateGrid />
      </div>

      {/* Split divider line */}
      <div
        style={{
          position: 'absolute',
          left: SPLIT_X - SPLIT_LINE_WIDTH / 2,
          top: splitLineTop,
          width: SPLIT_LINE_WIDTH,
          height: splitLineHeight,
          backgroundColor: SPLIT_LINE_COLOR,
          opacity: 0.25,
        }}
      />

      {/* Right Panel — Injection Molding */}
      <div
        style={{
          position: 'absolute',
          left: SPLIT_X + SPLIT_LINE_WIDTH / 2,
          top: 0,
          width: 1920 - SPLIT_X - SPLIT_LINE_WIDTH / 2,
          height: HEIGHT,
          backgroundColor: RIGHT_BG,
          overflow: 'hidden',
        }}
      >
        {/* Panel header */}
        <div
          style={{
            position: 'absolute',
            top: 40,
            left: 0,
            width: '100%',
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 14,
            fontWeight: 600,
            letterSpacing: 2,
            color: RIGHT_ACCENT,
            opacity: headerOpacity * 0.5,
            zIndex: 10,
          }}
        >
          INJECTION MOLDING
        </div>

        {/* Mold with fluid fill */}
        <MoldCavity />
      </div>

      {/* Bottom callout */}
      <Sequence from={CALLOUT_START} durationInFrames={TOTAL_FRAMES - CALLOUT_START}>
        <div
          style={{
            position: 'absolute',
            bottom: 100,
            left: 0,
            width: 1920,
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 14,
            color: TEXT_COLOR,
            opacity: calloutOpacity,
          }}
        >
          Precision through{' '}
          <span style={{ color: LEFT_ACCENT }}>specification</span>
          {' '}vs. precision through{' '}
          <span style={{ color: RIGHT_ACCENT }}>constraint</span>
        </div>
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff02PrinterVsMoldSplit;

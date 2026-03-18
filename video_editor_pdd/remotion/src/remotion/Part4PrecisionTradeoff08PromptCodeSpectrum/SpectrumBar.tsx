import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  BAR_X,
  BAR_Y,
  BAR_WIDTH,
  BAR_HEIGHT,
  BAR_RADIUS,
  BLUE,
  GRAY,
  BORDER_COLOR,
  TIMING,
} from './constants';

/**
 * The horizontal spectrum/gradient bar that draws from center outward,
 * plus its endpoint labels ("Pure natural language" / "Pure code").
 */
export const SpectrumBar: React.FC = () => {
  const frame = useCurrentFrame();

  // Bar draws from center outward over frames 0-30
  const drawProgress = interpolate(
    frame,
    [TIMING.barDrawStart, TIMING.barDrawStart + TIMING.barDrawDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Endpoint labels fade in during frames 15-30
  const labelOpacity = interpolate(
    frame,
    [15, 30],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const centerX = BAR_X + BAR_WIDTH / 2;
  const currentHalfWidth = (BAR_WIDTH / 2) * drawProgress;
  const currentLeft = centerX - currentHalfWidth;
  const currentWidth = currentHalfWidth * 2;

  return (
    <>
      {/* Spectrum bar glow */}
      <div
        style={{
          position: 'absolute',
          left: currentLeft,
          top: BAR_Y,
          width: currentWidth,
          height: BAR_HEIGHT,
          borderRadius: BAR_RADIUS,
          background: `linear-gradient(to right, ${BLUE}, ${GRAY})`,
          filter: 'blur(8px)',
          opacity: 0.1 * drawProgress,
        }}
      />

      {/* Spectrum bar */}
      <div
        style={{
          position: 'absolute',
          left: currentLeft,
          top: BAR_Y,
          width: currentWidth,
          height: BAR_HEIGHT,
          borderRadius: BAR_RADIUS,
          background: `linear-gradient(to right, ${BLUE}, ${GRAY})`,
          border: `1px solid rgba(51, 65, 85, ${0.3 * drawProgress})`,
          overflow: 'hidden',
        }}
      />

      {/* Left endpoint label: "Pure natural language" */}
      <div
        style={{
          position: 'absolute',
          left: BAR_X,
          top: BAR_Y + BAR_HEIGHT + 20,
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 700,
          color: BLUE,
          opacity: 0.7 * labelOpacity,
          whiteSpace: 'nowrap',
        }}
      >
        Pure natural language
      </div>

      {/* Right endpoint label: "Pure code" */}
      <div
        style={{
          position: 'absolute',
          left: BAR_X + BAR_WIDTH,
          top: BAR_Y + BAR_HEIGHT + 20,
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 700,
          color: GRAY,
          opacity: 0.7 * labelOpacity,
          whiteSpace: 'nowrap',
          transform: 'translateX(-100%)',
        }}
      >
        Pure code
      </div>
    </>
  );
};

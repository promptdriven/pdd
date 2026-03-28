import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  BAR_X,
  BAR_Y,
  BAR_WIDTH,
  BAR_HEIGHT,
  BAR_BORDER_RADIUS,
  BAR_BORDER_COLOR,
  LEFT_COLOR,
  MID_COLOR,
  RIGHT_COLOR,
  BAR_DRAW_START,
  BAR_DRAW_DURATION,
  ENDPOINT_LABEL_START,
  ENDPOINT_LABEL_DURATION,
  ENDPOINT_FONT_SIZE,
  ENDPOINT_FONT_WEIGHT,
  LABEL_FONT_FAMILY,
  ZONE_FILL_COLOR,
  ZONE_FILL_OPACITY,
  SLIDER_START,
  SLIDER_SLIDE_DURATION,
  SLIDER_REST_FRACTION,
} from './constants';

const GRADIENT_ID = 'spectrum-gradient';

export const SpectrumBar: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Bar draw-in from center ──
  const drawProgress = interpolate(
    frame,
    [BAR_DRAW_START, BAR_DRAW_START + BAR_DRAW_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // The bar expands from center: clip it symmetrically
  const visibleWidth = BAR_WIDTH * drawProgress;
  const clipLeft = BAR_X + (BAR_WIDTH - visibleWidth) / 2;
  const clipRight = clipLeft + visibleWidth;

  // ── Endpoint labels ──
  const labelOpacity = interpolate(
    frame,
    [ENDPOINT_LABEL_START, ENDPOINT_LABEL_START + ENDPOINT_LABEL_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // ── Zone fill (prompt space) ──
  const zoneFraction = interpolate(
    frame,
    [SLIDER_START, SLIDER_START + SLIDER_SLIDE_DURATION],
    [0, SLIDER_REST_FRACTION],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );
  const zoneWidth = BAR_WIDTH * zoneFraction;

  return (
    <>
      {/* SVG gradient definition */}
      <svg
        style={{ position: 'absolute', width: 0, height: 0 }}
        aria-hidden="true"
      >
        <defs>
          <linearGradient id={GRADIENT_ID} x1="0%" y1="0%" x2="100%" y2="0%">
            <stop offset="0%" stopColor={LEFT_COLOR} />
            <stop offset="50%" stopColor={MID_COLOR} />
            <stop offset="100%" stopColor={RIGHT_COLOR} />
          </linearGradient>
        </defs>
      </svg>

      {/* Spectrum bar (clipped for draw-in animation) */}
      <div
        style={{
          position: 'absolute',
          left: clipLeft,
          top: BAR_Y,
          width: clipRight - clipLeft,
          height: BAR_HEIGHT,
          overflow: 'hidden',
          borderRadius: BAR_BORDER_RADIUS,
        }}
      >
        <div
          style={{
            position: 'absolute',
            left: -(clipLeft - BAR_X),
            top: 0,
            width: BAR_WIDTH,
            height: BAR_HEIGHT,
            borderRadius: BAR_BORDER_RADIUS,
            background: `linear-gradient(to right, ${LEFT_COLOR}, ${MID_COLOR}, ${RIGHT_COLOR})`,
            border: `1px solid ${BAR_BORDER_COLOR}`,
            boxSizing: 'border-box',
          }}
        />
      </div>

      {/* Zone fill overlay (prompt space) */}
      {zoneFraction > 0 && (
        <div
          style={{
            position: 'absolute',
            left: BAR_X,
            top: BAR_Y,
            width: zoneWidth,
            height: BAR_HEIGHT,
            borderRadius: `${BAR_BORDER_RADIUS}px 0 0 ${BAR_BORDER_RADIUS}px`,
            backgroundColor: ZONE_FILL_COLOR,
            opacity: ZONE_FILL_OPACITY,
            pointerEvents: 'none',
          }}
        />
      )}

      {/* Left endpoint label */}
      <div
        style={{
          position: 'absolute',
          left: BAR_X,
          top: BAR_Y - 30,
          fontFamily: LABEL_FONT_FAMILY,
          fontSize: ENDPOINT_FONT_SIZE,
          fontWeight: ENDPOINT_FONT_WEIGHT,
          color: LEFT_COLOR,
          opacity: labelOpacity,
          whiteSpace: 'nowrap',
        }}
      >
        Pure natural language
      </div>

      {/* Right endpoint label */}
      <div
        style={{
          position: 'absolute',
          right: 1920 - (BAR_X + BAR_WIDTH),
          top: BAR_Y - 30,
          fontFamily: LABEL_FONT_FAMILY,
          fontSize: ENDPOINT_FONT_SIZE,
          fontWeight: ENDPOINT_FONT_WEIGHT,
          color: RIGHT_COLOR,
          opacity: labelOpacity,
          whiteSpace: 'nowrap',
          textAlign: 'right',
        }}
      >
        Pure code
      </div>
    </>
  );
};

export default SpectrumBar;

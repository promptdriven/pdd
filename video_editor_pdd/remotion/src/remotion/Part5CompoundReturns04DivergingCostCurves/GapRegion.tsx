import React, { useMemo } from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CHART_LEFT,
  CHART_WIDTH,
  CHART_HEIGHT,
  CHART_BOTTOM,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
  PATCHING_COLOR,
  PDD_COLOR,
  GAP_FILL_START,
  GAP_FILL_DURATION,
  GAP_LABEL_START,
  GAP_LABEL_FADE,
  GAP_LABEL_COLOR,
  FONT_FAMILY,
  PATCHING_DATA,
  PDD_BASELINE,
} from './constants';

/** Map data coordinates to pixel coordinates (duplicated here to avoid cross-file import issues) */
const xToPixel = (x: number) =>
  CHART_LEFT + ((x - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;

const yToPixelCorrected = (y: number) =>
  CHART_BOTTOM - ((y - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;

export const GapRegion: React.FC = () => {
  const frame = useCurrentFrame();

  // Gap fill opacity: fades in over GAP_FILL_DURATION starting at GAP_FILL_START
  const fillOpacity = interpolate(
    frame,
    [GAP_FILL_START, GAP_FILL_START + GAP_FILL_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Gap pulse: subtle opacity oscillation after gap is visible
  const pulseOpacity =
    frame > GAP_FILL_START + GAP_FILL_DURATION
      ? interpolate(
          Math.sin(((frame - GAP_FILL_START - GAP_FILL_DURATION) / 60) * Math.PI * 2),
          [-1, 1],
          [0.04, 0.08],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        )
      : 0.06;

  // Gap label fade in
  const labelOpacity = interpolate(
    frame,
    [GAP_LABEL_START, GAP_LABEL_START + GAP_LABEL_FADE],
    [0, 0.5],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Build the polygon path: patching curve (top boundary) -> PDD baseline (bottom boundary)
  const polygonPath = useMemo(() => {
    // Upper boundary: patching data points (left to right)
    const upperPoints = PATCHING_DATA.map(
      (pt) => `${xToPixel(pt.x)},${yToPixelCorrected(pt.y)}`
    );
    // Lower boundary: PDD baseline (right to left)
    const lowerPoints = [
      `${xToPixel(X_MAX)},${yToPixelCorrected(PDD_BASELINE)}`,
      `${xToPixel(X_MIN)},${yToPixelCorrected(PDD_BASELINE)}`,
    ];

    return [...upperPoints, ...lowerPoints].join(' ');
  }, []);

  // Center point for the "The Gap" label
  // Find midpoint x and average y between curves at that x
  const labelX = xToPixel(6);
  // At x=6, patching y ≈ 0.55, PDD y = 0.10, midpoint ≈ 0.325
  const labelY = yToPixelCorrected(0.325);

  return (
    <>
      <svg
        width={1920}
        height={1080}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <defs>
          <linearGradient id="gapGradient" x1="0" y1="0" x2="0" y2="1">
            <stop offset="0%" stopColor={PATCHING_COLOR} stopOpacity={0.06} />
            <stop offset="100%" stopColor={PDD_COLOR} stopOpacity={0.04} />
          </linearGradient>
        </defs>
        <polygon
          points={polygonPath}
          fill="url(#gapGradient)"
          opacity={fillOpacity * (pulseOpacity / 0.06)}
        />
      </svg>

      {/* "The Gap" label */}
      <div
        style={{
          position: 'absolute',
          left: labelX - 50,
          top: labelY - 10,
          width: 100,
          textAlign: 'center',
          fontFamily: FONT_FAMILY,
          fontSize: 14,
          fontWeight: 400,
          color: GAP_LABEL_COLOR,
          opacity: labelOpacity,
        }}
      >
        The Gap
      </div>
    </>
  );
};

export default GapRegion;

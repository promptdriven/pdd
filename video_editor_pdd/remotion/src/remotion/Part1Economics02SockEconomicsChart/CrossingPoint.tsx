import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  MARGIN_LEFT,
  MARGIN_TOP,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
  CROSSING_POINT,
  CROSSING_APPEAR_FRAME,
  CROSSING_FADE_DURATION,
  CROSSING_LABEL_COLOR,
  CROSSING_LABEL_OPACITY,
  FONT_FAMILY,
} from './constants';

const xToPixel = (x: number): number =>
  MARGIN_LEFT + ((x - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;

const yToPixel = (y: number): number =>
  MARGIN_TOP + ((Y_MAX - y) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;

export const CrossingPointMarker: React.FC = () => {
  const frame = useCurrentFrame();

  const cx = xToPixel(CROSSING_POINT.x);
  const cy = yToPixel(CROSSING_POINT.y);

  // Appear: easeOut(quad) over CROSSING_FADE_DURATION
  const appear = interpolate(
    frame,
    [CROSSING_APPEAR_FRAME, CROSSING_APPEAR_FRAME + CROSSING_FADE_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) },
  );

  if (appear <= 0) return null;

  // Gentle pulse on the glow: easeInOut(sine), period ~60 frames
  const pulsePhase = (frame - CROSSING_APPEAR_FRAME) / 60;
  const pulse = 0.5 + 0.5 * Math.sin(pulsePhase * Math.PI * 2);
  const glowOpacity = interpolate(pulse, [0, 1], [0.10, 0.22]);

  // Label position
  const labelX = cx;
  const labelY = cy - 40;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Glow */}
      <circle
        cx={cx}
        cy={cy}
        r={16}
        fill="#FFFFFF"
        fillOpacity={glowOpacity * appear}
      />

      {/* Solid dot */}
      <circle
        cx={cx}
        cy={cy}
        r={8}
        fill="#FFFFFF"
        fillOpacity={0.9 * appear}
      />

      {/* Dashed annotation line from label to point */}
      <line
        x1={labelX}
        y1={labelY + 10}
        x2={cx}
        y2={cy - 12}
        stroke={CROSSING_LABEL_COLOR}
        strokeOpacity={0.3 * appear}
        strokeWidth={1}
        strokeDasharray="4 3"
      />

      {/* "The Threshold" label */}
      <text
        x={labelX}
        y={labelY}
        textAnchor="middle"
        fill={CROSSING_LABEL_COLOR}
        fillOpacity={CROSSING_LABEL_OPACITY * appear}
        fontFamily={FONT_FAMILY}
        fontSize={18}
        fontWeight={700}
      >
        The Threshold
      </text>
    </svg>
  );
};

export default CrossingPointMarker;

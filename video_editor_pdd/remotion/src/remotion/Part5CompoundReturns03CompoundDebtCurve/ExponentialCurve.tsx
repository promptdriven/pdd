import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  DEBT_CURVE_COLOR,
  DEBT_DATA,
  CURVE_DURATION,
} from './constants';

/**
 * Converts normalized data points (0-1) to chart pixel coordinates.
 */
function toPixel(point: { x: number; y: number }): { px: number; py: number } {
  const px = CHART_LEFT + point.x * (CHART_RIGHT - CHART_LEFT);
  // y is inverted: 0 = bottom (CHART_BOTTOM), 1 = top (CHART_TOP)
  const py = CHART_BOTTOM - point.y * (CHART_BOTTOM - CHART_TOP);
  return { px, py };
}

/**
 * Build SVG path string from data points using smooth curves.
 */
function buildCurvePath(data: { x: number; y: number }[]): string {
  if (data.length < 2) return '';
  const first = toPixel(data[0]);
  let d = `M ${first.px} ${first.py}`;

  for (let i = 1; i < data.length; i++) {
    const prev = toPixel(data[i - 1]);
    const curr = toPixel(data[i]);
    // Use quadratic bezier for smooth curve
    const cpx = (prev.px + curr.px) / 2;
    const cpy = prev.py; // control point stays at prev height for exponential feel
    d += ` Q ${cpx} ${cpy} ${curr.px} ${curr.py}`;
  }
  return d;
}

export const ExponentialCurve: React.FC = () => {
  const frame = useCurrentFrame();

  // Draw progress with easeIn(cubic) — starts slow, accelerates
  const drawProgress = interpolate(frame, [0, CURVE_DURATION], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.cubic),
  });

  const path = buildCurvePath(DEBT_DATA);

  // Estimate total path length for stroke-dasharray animation
  // We use a generous estimate; actual dashoffset will clip it
  const estimatedLength = 2200;
  const visibleLength = drawProgress * estimatedLength;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id="curveGlow">
          <feGaussianBlur stdDeviation="6" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Glow trail behind the curve */}
      <path
        d={path}
        fill="none"
        stroke={DEBT_CURVE_COLOR}
        strokeWidth={6}
        opacity={0.08}
        strokeDasharray={estimatedLength}
        strokeDashoffset={estimatedLength - visibleLength}
        strokeLinecap="round"
        filter="url(#curveGlow)"
      />

      {/* Main curve */}
      <path
        d={path}
        fill="none"
        stroke={DEBT_CURVE_COLOR}
        strokeWidth={3}
        strokeDasharray={estimatedLength}
        strokeDashoffset={estimatedLength - visibleLength}
        strokeLinecap="round"
      />
    </svg>
  );
};

/**
 * Formula label that types in character by character.
 */
export const FormulaLabel: React.FC = () => {
  const frame = useCurrentFrame();
  const text = 'Debt × (1 + Rate)^Time';
  const typeDuration = 30; // frames to type full text

  const charsVisible = Math.floor(
    interpolate(frame, [0, typeDuration], [0, text.length], {
      extrapolateRight: 'clamp',
    })
  );

  const opacity = interpolate(frame, [0, 10], [0, 0.6], {
    extrapolateRight: 'clamp',
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: 1200,
        top: 250,
        fontFamily: 'JetBrains Mono, monospace',
        fontSize: 14,
        color: DEBT_CURVE_COLOR,
        opacity,
        whiteSpace: 'nowrap',
        transform: 'rotate(-15deg)',
        transformOrigin: 'left center',
      }}
    >
      {text.slice(0, charsVisible)}
      {charsVisible < text.length && (
        <span style={{ opacity: frame % 10 < 5 ? 1 : 0 }}>|</span>
      )}
    </div>
  );
};

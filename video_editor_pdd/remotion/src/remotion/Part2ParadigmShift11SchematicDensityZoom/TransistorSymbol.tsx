import React from 'react';
import {
  STROKE_COLOR,
  WIRE_COLOR,
  TRANSISTOR_STROKE_WIDTH,
  WIRE_STROKE_WIDTH,
} from './constants';

/**
 * A single MOSFET transistor symbol with hand-drawn wobble.
 * Rendered as SVG group at local coordinates; caller positions via transform.
 */

interface TransistorSymbolProps {
  x: number;
  y: number;
  seed: number; // for pseudo-random wobble
  scale?: number;
}

// Deterministic wobble from seed
function wobble(seed: number, idx: number): number {
  const v = Math.sin(seed * 9301 + idx * 4973) * 0.7;
  return v;
}

const TransistorSymbol: React.FC<TransistorSymbolProps> = ({
  x,
  y,
  seed,
  scale = 1,
}) => {
  const w = wobble;
  // MOSFET symbol: gate line on left, channel bar, source/drain leads
  // Simplified hand-drawn style
  const gateX = -10 + w(seed, 0);
  const channelX = 0 + w(seed, 1);

  return (
    <g transform={`translate(${x}, ${y}) scale(${scale})`}>
      {/* Gate lead (horizontal, from left) */}
      <line
        x1={-18 + w(seed, 2)}
        y1={0 + w(seed, 3)}
        x2={gateX}
        y2={0 + w(seed, 4)}
        stroke={WIRE_COLOR}
        strokeWidth={WIRE_STROKE_WIDTH}
        strokeLinecap="round"
      />
      {/* Gate vertical bar */}
      <line
        x1={gateX + w(seed, 5) * 0.3}
        y1={-12 + w(seed, 6)}
        x2={gateX + w(seed, 7) * 0.3}
        y2={12 + w(seed, 8)}
        stroke={STROKE_COLOR}
        strokeWidth={TRANSISTOR_STROKE_WIDTH}
        strokeLinecap="round"
      />
      {/* Channel bar */}
      <line
        x1={channelX + w(seed, 9) * 0.3}
        y1={-12 + w(seed, 10)}
        x2={channelX + w(seed, 11) * 0.3}
        y2={12 + w(seed, 12)}
        stroke={STROKE_COLOR}
        strokeWidth={TRANSISTOR_STROKE_WIDTH + 0.5}
        strokeLinecap="round"
      />
      {/* Source lead (top-right) */}
      <line
        x1={channelX + w(seed, 13) * 0.3}
        y1={-8 + w(seed, 14)}
        x2={14 + w(seed, 15)}
        y2={-8 + w(seed, 16)}
        stroke={WIRE_COLOR}
        strokeWidth={WIRE_STROKE_WIDTH}
        strokeLinecap="round"
      />
      <line
        x1={14 + w(seed, 17)}
        y1={-8 + w(seed, 18)}
        x2={14 + w(seed, 19)}
        y2={-18 + w(seed, 20)}
        stroke={WIRE_COLOR}
        strokeWidth={WIRE_STROKE_WIDTH}
        strokeLinecap="round"
      />
      {/* Drain lead (bottom-right) */}
      <line
        x1={channelX + w(seed, 21) * 0.3}
        y1={8 + w(seed, 22)}
        x2={14 + w(seed, 23)}
        y2={8 + w(seed, 24)}
        stroke={WIRE_COLOR}
        strokeWidth={WIRE_STROKE_WIDTH}
        strokeLinecap="round"
      />
      <line
        x1={14 + w(seed, 25)}
        y1={8 + w(seed, 26)}
        x2={14 + w(seed, 27)}
        y2={18 + w(seed, 28)}
        stroke={WIRE_COLOR}
        strokeWidth={WIRE_STROKE_WIDTH}
        strokeLinecap="round"
      />
      {/* Arrow on drain */}
      <polygon
        points={`${channelX + 2 + w(seed, 29) * 0.2},${8 + w(seed, 30) * 0.2} ${channelX + 5 + w(seed, 31) * 0.2},${6 + w(seed, 32) * 0.2} ${channelX + 5 + w(seed, 33) * 0.2},${10 + w(seed, 34) * 0.2}`}
        fill={STROKE_COLOR}
      />
    </g>
  );
};

export default TransistorSymbol;

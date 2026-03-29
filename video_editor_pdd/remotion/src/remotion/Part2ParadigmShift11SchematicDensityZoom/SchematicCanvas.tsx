import React, { useMemo } from 'react';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  STROKE_COLOR,
  WIRE_COLOR,
  TRANSISTOR_STROKE_WIDTH,
  WIRE_STROKE_WIDTH,
  SCHEMATIC_SPREAD,
} from './constants';

/**
 * Generates the schematic drawing: transistor symbols + connection wires.
 *
 * For performance we render transistors in tiers:
 *   - Tier 0 (0..30):    Full detailed transistor SVG symbols
 *   - Tier 1 (30..500):  Simplified transistor marks (3 lines each)
 *   - Tier 2 (500..5000): Tiny cross marks
 *   - Tier 3 (5000..50000): Single dots / micro-lines
 *
 * `visibleCount` controls how many are drawn.
 * The parent applies a CSS transform for zoom.
 */

interface SchematicCanvasProps {
  visibleCount: number;
}

// Deterministic pseudo-random from seed
function seededRandom(seed: number): number {
  const x = Math.sin(seed * 12345.6789 + 43758.5453) * 43758.5453;
  return x - Math.floor(x);
}

interface TransistorPos {
  x: number;
  y: number;
  seed: number;
  tier: number;
}

// Pre-compute layout positions for all transistors
function generateLayout(count: number): TransistorPos[] {
  const positions: TransistorPos[] = [];
  const cx = CANVAS_WIDTH / 2;
  const cy = CANVAS_HEIGHT / 2;
  const halfSpread = SCHEMATIC_SPREAD / 2;

  for (let i = 0; i < count; i++) {
    // Spread: inner transistors first, outer ones added later
    // Use a spiral-ish distribution so early ones cluster at center
    const r = seededRandom(i);
    const angle = seededRandom(i + 50000) * Math.PI * 2;
    // Distance from center grows with index (square-root distribution for area-uniformity)
    const dist = Math.sqrt(i / count) * halfSpread;
    const x = cx + Math.cos(angle) * dist * (0.5 + r * 0.5);
    const y = cy + Math.sin(angle) * dist * (0.5 + r * 0.5);

    let tier: number;
    if (i < 30) tier = 0;
    else if (i < 500) tier = 1;
    else if (i < 5000) tier = 2;
    else tier = 3;

    positions.push({ x, y, seed: i, tier });
  }
  return positions;
}

// Memoised full layout (50k positions)
const FULL_LAYOUT = generateLayout(50000);

// Draw connection wires between nearby transistors
function renderWires(positions: TransistorPos[], maxWires: number): React.ReactNode[] {
  const wires: React.ReactNode[] = [];
  const wireCount = Math.min(maxWires, positions.length - 1);
  for (let i = 0; i < wireCount; i++) {
    const a = positions[i];
    // Connect to a "nearby" transistor (deterministic neighbour)
    const neighbourIdx = Math.min(
      i + 1 + Math.floor(seededRandom(i + 99999) * 3),
      positions.length - 1
    );
    const b = positions[neighbourIdx];
    // Manhattan-style routing (horizontal then vertical)
    const midX = b.x;
    wires.push(
      <path
        key={`w-${i}`}
        d={`M${a.x},${a.y} L${midX},${a.y} L${midX},${b.y}`}
        stroke={WIRE_COLOR}
        strokeWidth={WIRE_STROKE_WIDTH}
        fill="none"
        strokeLinecap="round"
      />
    );
  }
  return wires;
}

// Detailed transistor symbol for tier 0
function renderDetailedTransistor(pos: TransistorPos): React.ReactNode {
  const { x, y, seed } = pos;
  const w = (s: number, idx: number) =>
    Math.sin(s * 9301 + idx * 4973) * 0.7;

  return (
    <g key={`t-${seed}`} transform={`translate(${x},${y})`}>
      {/* Gate lead */}
      <line x1={-18 + w(seed, 2)} y1={w(seed, 3)} x2={-10 + w(seed, 0)} y2={w(seed, 4)}
        stroke={WIRE_COLOR} strokeWidth={WIRE_STROKE_WIDTH} strokeLinecap="round" />
      {/* Gate bar */}
      <line x1={-10 + w(seed, 5) * 0.3} y1={-12 + w(seed, 6)} x2={-10 + w(seed, 7) * 0.3} y2={12 + w(seed, 8)}
        stroke={STROKE_COLOR} strokeWidth={TRANSISTOR_STROKE_WIDTH} strokeLinecap="round" />
      {/* Channel bar */}
      <line x1={w(seed, 9) * 0.3} y1={-12 + w(seed, 10)} x2={w(seed, 11) * 0.3} y2={12 + w(seed, 12)}
        stroke={STROKE_COLOR} strokeWidth={TRANSISTOR_STROKE_WIDTH + 0.5} strokeLinecap="round" />
      {/* Source lead */}
      <line x1={w(seed, 13) * 0.3} y1={-8 + w(seed, 14)} x2={14 + w(seed, 15)} y2={-8 + w(seed, 16)}
        stroke={WIRE_COLOR} strokeWidth={WIRE_STROKE_WIDTH} strokeLinecap="round" />
      <line x1={14 + w(seed, 17)} y1={-8 + w(seed, 18)} x2={14 + w(seed, 19)} y2={-18 + w(seed, 20)}
        stroke={WIRE_COLOR} strokeWidth={WIRE_STROKE_WIDTH} strokeLinecap="round" />
      {/* Drain lead */}
      <line x1={w(seed, 21) * 0.3} y1={8 + w(seed, 22)} x2={14 + w(seed, 23)} y2={8 + w(seed, 24)}
        stroke={WIRE_COLOR} strokeWidth={WIRE_STROKE_WIDTH} strokeLinecap="round" />
      <line x1={14 + w(seed, 25)} y1={8 + w(seed, 26)} x2={14 + w(seed, 27)} y2={18 + w(seed, 28)}
        stroke={WIRE_COLOR} strokeWidth={WIRE_STROKE_WIDTH} strokeLinecap="round" />
      {/* Arrow */}
      <polygon
        points={`${2 + w(seed, 29) * 0.2},${8 + w(seed, 30) * 0.2} ${5 + w(seed, 31) * 0.2},${6 + w(seed, 32) * 0.2} ${5 + w(seed, 33) * 0.2},${10 + w(seed, 34) * 0.2}`}
        fill={STROKE_COLOR} />
    </g>
  );
}

// Simplified transistor for tier 1 (3 lines)
function renderSimplifiedTransistor(pos: TransistorPos): React.ReactNode {
  const { x, y, seed } = pos;
  return (
    <g key={`t-${seed}`} transform={`translate(${x},${y})`}>
      <line x1={-10} y1={-8} x2={-10} y2={8} stroke={STROKE_COLOR} strokeWidth={1.2} strokeLinecap="round" />
      <line x1={-6} y1={-8} x2={-6} y2={8} stroke={STROKE_COLOR} strokeWidth={1.5} strokeLinecap="round" />
      <line x1={-14} y1={0} x2={-10} y2={0} stroke={WIRE_COLOR} strokeWidth={0.8} strokeLinecap="round" />
      <line x1={-6} y1={-5} x2={8} y2={-5} stroke={WIRE_COLOR} strokeWidth={0.8} strokeLinecap="round" />
      <line x1={-6} y1={5} x2={8} y2={5} stroke={WIRE_COLOR} strokeWidth={0.8} strokeLinecap="round" />
    </g>
  );
}

// Tiny cross mark for tier 2
function renderCrossMark(pos: TransistorPos): React.ReactNode {
  const { x, y, seed } = pos;
  return (
    <g key={`t-${seed}`}>
      <line x1={x - 3} y1={y - 3} x2={x + 3} y2={y + 3} stroke={STROKE_COLOR} strokeWidth={0.8} />
      <line x1={x - 3} y1={y + 3} x2={x + 3} y2={y - 3} stroke={STROKE_COLOR} strokeWidth={0.8} />
    </g>
  );
}

// Micro dot for tier 3
function renderDot(pos: TransistorPos): React.ReactNode {
  const { x, y, seed } = pos;
  return (
    <circle key={`t-${seed}`} cx={x} cy={y} r={1.2} fill={STROKE_COLOR} opacity={0.7} />
  );
}

const SchematicCanvas: React.FC<SchematicCanvasProps> = ({ visibleCount }) => {
  const clampedCount = Math.min(Math.max(Math.round(visibleCount), 0), 50000);

  const visiblePositions = useMemo(
    () => FULL_LAYOUT.slice(0, clampedCount),
    [clampedCount]
  );

  const transistorElements = useMemo(() => {
    const elements: React.ReactNode[] = [];
    for (let i = 0; i < visiblePositions.length; i++) {
      const pos = visiblePositions[i];
      if (pos.tier === 0) {
        elements.push(renderDetailedTransistor(pos));
      } else if (pos.tier === 1) {
        elements.push(renderSimplifiedTransistor(pos));
      } else if (pos.tier === 2) {
        elements.push(renderCrossMark(pos));
      } else {
        elements.push(renderDot(pos));
      }
    }
    return elements;
  }, [visiblePositions]);

  const wireElements = useMemo(() => {
    // Cap wires for performance; wires only on first ~2000 transistors
    const wirePositions = visiblePositions.slice(0, Math.min(clampedCount, 2000));
    return renderWires(wirePositions, wirePositions.length);
  }, [visiblePositions, clampedCount]);

  // SVG viewBox covers full schematic spread
  const svgSize = SCHEMATIC_SPREAD;
  const offsetX = CANVAS_WIDTH / 2 - svgSize / 2;
  const offsetY = CANVAS_HEIGHT / 2 - svgSize / 2;

  return (
    <svg
      width={svgSize}
      height={svgSize}
      viewBox={`${offsetX} ${offsetY} ${svgSize} ${svgSize}`}
      style={{
        position: 'absolute',
        left: '50%',
        top: '50%',
        transform: 'translate(-50%, -50%)',
      }}
    >
      {wireElements}
      {transistorElements}
    </svg>
  );
};

export default SchematicCanvas;

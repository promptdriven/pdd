// ============================================================
// SchematicCanvas.tsx – Generates procedural transistor schematic
// that grows denser as the animation zooms out.
// Uses a seeded pseudo-random for deterministic layout.
// ============================================================
import React, { useMemo } from 'react';

interface SchematicCanvasProps {
  /** How many transistors to render (based on current frame) */
  visibleCount: number;
  /** Virtual canvas width */
  canvasWidth: number;
  /** Virtual canvas height */
  canvasHeight: number;
  strokeColor: string;
  wireColor: string;
  strokeWidth: number;
  wireWidth: number;
}

// Simple seeded PRNG (mulberry32)
function seededRandom(seed: number) {
  let s = seed;
  return () => {
    s |= 0;
    s = (s + 0x6d2b79f5) | 0;
    let t = Math.imul(s ^ (s >>> 15), 1 | s);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

interface TransistorData {
  x: number;
  y: number;
  rotation: number;
  wobble1: number;
  wobble2: number;
  wireEndX: number;
  wireEndY: number;
}

function generateTransistors(
  count: number,
  canvasW: number,
  canvasH: number,
): TransistorData[] {
  const rng = seededRandom(42);
  const transistors: TransistorData[] = [];

  // Spiral placement — denser in center, radiating outward
  const centerX = canvasW / 2;
  const centerY = canvasH / 2;

  for (let i = 0; i < count; i++) {
    // Use a golden-ratio spiral distribution
    const angle = i * 2.399963; // golden angle in radians
    const radius = Math.sqrt(i) * 18;
    const x = centerX + Math.cos(angle) * radius + (rng() - 0.5) * 12;
    const y = centerY + Math.sin(angle) * radius + (rng() - 0.5) * 12;
    const rotation = rng() * 360;
    const wobble1 = (rng() - 0.5) * 2;
    const wobble2 = (rng() - 0.5) * 2;

    // Wire to nearby "neighbor"
    const wireAngle = rng() * Math.PI * 2;
    const wireLen = 10 + rng() * 20;
    const wireEndX = x + Math.cos(wireAngle) * wireLen;
    const wireEndY = y + Math.sin(wireAngle) * wireLen;

    transistors.push({ x, y, rotation, wobble1, wobble2, wireEndX, wireEndY });
  }

  return transistors;
}

// MOSFET-style transistor symbol as SVG path (hand-drawn wobble)
function transistorPath(w1: number, w2: number): string {
  // A simplified MOSFET symbol:
  // Vertical gate line, horizontal channel, three terminals
  return [
    `M ${-8 + w1} ${-10 + w2}`, // gate top
    `L ${-8 + w2} ${10 + w1}`, // gate bottom
    `M ${-4 + w1} ${-7}`, // channel top
    `L ${-4 + w2} ${7}`, // channel bottom
    `M ${-4 + w1} ${-7}`, // drain
    `L ${6 + w2} ${-7}`,
    `L ${6 + w1} ${-12}`,
    `M ${-4 + w2} ${0}`, // source center
    `L ${6 + w1} ${0}`,
    `M ${-4 + w1} ${7}`, // source bottom
    `L ${6 + w2} ${7}`,
    `L ${6 + w1} ${12}`,
  ].join(' ');
}

export const SchematicCanvas: React.FC<SchematicCanvasProps> = ({
  visibleCount,
  canvasWidth,
  canvasHeight,
  strokeColor,
  wireColor,
  strokeWidth,
  wireWidth,
}) => {
  // Pre-generate the full layout (deterministic)
  const allTransistors = useMemo(
    () => generateTransistors(Math.min(visibleCount, 6000), canvasWidth, canvasHeight),
    // We cap at 6000 SVG elements for performance; beyond that the density
    // is achieved by the zoom scale making them overlap visually.
    [visibleCount, canvasWidth, canvasHeight],
  );

  const rendered = allTransistors.slice(0, Math.min(visibleCount, 6000));

  return (
    <svg
      width={canvasWidth}
      height={canvasHeight}
      viewBox={`0 0 ${canvasWidth} ${canvasHeight}`}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Connection wires first (behind symbols) */}
      {rendered.map((t, i) => (
        <line
          key={`w${i}`}
          x1={t.x}
          y1={t.y}
          x2={t.wireEndX}
          y2={t.wireEndY}
          stroke={wireColor}
          strokeWidth={wireWidth}
          strokeLinecap="round"
        />
      ))}

      {/* Transistor symbols */}
      {rendered.map((t, i) => (
        <g
          key={`t${i}`}
          transform={`translate(${t.x}, ${t.y}) rotate(${t.rotation})`}
        >
          <path
            d={transistorPath(t.wobble1, t.wobble2)}
            stroke={strokeColor}
            strokeWidth={strokeWidth}
            fill="none"
            strokeLinecap="round"
            strokeLinejoin="round"
          />
        </g>
      ))}
    </svg>
  );
};

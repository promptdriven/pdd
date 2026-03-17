import React, { useMemo } from "react";
import {
  CHIP_COLORS,
  CHIP_OPACITIES,
  GATE_W,
  GATE_H,
  GATE_GAP,
  seededRandom,
  WIDTH,
  HEIGHT,
} from "./constants";

/**
 * A procedurally generated chip layout mosaic.
 * Renders a dense grid of colored rectangles representing gates,
 * metal layers, polysilicon, diffusion, and vias.
 *
 * The zoom prop scales the entire mosaic around the center.
 */

interface GateRect {
  x: number;
  y: number;
  w: number;
  h: number;
  color: string;
  opacity: number;
}

// Gate type distribution weights
const GATE_TYPES: Array<{
  color: string;
  opacity: number;
  weight: number;
}> = [
  { color: CHIP_COLORS.metal1, opacity: CHIP_OPACITIES.metal, weight: 0.3 },
  { color: CHIP_COLORS.metal2, opacity: CHIP_OPACITIES.metal, weight: 0.2 },
  { color: CHIP_COLORS.poly, opacity: CHIP_OPACITIES.poly, weight: 0.25 },
  {
    color: CHIP_COLORS.diffusion,
    opacity: CHIP_OPACITIES.diffusion,
    weight: 0.15,
  },
  { color: CHIP_COLORS.vias, opacity: CHIP_OPACITIES.vias, weight: 0.1 },
];

function pickGateType(rand: number): { color: string; opacity: number } {
  let cumulative = 0;
  for (const gt of GATE_TYPES) {
    cumulative += gt.weight;
    if (rand < cumulative) return { color: gt.color, opacity: gt.opacity };
  }
  return GATE_TYPES[0];
}

export const ChipLayoutMosaic: React.FC<{ zoom: number }> = ({ zoom }) => {
  // Generate gate data deterministically
  const gates = useMemo(() => {
    const rng = seededRandom(42);
    const result: GateRect[] = [];
    const cellW = GATE_W + GATE_GAP;
    const cellH = GATE_H + GATE_GAP;

    // Generate enough gates to fill the screen at any zoom level
    // At zoom=1, we see ~640x360 gates across 1920x1080
    // We generate a larger field so zooming in still has content
    const cols = 800;
    const rows = 500;

    // Offset to center the grid
    const offsetX = (WIDTH - cols * cellW) / 2;
    const offsetY = (HEIGHT - rows * cellH) / 2;

    for (let row = 0; row < rows; row++) {
      for (let col = 0; col < cols; col++) {
        const r = rng();
        const { color, opacity } = pickGateType(r);
        result.push({
          x: offsetX + col * cellW,
          y: offsetY + row * cellH,
          w: GATE_W,
          h: GATE_H,
          color,
          opacity,
        });
      }
    }

    // Add wiring traces (horizontal and vertical lines between gates)
    // These become visible at higher zoom levels
    const wireCount = 2000;
    for (let i = 0; i < wireCount; i++) {
      const r1 = rng();
      const r2 = rng();
      const r3 = rng();
      const isHorizontal = r3 > 0.5;
      const wx = offsetX + r1 * cols * cellW;
      const wy = offsetY + r2 * rows * cellH;
      result.push({
        x: wx,
        y: wy,
        w: isHorizontal ? 8 + r1 * 12 : 0.5,
        h: isHorizontal ? 0.5 : 6 + r2 * 10,
        color: r3 > 0.7 ? CHIP_COLORS.metal1 : CHIP_COLORS.metal2,
        opacity: 0.25,
      });
    }

    return result;
  }, []);

  // Use SVG for efficient rendering of many small rects
  // The zoom is applied as a transform on the SVG group
  const centerX = WIDTH / 2;
  const centerY = HEIGHT / 2;

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <g
        transform={`translate(${centerX}, ${centerY}) scale(${zoom}) translate(${-centerX}, ${-centerY})`}
      >
        {gates.map((g, i) => (
          <rect
            key={i}
            x={g.x}
            y={g.y}
            width={g.w}
            height={g.h}
            fill={g.color}
            opacity={g.opacity}
          />
        ))}
      </g>
    </svg>
  );
};

export default ChipLayoutMosaic;

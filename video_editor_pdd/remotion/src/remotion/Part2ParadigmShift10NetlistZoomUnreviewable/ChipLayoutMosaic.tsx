import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CHIP_COLORS,
  CHIP_OPACITIES,
  GATE_COLS,
  GATE_ROWS,
  GATE_WIDTH,
  GATE_HEIGHT,
  PHASE,
  ZOOM_INITIAL,
  ZOOM_FINAL,
  LABEL_COLOR,
  WIDTH,
  HEIGHT,
} from "./constants";

// Seeded pseudo-random for deterministic gate colors
function seededRandom(seed: number): number {
  const x = Math.sin(seed * 127.1 + seed * 311.7) * 43758.5453;
  return x - Math.floor(x);
}

type GateType = "metal1" | "metal2" | "polysilicon" | "diffusion" | "vias";

interface GateData {
  type: GateType;
  color: string;
  opacity: number;
}

function getGateData(col: number, row: number): GateData {
  const r = seededRandom(col * 1000 + row);
  if (r < 0.3) return { type: "metal1", color: CHIP_COLORS.metal1, opacity: CHIP_OPACITIES.metal1 };
  if (r < 0.55) return { type: "metal2", color: CHIP_COLORS.metal2, opacity: CHIP_OPACITIES.metal2 };
  if (r < 0.75) return { type: "polysilicon", color: CHIP_COLORS.polysilicon, opacity: CHIP_OPACITIES.polysilicon };
  if (r < 0.92) return { type: "diffusion", color: CHIP_COLORS.diffusion, opacity: CHIP_OPACITIES.diffusion };
  return { type: "vias", color: CHIP_COLORS.vias, opacity: CHIP_OPACITIES.vias };
}

// Generate wiring traces between gates
function shouldHaveHWire(col: number, row: number): boolean {
  return seededRandom(col * 2000 + row * 3 + 7) < 0.3;
}

function shouldHaveVWire(col: number, row: number): boolean {
  return seededRandom(col * 3000 + row * 5 + 13) < 0.25;
}

export const ChipLayoutMosaic: React.FC = () => {
  const frame = useCurrentFrame();

  // Compute zoom level
  const zoomProgress = interpolate(
    frame,
    [PHASE.chipStart, PHASE.chipZoomStart, PHASE.chipZoomEnd, PHASE.chipHoldEnd],
    [0, 0, 1, 1],
    { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
  );

  const easedProgress = Easing.bezier(0.42, 0, 0.58, 1)(zoomProgress);
  const scale = interpolate(easedProgress, [0, 1], [ZOOM_INITIAL, ZOOM_FINAL]);

  // Fade-in for "~2.4 billion gates" label
  const labelOpacity = interpolate(
    frame,
    [30, 45],
    [0, 0.4],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Morph-out opacity (fades during morph transition)
  const morphOutOpacity = interpolate(
    frame,
    [PHASE.morphStart, PHASE.morphEnd],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Pre-compute visible gate range based on zoom
  const visibleGates = useMemo(() => {
    const gates: Array<{
      col: number;
      row: number;
      x: number;
      y: number;
      w: number;
      h: number;
      color: string;
      opacity: number;
      hWire: boolean;
      vWire: boolean;
    }> = [];

    // Calculate the viewport in gate coordinates
    const centerCol = GATE_COLS / 2;
    const centerRow = GATE_ROWS / 2;
    const viewportW = WIDTH / (GATE_WIDTH * scale);
    const viewportH = HEIGHT / (GATE_HEIGHT * scale);
    const startCol = Math.max(0, Math.floor(centerCol - viewportW / 2) - 1);
    const endCol = Math.min(GATE_COLS, Math.ceil(centerCol + viewportW / 2) + 1);
    const startRow = Math.max(0, Math.floor(centerRow - viewportH / 2) - 1);
    const endRow = Math.min(GATE_ROWS, Math.ceil(centerRow + viewportH / 2) + 1);

    for (let row = startRow; row < endRow; row++) {
      for (let col = startCol; col < endCol; col++) {
        const gate = getGateData(col, row);
        gates.push({
          col,
          row,
          x: col * GATE_WIDTH,
          y: row * GATE_HEIGHT,
          w: gate.type === "vias" ? GATE_WIDTH * 0.4 : GATE_WIDTH * 0.85,
          h: gate.type === "vias" ? GATE_HEIGHT * 0.4 : GATE_HEIGHT * 0.85,
          color: gate.color,
          opacity: gate.opacity,
          hWire: shouldHaveHWire(col, row),
          vWire: shouldHaveVWire(col, row),
        });
      }
    }
    return gates;
  }, [scale]);

  // Show wiring at higher zoom levels
  const showWires = scale >= 3;
  const wireOpacity = interpolate(scale, [3, 5], [0, 0.3], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // The total mosaic dimensions
  const mosaicWidth = GATE_COLS * GATE_WIDTH;
  const mosaicHeight = GATE_ROWS * GATE_HEIGHT;

  return (
    <AbsoluteFill style={{ opacity: morphOutOpacity }}>
      {/* Zooming container */}
      <div
        style={{
          position: "absolute",
          width: WIDTH,
          height: HEIGHT,
          overflow: "hidden",
        }}
      >
        <div
          style={{
            position: "absolute",
            left: WIDTH / 2,
            top: HEIGHT / 2,
            transform: `scale(${scale})`,
            transformOrigin: "0 0",
          }}
        >
          <div
            style={{
              position: "absolute",
              left: -mosaicWidth / 2,
              top: -mosaicHeight / 2,
              width: mosaicWidth,
              height: mosaicHeight,
            }}
          >
            {/* Render gates via SVG for performance */}
            <svg
              width={mosaicWidth}
              height={mosaicHeight}
              viewBox={`0 0 ${mosaicWidth} ${mosaicHeight}`}
              style={{ position: "absolute", left: 0, top: 0 }}
            >
              {visibleGates.map((g) => (
                <React.Fragment key={`${g.col}-${g.row}`}>
                  <rect
                    x={g.x + (GATE_WIDTH - g.w) / 2}
                    y={g.y + (GATE_HEIGHT - g.h) / 2}
                    width={g.w}
                    height={g.h}
                    fill={g.color}
                    opacity={g.opacity}
                    rx={g.w < GATE_WIDTH * 0.5 ? g.w / 2 : 1}
                  />
                  {showWires && g.hWire && (
                    <line
                      x1={g.x + GATE_WIDTH}
                      y1={g.y + GATE_HEIGHT / 2}
                      x2={g.x + GATE_WIDTH * 2}
                      y2={g.y + GATE_HEIGHT / 2}
                      stroke={CHIP_COLORS.metal1}
                      strokeWidth={0.5}
                      opacity={wireOpacity}
                    />
                  )}
                  {showWires && g.vWire && (
                    <line
                      x1={g.x + GATE_WIDTH / 2}
                      y1={g.y + GATE_HEIGHT}
                      x2={g.x + GATE_WIDTH / 2}
                      y2={g.y + GATE_HEIGHT * 2}
                      stroke={CHIP_COLORS.metal2}
                      strokeWidth={0.5}
                      opacity={wireOpacity}
                    />
                  )}
                </React.Fragment>
              ))}
            </svg>
          </div>
        </div>
      </div>

      {/* Gate count label */}
      {labelOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            right: 170,
            top: 50,
            fontFamily: "JetBrains Mono, monospace",
            fontSize: 14,
            color: LABEL_COLOR,
            opacity: labelOpacity,
            whiteSpace: "nowrap",
          }}
        >
          ~2.4 billion gates
        </div>
      )}
    </AbsoluteFill>
  );
};

export default ChipLayoutMosaic;

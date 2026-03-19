import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { GATE_COLOR, GATE_OPACITY, WIRE_COLOR, WIRE_OPACITY } from "./constants";

// Standard logic gate SVG paths (relative to gate center)
const AND_GATE = "M -15 -12 L -15 12 L 0 12 Q 15 12 15 0 Q 15 -12 0 -12 Z";
const OR_GATE = "M -15 -12 Q -5 0 -15 12 Q 5 12 15 0 Q 5 -12 -15 -12 Z";
const NOT_GATE = "M -12 -10 L -12 10 L 12 0 Z";
const NOT_CIRCLE = { cx: 14, cy: 0, r: 3 };

// Predefined netlist layouts (gates + wires)
interface GateLayout {
  gates: Array<{
    type: "and" | "or" | "not";
    x: number;
    y: number;
    scale?: number;
  }>;
  wires: Array<{
    x1: number;
    y1: number;
    x2: number;
    y2: number;
  }>;
}

const NETLIST_A: GateLayout = {
  // 6 gates, horizontal compact
  gates: [
    { type: "not", x: -140, y: -60 },
    { type: "and", x: -60, y: -40 },
    { type: "and", x: -60, y: 40 },
    { type: "or", x: 40, y: 0 },
    { type: "not", x: 120, y: -60 },
    { type: "and", x: 120, y: 40 },
  ],
  wires: [
    { x1: -180, y1: -60, x2: -155, y2: -60 },
    { x1: -125, y1: -60, x2: -78, y2: -48 },
    { x1: -180, y1: -30, x2: -78, y2: -32 },
    { x1: -180, y1: 30, x2: -78, y2: 32 },
    { x1: -180, y1: 50, x2: -78, y2: 48 },
    { x1: -42, y1: -40, x2: 22, y2: -8 },
    { x1: -42, y1: 40, x2: 22, y2: 8 },
    { x1: 58, y1: 0, x2: 180, y2: 0 },
    { x1: 100, y1: -60, x2: 105, y2: -60 },
    { x1: 138, y1: -60, x2: 180, y2: -60 },
    { x1: 100, y1: 30, x2: 102, y2: 32 },
    { x1: 100, y1: 50, x2: 102, y2: 48 },
    { x1: 138, y1: 40, x2: 180, y2: 40 },
  ],
};

const NETLIST_B: GateLayout = {
  // 8 gates, vertical layout, longer wires
  gates: [
    { type: "not", x: -120, y: -80 },
    { type: "not", x: -120, y: -20 },
    { type: "and", x: -30, y: -80 },
    { type: "and", x: -30, y: -20 },
    { type: "or", x: -30, y: 40 },
    { type: "and", x: 60, y: -50 },
    { type: "or", x: 60, y: 30 },
    { type: "and", x: 140, y: -10 },
  ],
  wires: [
    { x1: -170, y1: -80, x2: -135, y2: -80 },
    { x1: -170, y1: -20, x2: -135, y2: -20 },
    { x1: -105, y1: -80, x2: -48, y2: -88 },
    { x1: -170, y1: -60, x2: -48, y2: -72 },
    { x1: -105, y1: -20, x2: -48, y2: -28 },
    { x1: -170, y1: 0, x2: -48, y2: -12 },
    { x1: -170, y1: 30, x2: -48, y2: 32 },
    { x1: -170, y1: 50, x2: -48, y2: 48 },
    { x1: -12, y1: -80, x2: 42, y2: -58 },
    { x1: -12, y1: -20, x2: 42, y2: -42 },
    { x1: -12, y1: 40, x2: 42, y2: 22 },
    { x1: -12, y1: 40, x2: 42, y2: 38 },
    { x1: 78, y1: -50, x2: 122, y2: -18 },
    { x1: 78, y1: 30, x2: 122, y2: -2 },
    { x1: 158, y1: -10, x2: 180, y2: -10 },
  ],
};

const NETLIST_C: GateLayout = {
  // 5 gates, mixed optimized
  gates: [
    { type: "not", x: -100, y: -40 },
    { type: "or", x: 0, y: -40 },
    { type: "and", x: 0, y: 40 },
    { type: "or", x: 100, y: 0 },
    { type: "not", x: 100, y: 60 },
  ],
  wires: [
    { x1: -160, y1: -40, x2: -115, y2: -40 },
    { x1: -85, y1: -40, x2: -18, y2: -48 },
    { x1: -160, y1: -20, x2: -18, y2: -32 },
    { x1: -160, y1: 30, x2: -18, y2: 32 },
    { x1: -160, y1: 50, x2: -18, y2: 48 },
    { x1: 18, y1: -40, x2: 82, y2: -8 },
    { x1: 18, y1: 40, x2: 82, y2: 8 },
    { x1: 118, y1: 0, x2: 160, y2: 0 },
    { x1: 80, y1: 60, x2: 85, y2: 60 },
    { x1: 117, y1: 60, x2: 160, y2: 60 },
  ],
};

const LAYOUTS = [NETLIST_A, NETLIST_B, NETLIST_C];
const LAYOUT_BY_NAME = {
  horizontal: NETLIST_A,
  horizontal_compact: NETLIST_A,
  vertical_long: NETLIST_B,
  mixed_optimized: NETLIST_C,
} as const;

const GATE_PATHS: Record<string, string> = {
  and: AND_GATE,
  or: OR_GATE,
  not: NOT_GATE,
};

interface GateNetlistProps {
  x: number;
  y: number;
  width: number;
  height: number;
  gateCount?: number;
  layout?: "horizontal" | "horizontal_compact" | "vertical_long" | "mixed_optimized";
  layoutIndex?: number;
  startFrame?: number;
  drawStart?: number;
  drawDuration: number;
}

export const GateNetlist: React.FC<GateNetlistProps> = ({
  x,
  y,
  width,
  height,
  gateCount: _gateCount,
  layout,
  layoutIndex,
  startFrame,
  drawStart,
  drawDuration,
}) => {
  const frame = useCurrentFrame();
  const resolvedLayout = typeof layoutIndex === "number"
    ? LAYOUTS[((layoutIndex % LAYOUTS.length) + LAYOUTS.length) % LAYOUTS.length]
    : layout
      ? LAYOUT_BY_NAME[layout]
      : NETLIST_A;
  const resolvedDrawStart = typeof startFrame === "number" ? startFrame : drawStart ?? 0;

  const drawProgress = interpolate(
    frame,
    [resolvedDrawStart, resolvedDrawStart + drawDuration],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (frame < resolvedDrawStart) return null;

  const totalElements = resolvedLayout.gates.length + resolvedLayout.wires.length;

  return (
    <svg
      width={width}
      height={height}
      viewBox="-200 -100 400 250"
      style={{
        position: "absolute",
        left: x - width / 2,
        top: y - height / 2,
        pointerEvents: "none",
        overflow: "visible",
      }}
    >
      {/* Wires (draw first, behind gates) */}
      {resolvedLayout.wires.map((wire, i) => {
        const wireIdx = resolvedLayout.gates.length + i;
        const wireProgress = interpolate(
          drawProgress,
          [wireIdx / totalElements, Math.min((wireIdx + 1) / totalElements, 1)],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
        );
        const lineLength = Math.sqrt(
          (wire.x2 - wire.x1) ** 2 + (wire.y2 - wire.y1) ** 2
        );
        return (
          <line
            key={`wire-${i}`}
            x1={wire.x1}
            y1={wire.y1}
            x2={wire.x2}
            y2={wire.y2}
            stroke={WIRE_COLOR}
            strokeWidth={1}
            opacity={WIRE_OPACITY * wireProgress}
            strokeDasharray={lineLength}
            strokeDashoffset={lineLength * (1 - wireProgress)}
          />
        );
      })}

      {/* Gates */}
      {resolvedLayout.gates.map((gate, i) => {
        const gateProgress = interpolate(
          drawProgress,
          [i / totalElements, Math.min((i + 1) / totalElements, 1)],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
        );
        return (
          <g
            key={`gate-${i}`}
            transform={`translate(${gate.x}, ${gate.y}) scale(${gate.scale || 1})`}
            opacity={GATE_OPACITY * gateProgress}
          >
            <path
              d={GATE_PATHS[gate.type]}
              fill="none"
              stroke={GATE_COLOR}
              strokeWidth={1.5}
              strokeLinejoin="round"
            />
            {gate.type === "not" && (
              <circle
                cx={NOT_CIRCLE.cx}
                cy={NOT_CIRCLE.cy}
                r={NOT_CIRCLE.r}
                fill="none"
                stroke={GATE_COLOR}
                strokeWidth={1.5}
              />
            )}
          </g>
        );
      })}
    </svg>
  );
};

export default GateNetlist;

import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  WIRE_COLOR,
  GATE_COLOR,
  LABEL_COLOR,
  COLUMN_WIDTH,
  COLUMN_HEIGHT,
  COLUMN_Y,
  NETLIST_GEN_DURATION,
} from './constants';

type Topology = 'dense-left' | 'tree-branch' | 'linear-chain';

interface GateNode {
  x: number;
  y: number;
  width: number;
  height: number;
  label: string;
}

interface Wire {
  x1: number;
  y1: number;
  x2: number;
  y2: number;
}

interface NetlistColumnProps {
  topology: Topology;
  colX: number;
  startFrame: number;
  label: string;
}

/**
 * Generate different gate layouts depending on topology.
 * All coordinates are relative to the column's local space (0,0)-(COLUMN_WIDTH, COLUMN_HEIGHT).
 */
function generateGates(topology: Topology): { gates: GateNode[]; wires: Wire[] } {
  const gw = 60;
  const gh = 30;

  if (topology === 'dense-left') {
    // Dense left-heavy layout: many gates clustered on the left, funnel right
    const gates: GateNode[] = [
      { x: 30, y: 30, width: gw, height: gh, label: 'AND' },
      { x: 30, y: 90, width: gw, height: gh, label: 'OR' },
      { x: 30, y: 150, width: gw, height: gh, label: 'AND' },
      { x: 30, y: 210, width: gw, height: gh, label: 'XOR' },
      { x: 30, y: 270, width: gw, height: gh, label: 'NOT' },
      { x: 30, y: 330, width: gw, height: gh, label: 'AND' },
      { x: 140, y: 60, width: gw, height: gh, label: 'NAND' },
      { x: 140, y: 150, width: gw, height: gh, label: 'OR' },
      { x: 140, y: 240, width: gw, height: gh, label: 'NOR' },
      { x: 140, y: 330, width: gw, height: gh, label: 'AND' },
      { x: 250, y: 105, width: gw, height: gh, label: 'MUX' },
      { x: 250, y: 285, width: gw, height: gh, label: 'MUX' },
      { x: 320, y: 195, width: gw + 10, height: gh, label: 'BUF' },
    ];
    const wires: Wire[] = [
      { x1: 90, y1: 45, x2: 140, y2: 75 },
      { x1: 90, y1: 105, x2: 140, y2: 75 },
      { x1: 90, y1: 165, x2: 140, y2: 165 },
      { x1: 90, y1: 225, x2: 140, y2: 255 },
      { x1: 90, y1: 285, x2: 140, y2: 255 },
      { x1: 90, y1: 345, x2: 140, y2: 345 },
      { x1: 200, y1: 75, x2: 250, y2: 120 },
      { x1: 200, y1: 165, x2: 250, y2: 120 },
      { x1: 200, y1: 255, x2: 250, y2: 300 },
      { x1: 200, y1: 345, x2: 250, y2: 300 },
      { x1: 310, y1: 120, x2: 320, y2: 210 },
      { x1: 310, y1: 300, x2: 320, y2: 210 },
    ];
    return { gates, wires };
  }

  if (topology === 'tree-branch') {
    // Binary tree branching from top
    const gates: GateNode[] = [
      { x: 170, y: 20, width: gw, height: gh, label: 'AND' },
      { x: 80, y: 100, width: gw, height: gh, label: 'OR' },
      { x: 260, y: 100, width: gw, height: gh, label: 'NAND' },
      { x: 30, y: 190, width: gw, height: gh, label: 'XOR' },
      { x: 130, y: 190, width: gw, height: gh, label: 'NOT' },
      { x: 220, y: 190, width: gw, height: gh, label: 'AND' },
      { x: 310, y: 190, width: gw, height: gh, label: 'NOR' },
      { x: 30, y: 280, width: gw, height: gh, label: 'BUF' },
      { x: 130, y: 280, width: gw, height: gh, label: 'AND' },
      { x: 220, y: 280, width: gw, height: gh, label: 'OR' },
      { x: 310, y: 280, width: gw, height: gh, label: 'BUF' },
      { x: 170, y: 370, width: gw, height: gh, label: 'MUX' },
    ];
    const wires: Wire[] = [
      { x1: 200, y1: 50, x2: 110, y2: 100 },
      { x1: 200, y1: 50, x2: 290, y2: 100 },
      { x1: 110, y1: 130, x2: 60, y2: 190 },
      { x1: 110, y1: 130, x2: 160, y2: 190 },
      { x1: 290, y1: 130, x2: 250, y2: 190 },
      { x1: 290, y1: 130, x2: 340, y2: 190 },
      { x1: 60, y1: 220, x2: 60, y2: 280 },
      { x1: 160, y1: 220, x2: 160, y2: 280 },
      { x1: 250, y1: 220, x2: 250, y2: 280 },
      { x1: 340, y1: 220, x2: 340, y2: 280 },
      { x1: 60, y1: 310, x2: 200, y2: 370 },
      { x1: 160, y1: 310, x2: 200, y2: 370 },
      { x1: 250, y1: 310, x2: 200, y2: 370 },
      { x1: 340, y1: 310, x2: 200, y2: 370 },
    ];
    return { gates, wires };
  }

  // linear-chain: top-to-bottom sequential chain
  const gates: GateNode[] = [
    { x: 50, y: 20, width: gw, height: gh, label: 'AND' },
    { x: 170, y: 20, width: gw, height: gh, label: 'OR' },
    { x: 290, y: 20, width: gw, height: gh, label: 'NOT' },
    { x: 120, y: 90, width: gw, height: gh, label: 'NAND' },
    { x: 240, y: 90, width: gw, height: gh, label: 'XOR' },
    { x: 180, y: 165, width: gw, height: gh, label: 'NOR' },
    { x: 180, y: 240, width: gw, height: gh, label: 'AND' },
    { x: 180, y: 315, width: gw, height: gh, label: 'MUX' },
    { x: 100, y: 315, width: gw, height: gh, label: 'BUF' },
    { x: 260, y: 315, width: gw, height: gh, label: 'BUF' },
    { x: 180, y: 390, width: gw, height: gh, label: 'OR' },
  ];
  const wires: Wire[] = [
    { x1: 80, y1: 50, x2: 150, y2: 90 },
    { x1: 200, y1: 50, x2: 150, y2: 90 },
    { x1: 200, y1: 50, x2: 270, y2: 90 },
    { x1: 320, y1: 50, x2: 270, y2: 90 },
    { x1: 150, y1: 120, x2: 210, y2: 165 },
    { x1: 270, y1: 120, x2: 210, y2: 165 },
    { x1: 210, y1: 195, x2: 210, y2: 240 },
    { x1: 210, y1: 270, x2: 210, y2: 315 },
    { x1: 210, y1: 270, x2: 130, y2: 315 },
    { x1: 210, y1: 270, x2: 290, y2: 315 },
    { x1: 130, y1: 345, x2: 210, y2: 390 },
    { x1: 210, y1: 345, x2: 210, y2: 390 },
    { x1: 290, y1: 345, x2: 210, y2: 390 },
  ];
  return { gates, wires };
}

const NetlistColumn: React.FC<NetlistColumnProps> = ({
  topology,
  colX,
  startFrame,
  label,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;
  const { gates, wires } = React.useMemo(() => generateGates(topology), [topology]);

  // Label appears instantly at start
  const labelOpacity = interpolate(localFrame, [0, 10], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Overall generation progress (0→1) over NETLIST_GEN_DURATION
  const genProgress = interpolate(localFrame, [0, NETLIST_GEN_DURATION], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  if (localFrame < 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: colX - COLUMN_WIDTH / 2,
        top: COLUMN_Y,
        width: COLUMN_WIDTH,
        height: COLUMN_HEIGHT,
      }}
    >
      {/* Run label */}
      <div
        style={{
          position: 'absolute',
          top: -30,
          left: 0,
          width: COLUMN_WIDTH,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 400,
          color: LABEL_COLOR,
          opacity: labelOpacity,
        }}
      >
        {label}
      </div>

      {/* SVG for gates + wires */}
      <svg
        width={COLUMN_WIDTH}
        height={COLUMN_HEIGHT}
        viewBox={`0 0 ${COLUMN_WIDTH} ${COLUMN_HEIGHT}`}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {/* Border */}
        <rect
          x={0}
          y={0}
          width={COLUMN_WIDTH}
          height={COLUMN_HEIGHT}
          fill="none"
          stroke={LABEL_COLOR}
          strokeWidth={1}
          opacity={0.2}
          rx={8}
        />

        {/* Wires */}
        {wires.map((w, i) => {
          const wireThreshold = (i + 1) / (wires.length + gates.length);
          const wireStart = Math.max(0, wireThreshold - 0.08);
          const wireEnd = Math.max(wireStart + 0.001, wireThreshold);
          const wireOpacity = interpolate(
            genProgress,
            [wireStart, wireEnd],
            [0, 0.8],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
          );
          return (
            <line
              key={`w-${i}`}
              x1={w.x1}
              y1={w.y1}
              x2={w.x2}
              y2={w.y2}
              stroke={WIRE_COLOR}
              strokeWidth={1.5}
              opacity={wireOpacity}
            />
          );
        })}

        {/* Gates */}
        {gates.map((g, i) => {
          const gateThreshold = (i + 1) / (gates.length + wires.length);
          const gateStart = Math.max(0, gateThreshold - 0.06);
          const gateEnd = Math.max(gateStart + 0.001, gateThreshold);
          const gateOpacity = interpolate(
            genProgress,
            [gateStart, gateEnd],
            [0, 1],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
          );
          const gateScale = interpolate(
            genProgress,
            [gateStart, gateEnd],
            [0.5, 1],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
          );
          return (
            <g
              key={`g-${i}`}
              transform={`translate(${g.x + g.width / 2}, ${g.y + g.height / 2}) scale(${gateScale}) translate(${-(g.x + g.width / 2)}, ${-(g.y + g.height / 2)})`}
              opacity={gateOpacity}
            >
              <rect
                x={g.x}
                y={g.y}
                width={g.width}
                height={g.height}
                fill={GATE_COLOR}
                rx={4}
                opacity={0.85}
              />
              <text
                x={g.x + g.width / 2}
                y={g.y + g.height / 2 + 4}
                textAnchor="middle"
                fill="#FFFFFF"
                fontSize={11}
                fontFamily="JetBrains Mono, monospace"
                fontWeight={600}
              >
                {g.label}
              </text>
            </g>
          );
        })}

        {/* Input pins (top) */}
        {[80, 160, 240, 320].map((px, i) => {
          const pinOpacity = interpolate(genProgress, [0, 0.15], [0, 0.6], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          });
          return (
            <g key={`pin-in-${i}`} opacity={pinOpacity}>
              <circle cx={px} cy={8} r={4} fill={WIRE_COLOR} />
              <line x1={px} y1={12} x2={px} y2={25} stroke={WIRE_COLOR} strokeWidth={1} opacity={0.5} />
            </g>
          );
        })}

        {/* Output pins (bottom) */}
        {[160, 240].map((px, i) => {
          const pinOpacity = interpolate(genProgress, [0.85, 1], [0, 0.6], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          });
          return (
            <g key={`pin-out-${i}`} opacity={pinOpacity}>
              <line
                x1={px}
                y1={COLUMN_HEIGHT - 50}
                x2={px}
                y2={COLUMN_HEIGHT - 20}
                stroke={WIRE_COLOR}
                strokeWidth={1}
                opacity={0.5}
              />
              <polygon
                points={`${px - 5},${COLUMN_HEIGHT - 20} ${px + 5},${COLUMN_HEIGHT - 20} ${px},${COLUMN_HEIGHT - 12}`}
                fill={WIRE_COLOR}
              />
            </g>
          );
        })}
      </svg>
    </div>
  );
};

export default NetlistColumn;

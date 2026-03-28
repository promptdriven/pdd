import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import {
  GATE_COLOR,
  GATE_STREAM_START,
  CANVAS_WIDTH,
} from './constants';

interface GateSymbol {
  type: 'and' | 'or' | 'not' | 'nand' | 'xor';
  yOffset: number;
  speed: number;
  startDelay: number;
  size: number;
}

/**
 * Renders a continuous stream of logic gate symbols flowing rightward.
 * Appears from GATE_STREAM_START onward.
 */
export const GateStream: React.FC = () => {
  const frame = useCurrentFrame();
  const localFrame = Math.max(0, frame - GATE_STREAM_START);

  // Generate deterministic gate symbols
  const gates = useMemo<GateSymbol[]>(() => {
    const items: GateSymbol[] = [];
    const types: GateSymbol['type'][] = ['and', 'or', 'not', 'nand', 'xor'];
    const seed = (i: number) => {
      const s = Math.sin(i * 127.1 + 311.7) * 43758.5453;
      return s - Math.floor(s);
    };

    for (let i = 0; i < 30; i++) {
      items.push({
        type: types[Math.floor(seed(i * 7) * types.length)],
        yOffset: (seed(i * 13) - 0.5) * 80,
        speed: 1.5 + seed(i * 17) * 2,
        startDelay: i * 5,
        size: 16 + seed(i * 23) * 10,
      });
    }
    return items;
  }, []);

  if (frame < GATE_STREAM_START) return null;

  // Starting x position for gate stream (right of chip output)
  const streamStartX = 1140;
  const streamY = 580;

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: CANVAS_WIDTH,
        height: 1080,
        overflow: 'hidden',
        pointerEvents: 'none',
      }}
    >
      <svg width={CANVAS_WIDTH} height={1080}>
        {gates.map((gate, i) => {
          const elapsed = localFrame - gate.startDelay;
          if (elapsed < 0) return null;

          const x = streamStartX + elapsed * gate.speed;
          if (x > CANVAS_WIDTH + 40) return null;

          const y = streamY + gate.yOffset;
          const entryOpacity = interpolate(
            elapsed,
            [0, 10],
            [0, 0.85],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
          );

          return (
            <g key={`gate-${i}`} transform={`translate(${x}, ${y})`} opacity={entryOpacity}>
              {renderGateShape(gate.type, gate.size)}
            </g>
          );
        })}

        {/* Connecting wire lines between gates */}
        {localFrame > 15 && (
          <line
            x1={streamStartX}
            y1={streamY}
            x2={Math.min(streamStartX + localFrame * 3, CANVAS_WIDTH)}
            y2={streamY}
            stroke={GATE_COLOR}
            strokeWidth={1.5}
            opacity={0.3}
          />
        )}
      </svg>
    </div>
  );
};

function renderGateShape(type: string, size: number): React.ReactNode {
  const s = size;
  const hs = s / 2;

  switch (type) {
    case 'and':
      // D-shape AND gate
      return (
        <path
          d={`M ${-hs} ${-hs} L ${0} ${-hs} A ${hs} ${hs} 0 0 1 ${0} ${hs} L ${-hs} ${hs} Z`}
          fill="none"
          stroke={GATE_COLOR}
          strokeWidth={1.5}
        />
      );
    case 'or':
      // Curved OR gate
      return (
        <path
          d={`M ${-hs} ${-hs} Q ${0} ${-hs * 0.5} ${hs} ${0} Q ${0} ${hs * 0.5} ${-hs} ${hs} Q ${-hs * 0.3} ${0} ${-hs} ${-hs}`}
          fill="none"
          stroke={GATE_COLOR}
          strokeWidth={1.5}
        />
      );
    case 'not':
      // Triangle with circle (inverter)
      return (
        <>
          <polygon
            points={`${-hs},${-hs} ${hs * 0.6},${0} ${-hs},${hs}`}
            fill="none"
            stroke={GATE_COLOR}
            strokeWidth={1.5}
          />
          <circle
            cx={hs * 0.8}
            cy={0}
            r={hs * 0.2}
            fill="none"
            stroke={GATE_COLOR}
            strokeWidth={1.5}
          />
        </>
      );
    case 'nand':
      // AND shape with bubble
      return (
        <>
          <path
            d={`M ${-hs} ${-hs} L ${0} ${-hs} A ${hs} ${hs} 0 0 1 ${0} ${hs} L ${-hs} ${hs} Z`}
            fill="none"
            stroke={GATE_COLOR}
            strokeWidth={1.5}
          />
          <circle
            cx={hs * 0.3}
            cy={0}
            r={hs * 0.2}
            fill="none"
            stroke={GATE_COLOR}
            strokeWidth={1.5}
          />
        </>
      );
    case 'xor':
      // OR shape with extra curve
      return (
        <>
          <path
            d={`M ${-hs} ${-hs} Q ${0} ${-hs * 0.5} ${hs} ${0} Q ${0} ${hs * 0.5} ${-hs} ${hs} Q ${-hs * 0.3} ${0} ${-hs} ${-hs}`}
            fill="none"
            stroke={GATE_COLOR}
            strokeWidth={1.5}
          />
          <path
            d={`M ${-hs * 1.2} ${-hs} Q ${-hs * 0.5} ${0} ${-hs * 1.2} ${hs}`}
            fill="none"
            stroke={GATE_COLOR}
            strokeWidth={1.5}
          />
        </>
      );
    default:
      return null;
  }
}

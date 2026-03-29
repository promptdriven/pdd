import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

/**
 * ChipLayout — renders a dense grid of tiny gate rectangles with wire routing.
 * Supports animated zoom to create the fractal-density effect.
 */

const GATE_COLORS = ['#4A90D9', '#5AAA6E', '#D9944A'] as const;
const GATE_OPACITY = 0.6;
const WIRE_COLOR = '#64748B';
const WIRE_OPACITY = 0.3;

// Seeded pseudo-random for deterministic gate layout
function seededRandom(seed: number): () => number {
  let s = seed;
  return () => {
    s = (s * 16807 + 0) % 2147483647;
    return (s - 1) / 2147483646;
  };
}

interface Gate {
  x: number;
  y: number;
  w: number;
  h: number;
  color: string;
}

interface Wire {
  x1: number;
  y1: number;
  x2: number;
  y2: number;
}

function generateGateGrid(
  cols: number,
  rows: number,
  cellW: number,
  cellH: number,
  offsetX: number,
  offsetY: number,
  seed: number
): { gates: Gate[]; wires: Wire[] } {
  const rand = seededRandom(seed);
  const gates: Gate[] = [];
  const wires: Wire[] = [];

  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const x = offsetX + c * cellW + rand() * (cellW * 0.3);
      const y = offsetY + r * cellH + rand() * (cellH * 0.3);
      const gateW = cellW * 0.5 + rand() * cellW * 0.2;
      const gateH = cellH * 0.3 + rand() * cellH * 0.2;
      const color = GATE_COLORS[Math.floor(rand() * GATE_COLORS.length)];
      gates.push({ x, y, w: gateW, h: gateH, color });

      // Horizontal wire to next gate
      if (c < cols - 1) {
        wires.push({
          x1: x + gateW,
          y1: y + gateH / 2,
          x2: offsetX + (c + 1) * cellW,
          y2: y + gateH / 2,
        });
      }
      // Occasional vertical wire
      if (r < rows - 1 && rand() > 0.6) {
        wires.push({
          x1: x + gateW / 2,
          y1: y + gateH,
          x2: x + gateW / 2,
          y2: offsetY + (r + 1) * cellH,
        });
      }
    }
  }

  return { gates, wires };
}

export const ChipLayout: React.FC<{
  zoomStartFrame: number;
  zoomEndFrame: number;
}> = ({ zoomStartFrame, zoomEndFrame }) => {
  const frame = useCurrentFrame();

  const scale = interpolate(frame, [zoomStartFrame, zoomEndFrame], [1, 8], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });

  // Generate multiple detail layers for fractal effect
  const layer1 = useMemo(
    () => generateGateGrid(96, 54, 20, 20, 0, 0, 42),
    []
  );
  const layer2 = useMemo(
    () => generateGateGrid(192, 108, 10, 10, 0, 0, 137),
    []
  );
  const layer3 = useMemo(
    () => generateGateGrid(384, 216, 5, 5, 0, 0, 271),
    []
  );

  // As we zoom in, show finer detail layers
  const layer2Opacity = interpolate(scale, [1.5, 3], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });
  const layer3Opacity = interpolate(scale, [4, 6], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const translateX = interpolate(frame, [zoomStartFrame, zoomEndFrame], [0, -960 * 3], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });
  const translateY = interpolate(frame, [zoomStartFrame, zoomEndFrame], [0, -540 * 3], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
        overflow: 'hidden',
      }}
    >
      <div
        style={{
          transform: `scale(${scale}) translate(${translateX / scale}px, ${translateY / scale}px)`,
          transformOrigin: 'center center',
          width: 1920,
          height: 1080,
          position: 'absolute',
        }}
      >
        {/* Layer 1: Coarse gates */}
        <svg
          width={1920}
          height={1080}
          viewBox="0 0 1920 1080"
          style={{ position: 'absolute', top: 0, left: 0 }}
        >
          {layer1.wires.map((w, i) => (
            <line
              key={`w1-${i}`}
              x1={w.x1}
              y1={w.y1}
              x2={w.x2}
              y2={w.y2}
              stroke={WIRE_COLOR}
              strokeOpacity={WIRE_OPACITY}
              strokeWidth={0.5}
            />
          ))}
          {layer1.gates.map((g, i) => (
            <rect
              key={`g1-${i}`}
              x={g.x}
              y={g.y}
              width={g.w}
              height={g.h}
              fill={g.color}
              opacity={GATE_OPACITY}
            />
          ))}
        </svg>

        {/* Layer 2: Medium detail */}
        {layer2Opacity > 0 && (
          <svg
            width={1920}
            height={1080}
            viewBox="0 0 1920 1080"
            style={{
              position: 'absolute',
              top: 0,
              left: 0,
              opacity: layer2Opacity,
            }}
          >
            {layer2.wires.map((w, i) => (
              <line
                key={`w2-${i}`}
                x1={w.x1}
                y1={w.y1}
                x2={w.x2}
                y2={w.y2}
                stroke={WIRE_COLOR}
                strokeOpacity={WIRE_OPACITY}
                strokeWidth={0.3}
              />
            ))}
            {layer2.gates.map((g, i) => (
              <rect
                key={`g2-${i}`}
                x={g.x}
                y={g.y}
                width={g.w}
                height={g.h}
                fill={g.color}
                opacity={GATE_OPACITY * 0.8}
              />
            ))}
          </svg>
        )}

        {/* Layer 3: Fine detail (fractal) */}
        {layer3Opacity > 0 && (
          <svg
            width={1920}
            height={1080}
            viewBox="0 0 1920 1080"
            style={{
              position: 'absolute',
              top: 0,
              left: 0,
              opacity: layer3Opacity,
            }}
          >
            {layer3.wires.map((w, i) => (
              <line
                key={`w3-${i}`}
                x1={w.x1}
                y1={w.y1}
                x2={w.x2}
                y2={w.y2}
                stroke={WIRE_COLOR}
                strokeOpacity={WIRE_OPACITY}
                strokeWidth={0.2}
              />
            ))}
            {layer3.gates.map((g, i) => (
              <rect
                key={`g3-${i}`}
                x={g.x}
                y={g.y}
                width={g.w}
                height={g.h}
                fill={g.color}
                opacity={GATE_OPACITY * 0.6}
              />
            ))}
          </svg>
        )}
      </div>
    </div>
  );
};

export default ChipLayout;

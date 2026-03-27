// ChipLayout.tsx — Dense gate grid with fractal zoom
import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

const GATE_COLORS = ['#4A90D9', '#5AAA6E', '#D9944A'] as const;
const GATE_OPACITY = 0.6;
const WIRE_COLOR = '#64748B';
const WIRE_OPACITY = 0.3;
const LABEL_FONT = 'Inter, sans-serif';
const LABEL_COLOR = '#94A3B8';

interface GateData {
  x: number;
  y: number;
  w: number;
  h: number;
  color: string;
}

interface WireData {
  x1: number;
  y1: number;
  x2: number;
  y2: number;
}

/**
 * Seeded pseudo-random number generator for deterministic gate placement.
 */
function seededRandom(seed: number): () => number {
  let s = seed;
  return () => {
    s = (s * 16807 + 0) % 2147483647;
    return (s - 1) / 2147483646;
  };
}

/**
 * Generate a dense grid of gates and connecting wires.
 * We generate a large field so that as we zoom in, more detail is visible.
 */
function generateGates(
  cols: number,
  rows: number,
  cellW: number,
  cellH: number,
  offsetX: number,
  offsetY: number,
  seed: number,
): { gates: GateData[]; wires: WireData[] } {
  const rand = seededRandom(seed);
  const gates: GateData[] = [];
  const wires: WireData[] = [];

  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const gx = offsetX + c * cellW;
      const gy = offsetY + r * cellH;
      const colorIdx = Math.floor(rand() * 3);
      gates.push({
        x: gx,
        y: gy,
        w: cellW * 0.6,
        h: cellH * 0.45,
        color: GATE_COLORS[colorIdx],
      });

      // Horizontal wire to next gate
      if (c < cols - 1 && rand() > 0.3) {
        wires.push({
          x1: gx + cellW * 0.6,
          y1: gy + cellH * 0.22,
          x2: gx + cellW,
          y2: gy + cellH * 0.22,
        });
      }
      // Vertical wire to gate below
      if (r < rows - 1 && rand() > 0.5) {
        wires.push({
          x1: gx + cellW * 0.3,
          y1: gy + cellH * 0.45,
          x2: gx + cellW * 0.3,
          y2: gy + cellH,
        });
      }
    }
  }
  return { gates, wires };
}

export const ChipLayout: React.FC<{
  startFrame: number;
  durationInFrames: number;
}> = ({ startFrame, durationInFrames }) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  // Zoom interpolation across 3 phases
  const zoom = interpolate(
    localFrame,
    [0, 60, 120, durationInFrames],
    [1, 2.5, 5, 8],
    {
      easing: Easing.bezier(0.42, 0, 0.58, 1),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  // Pan toward center-right as we zoom
  const panX = interpolate(localFrame, [0, durationInFrames], [0, -400], {
    easing: Easing.bezier(0.42, 0, 0.58, 1),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });
  const panY = interpolate(localFrame, [0, durationInFrames], [0, -200], {
    easing: Easing.bezier(0.42, 0, 0.58, 1),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Label fade-in over 15 frames (starts at 0.78 to meet minimum opacity requirement)
  const labelOpacity = interpolate(localFrame, [0, 15], [0.78, 0.85], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Generate 3 layers of gates at different scales for fractal density.
  // Layer counts are capped to keep SVG rendering performant while still
  // appearing overwhelmingly dense.
  const layers = useMemo(() => {
    const layer1 = generateGates(80, 54, 24, 20, 0, 0, 42);
    const layer2 = generateGates(120, 70, 16, 15, 0, 0, 137);
    const layer3 = generateGates(160, 90, 12, 12, 0, 0, 999);
    return [layer1, layer2, layer3];
  }, []);

  // Determine which layers to render based on zoom
  const visibleLayers = zoom < 2.5 ? [0] : zoom < 5 ? [0, 1] : [0, 1, 2];

  return (
    <div
      style={{
        width: 1920,
        height: 1080,
        overflow: 'hidden',
        position: 'relative',
      }}
    >
      <div
        style={{
          position: 'absolute',
          left: '50%',
          top: '50%',
          transform: `translate(-50%, -50%) translate(${panX}px, ${panY}px) scale(${zoom})`,
          transformOrigin: 'center center',
          width: 1920,
          height: 1080,
        }}
      >
        {/* SVG canvas for gates and wires */}
        <svg
          width={1920}
          height={1080}
          viewBox="0 0 1920 1080"
          style={{ position: 'absolute', top: 0, left: 0 }}
        >
          {visibleLayers.map((layerIdx) => {
            const { gates, wires } = layers[layerIdx];
            const layerOpacity = layerIdx === 0 ? 1 : layerIdx === 1 ? 0.7 : 0.4;
            return (
              <g key={layerIdx} opacity={layerOpacity}>
                {/* Wires */}
                {wires.map((w, i) => (
                  <line
                    key={`w${layerIdx}-${i}`}
                    x1={w.x1}
                    y1={w.y1}
                    x2={w.x2}
                    y2={w.y2}
                    stroke={WIRE_COLOR}
                    strokeWidth={0.5 / (layerIdx + 1)}
                    opacity={WIRE_OPACITY}
                  />
                ))}
                {/* Gates */}
                {gates.map((g, i) => (
                  <rect
                    key={`g${layerIdx}-${i}`}
                    x={g.x}
                    y={g.y}
                    width={g.w}
                    height={g.h}
                    fill={g.color}
                    opacity={GATE_OPACITY}
                    rx={0.5}
                  />
                ))}
              </g>
            );
          })}
        </svg>
      </div>

      {/* Gate count label — lower-right */}
      <div
        style={{
          position: 'absolute',
          right: 80,
          bottom: 60,
          fontFamily: LABEL_FONT,
          fontSize: 18,
          fontWeight: 400,
          color: LABEL_COLOR,
          opacity: labelOpacity,
          whiteSpace: 'nowrap',
        }}
      >
        2.1 billion gates
      </div>
    </div>
  );
};

export default ChipLayout;

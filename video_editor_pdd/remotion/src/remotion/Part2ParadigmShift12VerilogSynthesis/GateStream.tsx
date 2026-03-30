import React, { useMemo } from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  GATE_COLOR,
  GATE_STREAM_START,
  CHIP_X,
  CHIP_Y,
  CHIP_WIDTH,
  WIDTH,
} from "./constants";

// Gate symbol SVG paths (drawn as small logic gate icons)
const AND_GATE = "M0,-8 L0,8 L10,8 A10,10 0 0,0 10,-8 Z";
const OR_GATE = "M0,-8 Q5,0 0,8 Q10,8 16,0 Q10,-8 0,-8 Z";
const NOT_GATE = "M0,-8 L14,0 L0,8 Z M16,-3 A3,3 0 1,0 16,3 A3,3 0 1,0 16,-3";
const NAND_GATE = "M0,-8 L0,8 L10,8 A10,10 0 0,0 10,-8 Z M20,-3 A3,3 0 1,0 20,3 A3,3 0 1,0 20,-3";

const GATE_TYPES = [AND_GATE, OR_GATE, NOT_GATE, NAND_GATE];

function seededRandom(seed: number): () => number {
  let s = seed;
  return () => {
    s = (s * 16807 + 0) % 2147483647;
    return (s - 1) / 2147483646;
  };
}

interface GateParticle {
  yOffset: number;
  gateIdx: number;
  speed: number;
  scale: number;
  row: number;
}

export const GateStream: React.FC = () => {
  const frame = useCurrentFrame();

  const streamFrame = frame - GATE_STREAM_START;
  const isActive = streamFrame >= 0;

  const startX = CHIP_X + CHIP_WIDTH / 2 + 30;
  const endX = WIDTH + 40;
  const streamWidth = endX - startX;

  const gates = useMemo<GateParticle[]>(() => {
    const rand = seededRandom(99);
    const result: GateParticle[] = [];
    for (let i = 0; i < 30; i++) {
      result.push({
        yOffset: (rand() - 0.5) * 16,
        gateIdx: Math.floor(rand() * GATE_TYPES.length),
        speed: 1.5 + rand() * 1.5,
        scale: 0.7 + rand() * 0.5,
        row: Math.floor(i / 10),
      });
    }
    return result;
  }, []);

  if (!isActive) return null;

  // Row Y positions centered around CHIP_Y
  const rowYs = [CHIP_Y - 30, CHIP_Y, CHIP_Y + 30];

  // Overall stream opacity ramp-in
  const streamOpacity = interpolate(streamFrame, [0, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <svg
      width={WIDTH}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0, opacity: streamOpacity }}
    >
      {/* Connecting wire lines */}
      {rowYs.map((ry, ri) => (
        <line
          key={`wire-${ri}`}
          x1={startX}
          y1={ry}
          x2={endX}
          y2={ry}
          stroke={GATE_COLOR}
          strokeWidth={1}
          opacity={0.2}
        />
      ))}

      {/* Gate symbols flowing right */}
      {gates.map((g, i) => {
        const rowY = rowYs[g.row] + g.yOffset;
        // Each gate starts offset and moves rightward
        const offset = (i % 10) * (streamWidth / 10);
        const xPos = startX + ((offset + streamFrame * g.speed * 2) % streamWidth);

        // Fade in at left edge, fade out at right edge
        const edgeDist = Math.min(xPos - startX, endX - xPos);
        const fadeOpacity = interpolate(edgeDist, [0, 60], [0, 0.85], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        });

        return (
          <g
            key={i}
            transform={`translate(${xPos}, ${rowY}) scale(${g.scale})`}
            opacity={fadeOpacity}
          >
            <path d={GATE_TYPES[g.gateIdx]} fill={GATE_COLOR} fillOpacity={0.3} stroke={GATE_COLOR} strokeWidth={1.5} />
          </g>
        );
      })}

      {/* Small connection dots at intervals */}
      {rowYs.map((ry, ri) =>
        Array.from({ length: 8 }).map((_, di) => {
          const dotX = startX + 60 + ((di * 90 + streamFrame * 2) % streamWidth);
          if (dotX > endX - 20) return null;
          return (
            <circle
              key={`dot-${ri}-${di}`}
              cx={dotX}
              cy={ry}
              r={2.5}
              fill={GATE_COLOR}
              opacity={0.5}
            />
          );
        })
      )}
    </svg>
  );
};

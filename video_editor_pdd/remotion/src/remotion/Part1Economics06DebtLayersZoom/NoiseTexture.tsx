// NoiseTexture.tsx — Animated noise/static overlay for the Context Rot layer
import React, { useMemo } from "react";
import { useCurrentFrame } from "remotion";
import {
  NOISE_COLOR,
  NOISE_OPACITY,
  NOISE_GRAIN_SIZE,
  NOISE_DRIFT_PX_PER_FRAME,
} from "./constants";

interface NoiseTextureProps {
  width: number;
  height: number;
}

/**
 * Generates a canvas-based noise texture that drifts laterally.
 * Uses an SVG filter for the grain effect to avoid canvas dependency.
 */
export const NoiseTexture: React.FC<NoiseTextureProps> = ({ width, height }) => {
  const frame = useCurrentFrame();

  // Lateral drift: 0.5px per frame
  const offsetX = frame * NOISE_DRIFT_PX_PER_FRAME;

  // Generate a deterministic set of noise dots using useMemo
  // We create a grid of semi-random dots that tile
  const noiseDots = useMemo(() => {
    const dots: Array<{ x: number; y: number; opacity: number }> = [];
    const cols = Math.ceil(width / NOISE_GRAIN_SIZE) + 40; // extra for drift
    const rows = Math.ceil(height / NOISE_GRAIN_SIZE);

    // Simple pseudo-random based on position
    for (let r = 0; r < rows; r++) {
      for (let c = 0; c < cols; c++) {
        // Use a hash-like function for pseudo-randomness
        const seed = (r * 997 + c * 131 + 7919) % 1000;
        if (seed < 300) {
          // ~30% density
          dots.push({
            x: c * NOISE_GRAIN_SIZE,
            y: r * NOISE_GRAIN_SIZE,
            opacity: ((seed % 5) + 1) / 5, // varying opacity 0.2-1.0
          });
        }
      }
    }
    return dots;
  }, [width, height]);

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width,
        height,
        overflow: "hidden",
        pointerEvents: "none",
      }}
    >
      <svg
        width={width + 80}
        height={height}
        style={{
          position: "absolute",
          top: 0,
          left: -(offsetX % (NOISE_GRAIN_SIZE * 40)),
        }}
      >
        {noiseDots.map((dot, i) => (
          <rect
            key={i}
            x={dot.x}
            y={dot.y}
            width={NOISE_GRAIN_SIZE}
            height={NOISE_GRAIN_SIZE}
            fill={NOISE_COLOR}
            opacity={NOISE_OPACITY * dot.opacity}
          />
        ))}
      </svg>
    </div>
  );
};

export default NoiseTexture;

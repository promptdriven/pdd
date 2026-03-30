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
  opacity?: number;
  grainSize?: number;
  driftSpeed?: number;
}

/**
 * Generates a subtle animated noise/static overlay using SVG filters.
 * Drifts laterally to create a "living static" effect on the Context Rot layer.
 */
export const NoiseTexture: React.FC<NoiseTextureProps> = ({
  width,
  height,
  opacity = NOISE_OPACITY,
  grainSize = NOISE_GRAIN_SIZE,
  driftSpeed = NOISE_DRIFT_PX_PER_FRAME,
}) => {
  const frame = useCurrentFrame();

  // Lateral drift offset
  const driftX = frame * driftSpeed;

  // Generate a pseudo-random seed based on frame for animation
  // We use multiple overlapping noise layers offset by frame
  const filterId = useMemo(() => `noise-filter-${Math.random().toString(36).slice(2, 8)}`, []);

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
        width={width + 100}
        height={height}
        style={{
          position: "absolute",
          top: 0,
          left: -50 + (driftX % 100) - 50,
        }}
      >
        <defs>
          <filter id={filterId}>
            <feTurbulence
              type="fractalNoise"
              baseFrequency={`${0.5 / grainSize} ${0.5 / grainSize}`}
              numOctaves={3}
              seed={Math.floor(frame / 3)}
              stitchTiles="stitch"
            />
            <feColorMatrix
              type="saturate"
              values="0"
            />
          </filter>
        </defs>
        <rect
          x={0}
          y={0}
          width={width + 100}
          height={height}
          filter={`url(#${filterId})`}
          fill={NOISE_COLOR}
          opacity={opacity}
        />
      </svg>
    </div>
  );
};

export default NoiseTexture;

import React, { useMemo } from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface NoiseTextureProps {
  /** Bounding region for the noise overlay */
  left: number;
  top: number;
  width: number;
  height: number;
  /** Base opacity of the noise layer */
  baseOpacity: number;
  /** Extra opacity added when pulsing */
  pulseAmplitude: number;
  /** Whether the noise is currently in a "pulse" state (0-1) */
  pulseProgress: number;
}

/**
 * Renders a pseudo-noise texture using SVG filters.
 * Pulses opacity in sync with the feedback loop.
 */
const NoiseTexture: React.FC<NoiseTextureProps> = ({
  left,
  top,
  width,
  height,
  baseOpacity,
  pulseAmplitude,
  pulseProgress,
}) => {
  const frame = useCurrentFrame();

  // Sine-based pulse for a smooth breathing effect
  const pulseOpacity = interpolate(
    pulseProgress,
    [0, 0.5, 1],
    [0, pulseAmplitude, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const opacity = baseOpacity + pulseOpacity;

  // Generate a unique seed per frame for animated noise
  const seed = useMemo(() => frame % 120, [frame]);

  return (
    <div
      style={{
        position: "absolute",
        left,
        top,
        width,
        height,
        opacity,
        overflow: "hidden",
        pointerEvents: "none",
      }}
    >
      <svg
        width={width}
        height={height}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <filter id={`noise-${seed}`}>
            <feTurbulence
              type="fractalNoise"
              baseFrequency="0.65"
              numOctaves={3}
              seed={seed}
              stitchTiles="stitch"
            />
            <feColorMatrix
              type="matrix"
              values="0 0 0 0 0.94
                      0 0 0 0 0.27
                      0 0 0 0 0.27
                      0 0 0 0.6 0"
            />
          </filter>
        </defs>
        <rect
          width={width}
          height={height}
          filter={`url(#noise-${seed})`}
          opacity={1}
        />
      </svg>
    </div>
  );
};

export default NoiseTexture;

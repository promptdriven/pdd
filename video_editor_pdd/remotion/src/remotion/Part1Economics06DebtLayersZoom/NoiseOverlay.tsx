import React, { useMemo } from "react";
import { useCurrentFrame } from "remotion";

/**
 * Generates a repeatable pseudo-random noise pattern as an SVG filter.
 * The pattern drifts laterally to create a subtle animated static effect.
 */

interface NoiseOverlayProps {
  /** Width of the overlay area */
  width: number;
  /** Height of the overlay area */
  height: number;
  /** Noise grain color */
  grainColor: string;
  /** Noise opacity (0-1) */
  grainOpacity: number;
  /** Grain size in px */
  grainSize: number;
  /** Lateral drift speed in px/frame */
  driftSpeed: number;
  /** Overall opacity of the overlay (for fade-in) */
  opacity: number;
}

const NoiseOverlay: React.FC<NoiseOverlayProps> = ({
  width,
  height,
  grainColor,
  grainOpacity,
  grainSize,
  driftSpeed,
  opacity,
}) => {
  const frame = useCurrentFrame();
  const driftX = frame * driftSpeed;

  // Generate a grid of noise rectangles procedurally
  const noiseRects = useMemo(() => {
    const rects: { x: number; y: number; opacity: number }[] = [];
    const cols = Math.ceil(width / grainSize) + 2;
    const rows = Math.ceil(height / grainSize) + 2;

    // Use a simple seeded random for deterministic noise per-frame
    // We regenerate pattern every 4 frames for a flickering static feel
    const seed = Math.floor(frame / 4);
    let hash = seed;

    for (let row = 0; row < rows; row++) {
      for (let col = 0; col < cols; col++) {
        // Simple LCG pseudo-random
        hash = (hash * 1103515245 + 12345) & 0x7fffffff;
        const rand = (hash % 1000) / 1000;
        // Only render ~30% of cells for a sparse noise look
        if (rand < 0.3) {
          rects.push({
            x: col * grainSize,
            y: row * grainSize,
            opacity: rand * 2, // 0 to 0.6 range
          });
        }
      }
    }
    return rects;
  }, [width, height, grainSize, frame]);

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width,
        height,
        overflow: "hidden",
        opacity,
        pointerEvents: "none",
      }}
    >
      <svg
        width={width}
        height={height}
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          transform: `translateX(${driftX % grainSize}px)`,
        }}
      >
        {noiseRects.map((rect, i) => (
          <rect
            key={i}
            x={rect.x}
            y={rect.y}
            width={grainSize}
            height={grainSize}
            fill={grainColor}
            opacity={grainOpacity * rect.opacity}
          />
        ))}
      </svg>
    </div>
  );
};

export default NoiseOverlay;

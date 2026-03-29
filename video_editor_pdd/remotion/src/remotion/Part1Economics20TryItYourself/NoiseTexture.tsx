import React, { useMemo } from "react";
import { AbsoluteFill, random } from "remotion";

interface NoiseTextureProps {
  color: string;
  opacity: number;
  seed?: number;
}

/**
 * Generates a subtle noise/grain texture overlay using small SVG rects.
 * Static — does not animate per-frame.
 */
export const NoiseTexture: React.FC<NoiseTextureProps> = ({
  color,
  opacity,
  seed = 42,
}) => {
  const dots = useMemo(() => {
    const result: { x: number; y: number; o: number }[] = [];
    const step = 12;
    for (let x = 0; x < 1920; x += step) {
      for (let y = 0; y < 1080; y += step) {
        const r = random(`noise-${seed}-${x}-${y}`);
        if (r > 0.6) {
          result.push({ x, y, o: r * opacity });
        }
      }
    }
    return result;
  }, [seed, opacity]);

  return (
    <AbsoluteFill style={{ pointerEvents: "none" }}>
      <svg width={1920} height={1080} viewBox="0 0 1920 1080">
        {dots.map((d, i) => (
          <rect
            key={i}
            x={d.x}
            y={d.y}
            width={2}
            height={2}
            fill={color}
            opacity={d.o}
          />
        ))}
      </svg>
    </AbsoluteFill>
  );
};

export default NoiseTexture;

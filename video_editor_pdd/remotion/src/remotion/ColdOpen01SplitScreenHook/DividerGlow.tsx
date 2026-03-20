import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface DividerGlowProps {
  x: number;
  colorTop: string;
  colorBottom: string;
  opacity: number;
  cycleFrames: number;
  canvasHeight: number;
}

/**
 * A pulsing gradient glow on the vertical divider that oscillates
 * between two colors using a sine ease.
 */
const DividerGlow: React.FC<DividerGlowProps> = ({
  x,
  colorTop,
  colorBottom,
  opacity,
  cycleFrames,
  canvasHeight,
}) => {
  const frame = useCurrentFrame();

  // Sine oscillation: 0 → 1 → 0 per cycle
  const pulse = interpolate(frame % cycleFrames, [0, cycleFrames], [0, 1], {
    easing: (t) => Math.sin(t * Math.PI),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const glowWidth = 12 + pulse * 8; // 12-20px spread

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: x - glowWidth / 2,
        width: glowWidth,
        height: canvasHeight,
        opacity: opacity * (0.5 + pulse * 0.5),
        background: `linear-gradient(to bottom, ${colorTop}, ${colorBottom})`,
        filter: `blur(${4 + pulse * 4}px)`,
        pointerEvents: "none",
      }}
    />
  );
};

export default DividerGlow;

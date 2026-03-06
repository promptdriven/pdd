import React from "react";
import { AbsoluteFill } from "remotion";
import { WIDTH, HEIGHT } from "./constants";

interface RadialGlowProps {
  /** Center position [x, y] in canvas coordinates */
  center: [number, number];
  /** Radius of the radial gradient in pixels */
  radius: number;
  /** CSS color string for the glow */
  color: string;
  /** Opacity of the glow (0–1) */
  opacity: number;
}

/**
 * A single radial gradient glow positioned absolutely on the canvas.
 * Renders a full-screen div with a radial-gradient background.
 */
export const RadialGlow: React.FC<RadialGlowProps> = ({
  center,
  radius,
  color,
  opacity,
}) => {
  const [cx, cy] = center;

  return (
    <AbsoluteFill
      style={{
        width: WIDTH,
        height: HEIGHT,
        opacity,
        background: `radial-gradient(circle ${radius}px at ${cx}px ${cy}px, ${color}, transparent)`,
        pointerEvents: "none",
      }}
    />
  );
};

export default RadialGlow;

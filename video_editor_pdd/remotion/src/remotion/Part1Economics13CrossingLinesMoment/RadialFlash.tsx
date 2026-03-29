// RadialFlash.tsx — White radial glow flash at crossing points
import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { FLASH_COLOR } from "./constants";

interface RadialFlashProps {
  /** Center X position */
  cx: number;
  /** Center Y position */
  cy: number;
  /** Maximum radius of the flash */
  maxRadius: number;
  /** Frame at which the flash starts (absolute) */
  startFrame: number;
  /** Duration in frames */
  duration: number;
}

export const RadialFlash: React.FC<RadialFlashProps> = ({
  cx,
  cy,
  maxRadius,
  startFrame,
  duration,
}) => {
  const frame = useCurrentFrame();

  if (frame < startFrame || frame > startFrame + duration) return null;

  const progress = interpolate(
    frame,
    [startFrame, startFrame + duration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.exp),
    }
  );

  // Radius grows, opacity fades
  const radius = maxRadius * (0.3 + 0.7 * progress);
  const opacity = interpolate(progress, [0, 0.2, 1], [0, 0.9, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      <defs>
        <radialGradient id={`flash-${cx}-${cy}`}>
          <stop offset="0%" stopColor={FLASH_COLOR} stopOpacity={1} />
          <stop offset="60%" stopColor={FLASH_COLOR} stopOpacity={0.4} />
          <stop offset="100%" stopColor={FLASH_COLOR} stopOpacity={0} />
        </radialGradient>
      </defs>
      <circle
        cx={cx}
        cy={cy}
        r={radius}
        fill={`url(#flash-${cx}-${cy})`}
        opacity={opacity}
      />
      {/* Sharp center dot */}
      <circle
        cx={cx}
        cy={cy}
        r={4}
        fill={FLASH_COLOR}
        opacity={opacity * 1.2}
      />
    </svg>
  );
};

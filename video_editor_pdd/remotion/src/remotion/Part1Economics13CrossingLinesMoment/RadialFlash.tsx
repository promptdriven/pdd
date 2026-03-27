import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { FLASH_COLOR } from "./constants";

export interface RadialFlashProps {
  /** Pixel position of the flash center */
  cx: number;
  cy: number;
  /** Maximum radius of the flash */
  radius: number;
  /** Frame at which the flash triggers (relative to this component's mount) */
  triggerFrame: number;
  /** Duration of flash in frames */
  duration?: number;
  color?: string;
}

export const RadialFlash: React.FC<RadialFlashProps> = ({
  cx,
  cy,
  radius,
  triggerFrame,
  duration = 20,
  color = FLASH_COLOR,
}) => {
  const frame = useCurrentFrame();

  if (frame < triggerFrame || frame > triggerFrame + duration) {
    return null;
  }

  const localFrame = frame - triggerFrame;

  const opacity = interpolate(localFrame, [0, duration], [0.9, 0], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.expo),
  });

  const currentRadius = interpolate(localFrame, [0, duration], [4, radius], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.expo),
  });

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      <defs>
        <radialGradient id={`flash-grad-${cx}-${cy}`}>
          <stop offset="0%" stopColor={color} stopOpacity={opacity} />
          <stop offset="60%" stopColor={color} stopOpacity={opacity * 0.5} />
          <stop offset="100%" stopColor={color} stopOpacity={0} />
        </radialGradient>
      </defs>
      <circle
        cx={cx}
        cy={cy}
        r={currentRadius}
        fill={`url(#flash-grad-${cx}-${cy})`}
      />
      {/* Inner bright core */}
      <circle
        cx={cx}
        cy={cy}
        r={currentRadius * 0.3}
        fill={color}
        opacity={opacity}
      />
    </svg>
  );
};

export default RadialFlash;

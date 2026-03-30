import React, { useMemo } from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  PATCH_LINE_COLOR,
  IMMEDIATE_PATCH_DATA,
  PULSE_START,
  PULSE_END,
  mapX,
  mapY,
} from "./constants";

/**
 * Pulsing glow effect on the amber solid line during the "validation" beat.
 * Shows a bright glow cycling on a 30-frame period.
 */
export const PulseLine: React.FC = () => {
  const frame = useCurrentFrame();

  const pathD = useMemo(() => {
    return IMMEDIATE_PATCH_DATA.map((pt, i) => {
      const px = mapX(pt.x);
      const py = mapY(pt.y);
      return `${i === 0 ? "M" : "L"} ${px} ${py}`;
    }).join(" ");
  }, []);

  if (frame < PULSE_START || frame > PULSE_END + 30) return null;

  // Fade in/out the pulse effect
  const pulseEnvelope = interpolate(
    frame,
    [PULSE_START, PULSE_START + 15, PULSE_END - 15, PULSE_END],
    [0, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Oscillating glow: 30-frame cycle using sine easing
  const cycleFrame = (frame - PULSE_START) % 30;
  const pulseIntensity = interpolate(cycleFrame, [0, 15, 30], [0.3, 1, 0.3], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.sin),
  });

  const glowAmount = pulseEnvelope * pulseIntensity;

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <defs>
        <filter id="pulse-glow" x="-20%" y="-20%" width="140%" height="140%">
          <feGaussianBlur
            stdDeviation={8 * glowAmount}
            result="blur"
          />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>
      <path
        d={pathD}
        fill="none"
        stroke={PATCH_LINE_COLOR}
        strokeWidth={4}
        strokeLinecap="round"
        strokeLinejoin="round"
        opacity={0.6 * glowAmount}
        filter="url(#pulse-glow)"
      />
    </svg>
  );
};

export default PulseLine;

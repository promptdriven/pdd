import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  GLOW_DURATION,
  GLOW_SWEEP_WIDTH,
  CELL_PDD_COLOR,
} from "./constants";

interface GlowSweepProps {
  regionX: number;
  regionY: number;
  regionWidth: number;
  regionHeight: number;
}

export const GlowSweep: React.FC<GlowSweepProps> = ({
  regionX,
  regionY,
  regionWidth,
  regionHeight,
}) => {
  const frame = useCurrentFrame();

  // Linear sweep from top to bottom of the region
  const sweepProgress = interpolate(frame, [0, GLOW_DURATION], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.linear,
  });

  // The glow band moves from above the region to below
  const totalTravel = regionHeight + GLOW_SWEEP_WIDTH;
  const sweepY = regionY - GLOW_SWEEP_WIDTH + sweepProgress * totalTravel;

  return (
    <div
      style={{
        position: "absolute",
        left: regionX,
        top: regionY,
        width: regionWidth,
        height: regionHeight,
        overflow: "hidden",
        pointerEvents: "none",
      }}
    >
      <div
        style={{
          position: "absolute",
          left: 0,
          top: sweepY - regionY,
          width: regionWidth,
          height: GLOW_SWEEP_WIDTH,
          background: `linear-gradient(180deg, transparent 0%, ${CELL_PDD_COLOR}14 30%, ${CELL_PDD_COLOR}14 70%, transparent 100%)`,
          pointerEvents: "none",
        }}
      />
    </div>
  );
};

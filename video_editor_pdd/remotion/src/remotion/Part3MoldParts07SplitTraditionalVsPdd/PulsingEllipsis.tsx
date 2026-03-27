import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import { ELLIPSIS_CYCLE } from "./constants";

interface PulsingEllipsisProps {
  color: string;
  startFrame: number;
  centerX: number;
  y: number;
}

export const PulsingEllipsis: React.FC<PulsingEllipsisProps> = ({
  color,
  startFrame,
  centerX,
  y,
}) => {
  const frame = useCurrentFrame();

  if (frame < startFrame) return null;

  const elapsed = frame - startFrame;

  return (
    <div
      style={{
        position: "absolute",
        left: centerX - 30,
        top: y,
        width: 60,
        display: "flex",
        justifyContent: "center",
        gap: 8,
      }}
    >
      {[0, 1, 2].map((dotIndex) => {
        const dotPhase = (elapsed + dotIndex * 7) % ELLIPSIS_CYCLE;
        const dotOpacity = interpolate(
          dotPhase,
          [0, ELLIPSIS_CYCLE / 2, ELLIPSIS_CYCLE],
          [0.15, 0.5, 0.15],
          { extrapolateRight: "clamp", easing: Easing.inOut(Easing.sin) }
        );
        return (
          <div
            key={dotIndex}
            style={{
              width: 6,
              height: 6,
              borderRadius: "50%",
              backgroundColor: color,
              opacity: dotOpacity,
            }}
          />
        );
      })}
    </div>
  );
};

export default PulsingEllipsis;

import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { COLORS } from "./constants";

/**
 * Renders the label and sublabel for a pipeline step,
 * fading in when the step activates.
 */
export const StepLabel: React.FC<{
  label: string;
  sublabel: string;
  x: number;
  y: number;
  startFrame: number;
}> = ({ label, sublabel, x, y, startFrame }) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  const opacity = localFrame < 0
    ? 0
    : interpolate(localFrame, [0, 15], [0, 1], {
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.cubic),
      });

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y + 40,
        transform: "translateX(-50%)",
        textAlign: "center",
        opacity,
      }}
    >
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          color: COLORS.textPrimary,
          opacity: 0.5,
          whiteSpace: "nowrap",
        }}
      >
        {label}
      </div>
      <div
        style={{
          fontFamily: "JetBrains Mono, monospace",
          fontSize: 11,
          color: COLORS.textSecondary,
          opacity: 0.3,
          marginTop: 4,
          whiteSpace: "nowrap",
        }}
      >
        {sublabel}
      </div>
    </div>
  );
};

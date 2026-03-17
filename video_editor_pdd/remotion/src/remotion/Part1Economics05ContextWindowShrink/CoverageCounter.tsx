import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  COUNTER_X,
  COUNTER_Y,
  FONT_FAMILY,
  GRID_STAGES,
  GRID_APPEAR_START,
  GRID_APPEAR_END,
} from "./constants";

/**
 * CoverageCounter — displays "Context coverage: XX%" with animated
 * value and color transitions as the grid grows.
 */
export const CoverageCounter: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [GRID_APPEAR_START, GRID_APPEAR_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Determine current coverage value and color
  let currentCoverage = GRID_STAGES[0].coverage;
  let currentColor = GRID_STAGES[0].coverageColor;

  for (let i = 1; i < GRID_STAGES.length; i++) {
    const stage = GRID_STAGES[i];
    const prev = GRID_STAGES[i - 1];
    if (frame >= stage.morphStart) {
      const progress = interpolate(
        frame,
        [stage.morphStart, stage.morphEnd + 15],
        [0, 1],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.quad),
        }
      );
      currentCoverage = prev.coverage + (stage.coverage - prev.coverage) * progress;

      // Color transition
      const colorProgress = interpolate(
        frame,
        [stage.morphStart, stage.morphEnd + 20],
        [0, 1],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.inOut(Easing.quad),
        }
      );

      if (colorProgress >= 1) {
        currentColor = stage.coverageColor;
      } else if (colorProgress > 0) {
        currentColor = lerpColor(prev.coverageColor, stage.coverageColor, colorProgress);
      }
    }
  }

  const displayValue = Math.round(currentCoverage);

  return (
    <div
      style={{
        position: "absolute",
        left: COUNTER_X,
        top: COUNTER_Y,
        opacity,
        textAlign: "right" as const,
      }}
    >
      <div
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: 12,
          color: "#94A3B8",
          opacity: 0.5,
          marginBottom: 4,
        }}
      >
        Context coverage:
      </div>
      <div
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: 28,
          fontWeight: 700,
          color: currentColor,
        }}
      >
        {displayValue}%
      </div>
    </div>
  );
};

/** Linearly interpolate between two hex colors */
function lerpColor(a: string, b: string, t: number): string {
  const parse = (hex: string) => {
    const h = hex.replace("#", "");
    return [
      parseInt(h.substring(0, 2), 16),
      parseInt(h.substring(2, 4), 16),
      parseInt(h.substring(4, 6), 16),
    ];
  };
  const [r1, g1, b1] = parse(a);
  const [r2, g2, b2] = parse(b);
  const r = Math.round(r1 + (r2 - r1) * t);
  const g = Math.round(g1 + (g2 - g1) * t);
  const bl = Math.round(b1 + (b2 - b1) * t);
  return `rgb(${r}, ${g}, ${bl})`;
}

export default CoverageCounter;

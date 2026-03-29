import React, { useMemo } from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  COUNTER_X,
  COUNTER_Y,
  LABEL_COLOR,
  GROWTH_STAGES,
} from "./constants";

/**
 * Top-right coverage counter showing "Context coverage: XX%"
 * with color transitions and spring-animated number changes.
 */

interface CoverageCounterProps {
  currentStageIndex: number;
  transitionProgress: number;
}

const CoverageCounter: React.FC<CoverageCounterProps> = ({
  currentStageIndex,
  transitionProgress,
}) => {
  const frame = useCurrentFrame();

  const stage = GROWTH_STAGES[currentStageIndex];
  const prevStage =
    currentStageIndex > 0
      ? GROWTH_STAGES[currentStageIndex - 1]
      : GROWTH_STAGES[0];

  // Interpolate coverage number during transitions
  const displayCoverage = useMemo(() => {
    if (transitionProgress >= 1 || currentStageIndex === 0) {
      return stage.coverage;
    }
    return Math.round(
      prevStage.coverage +
        (stage.coverage - prevStage.coverage) * transitionProgress
    );
  }, [stage, prevStage, transitionProgress, currentStageIndex]);

  // Interpolate color
  const coverageColor = useMemo(() => {
    if (transitionProgress >= 1 || currentStageIndex === 0) {
      return stage.coverageColor;
    }
    // Parse hex colors and lerp
    const from = hexToRgb(prevStage.coverageColor);
    const to = hexToRgb(stage.coverageColor);
    const t = transitionProgress;
    const r = Math.round(from.r + (to.r - from.r) * t);
    const g = Math.round(from.g + (to.g - from.g) * t);
    const b = Math.round(from.b + (to.b - from.b) * t);
    return `rgb(${r}, ${g}, ${b})`;
  }, [stage, prevStage, transitionProgress, currentStageIndex]);

  // Visible from frame 0, fully bright by frame 20
  const opacity = interpolate(frame, [0, 20], [0.7, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        position: "absolute",
        left: COUNTER_X,
        top: COUNTER_Y,
        opacity,
        display: "flex",
        flexDirection: "column",
        alignItems: "flex-end",
        zIndex: 20,
      }}
    >
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 400,
          color: LABEL_COLOR,
          marginBottom: 4,
        }}
      >
        Context coverage:
      </span>
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 36,
          fontWeight: 700,
          color: coverageColor,
          lineHeight: 1,
        }}
      >
        {displayCoverage}%
      </span>
    </div>
  );
};

function hexToRgb(hex: string): { r: number; g: number; b: number } {
  const h = hex.replace("#", "");
  return {
    r: parseInt(h.substring(0, 2), 16),
    g: parseInt(h.substring(2, 4), 16),
    b: parseInt(h.substring(4, 6), 16),
  };
}

export default CoverageCounter;

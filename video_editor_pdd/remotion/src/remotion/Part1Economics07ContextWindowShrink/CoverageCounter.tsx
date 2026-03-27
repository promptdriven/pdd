import React, { useMemo } from "react";
import { useCurrentFrame, interpolate, Easing, spring, useVideoConfig } from "remotion";
import {
  GROWTH_STAGES,
  TRANSITION_FRAMES,
  COUNTER_X,
  COUNTER_Y,
  LABEL_COLOR,
} from "./constants";

/**
 * Displays the "Context coverage: XX%" counter in the top-right.
 * Color transitions between stage colors; number uses spring physics.
 */
export const CoverageCounter: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Compute the current coverage percentage (animated)
  const currentCoverage = useMemo(() => {
    let coverage = GROWTH_STAGES[0].coveragePercent;

    for (let i = 1; i < GROWTH_STAGES.length; i++) {
      const stage = GROWTH_STAGES[i];
      const prevStage = GROWTH_STAGES[i - 1];
      const transitionStart = stage.startFrame;
      const transitionEnd = transitionStart + TRANSITION_FRAMES;

      if (frame >= transitionEnd) {
        coverage = stage.coveragePercent;
      } else if (frame >= transitionStart) {
        const progress = interpolate(
          frame,
          [transitionStart, transitionEnd],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
        );
        coverage = prevStage.coveragePercent + (stage.coveragePercent - prevStage.coveragePercent) * progress;
      }
    }
    return Math.round(coverage);
  }, [frame]);

  // Compute the current color by interpolating between stages
  const currentColor = useMemo(() => {
    for (let i = GROWTH_STAGES.length - 1; i >= 0; i--) {
      const stage = GROWTH_STAGES[i];
      if (i === 0) return stage.coverageColor;

      const transitionEnd = stage.startFrame + TRANSITION_FRAMES;
      if (frame >= transitionEnd) return stage.coverageColor;

      if (frame >= stage.startFrame) {
        // During transition — interpolate color via opacity crossfade
        const prevColor = GROWTH_STAGES[i - 1].coverageColor;
        const progress = interpolate(
          frame,
          [stage.startFrame, transitionEnd],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
        );
        // Return the new color once past halfway; otherwise the old
        return progress > 0.5 ? stage.coverageColor : prevColor;
      }
    }
    return GROWTH_STAGES[0].coverageColor;
  }, [frame]);

  // Fade in
  const opacity = interpolate(frame, [40, 70], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Spring-driven scale on number changes
  const numberScale = useMemo(() => {
    for (let i = 1; i < GROWTH_STAGES.length; i++) {
      const start = GROWTH_STAGES[i].startFrame;
      if (frame >= start && frame < start + TRANSITION_FRAMES) {
        const s = spring({
          frame: frame - start,
          fps,
          config: { stiffness: 100, damping: 12, mass: 0.5 },
        });
        return 0.85 + s * 0.15;
      }
    }
    return 1;
  }, [frame, fps]);

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
        transform: "translateX(-50%)",
      }}
    >
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 400,
          color: LABEL_COLOR,
          marginBottom: 4,
          whiteSpace: "nowrap",
        }}
      >
        Context coverage:
      </div>
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 36,
          fontWeight: 700,
          color: currentColor,
          transform: `scale(${numberScale})`,
          transformOrigin: "center right",
          whiteSpace: "nowrap",
        }}
      >
        {currentCoverage}%
      </div>
    </div>
  );
};

export default CoverageCounter;

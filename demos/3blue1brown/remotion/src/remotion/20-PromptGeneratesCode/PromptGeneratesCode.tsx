import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { PromptDoc } from "./PromptDoc";
import { CodeFlow } from "./CodeFlow";
import { TestWalls } from "./TestWall";
import { COLORS, BEATS, PromptGeneratesCodePropsType } from "./constants";

/**
 * Main composition: Prompt Generates Code - Tests as Walls.
 *
 * Sequence:
 *   0-60:   Prompt activates with blue glow
 *   60-150: Code particles stream from prompt
 *   150-270: Test walls materialize as amber bars
 *   270-360: Code fills the walled container
 *   360-450: Final state with glow hierarchy
 */
export const PromptGeneratesCode: React.FC<PromptGeneratesCodePropsType> = ({
  showNarration = true,
}) => {
  const frame = useCurrentFrame();

  // Narration fade-in during final phase
  const narrationOpacity = showNarration
    ? interpolate(
        frame,
        [BEATS.NARRATION_START, BEATS.NARRATION_START + 30],
        [0, 1],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        },
      )
    : 0;

  return (
    <AbsoluteFill
      style={{
        background: COLORS.BACKGROUND,
      }}
    >
      {/* Prompt document (top-left) */}
      <PromptDoc />

      {/* Test walls (amber container) - rendered behind code flow for layering */}
      <TestWalls />

      {/* Code particles + fill */}
      <CodeFlow />

      {/* Narration overlay */}
      {narrationOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 100,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: narrationOpacity,
          }}
        >
          <div
            style={{
              fontSize: 28,
              fontFamily: "sans-serif",
              fontWeight: 400,
              color: "rgba(255, 255, 255, 0.95)",
              lineHeight: 1.6,
              maxWidth: 1100,
              margin: "0 auto",
              letterSpacing: 0.5,
            }}
          >
            The prompt is your mold. The code is just plastic. And just like
            chip synthesis--the code is different every generation. But the
            tests lock the behavior. The process is deterministic.
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};

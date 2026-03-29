import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { BG_COLOR, TOTAL_FRAMES } from "./constants";
import { ChartAxes } from "./ChartAxes";
import { ForkingLines } from "./ForkingLines";
import { Annotations } from "./Annotations";
import { TrapArrow } from "./TrapArrow";

export const defaultPart1Economics10ForkCodebaseSizeProps = {};

/**
 * Section 1.10: Fork by Codebase Size — The Trap
 *
 * The patch cost line forks at ~2020 into two diverging paths:
 * - Small codebase: AI patching is transformative (plunges down)
 * - Large codebase: experienced devs are actually slower with AI (stays flat)
 *
 * Annotations reveal the METR 2025 finding and the perception gap.
 * A curved arrow shows the trap: every patch adds code, pushing you
 * from the world where AI helps into the world where it doesn't.
 *
 * Duration: ~46s (1380 frames @ 30fps)
 */
export const Part1Economics10ForkCodebaseSize: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Base chart: axes, grid, labels — visible from frame 0 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ChartAxes />
      </Sequence>

      {/* Chart lines: generate line, patch line, forking lines */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ForkingLines />
      </Sequence>

      {/* Annotations: context label, METR citation, belief gap */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <Annotations />
      </Sequence>

      {/* Trap arrow: curved dashed arrow + "Every patch adds code." */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <TrapArrow />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics10ForkCodebaseSize;

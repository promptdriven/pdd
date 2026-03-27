import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { BG_COLOR, TOTAL_FRAMES } from "./constants";
import ChartAxes from "./ChartAxes";
import ForkingLines from "./ForkingLines";
import Annotations from "./Annotations";
import TrapArrow from "./TrapArrow";

export const defaultPart1Economics10ForkCodebaseSizeProps = {};

/**
 * Section 1.10 — Fork by Codebase Size: The Trap
 *
 * Visualises how AI-assisted patching cost forks into two diverging stories
 * depending on codebase size:
 *   • Small codebases — cost plunges (green)
 *   • Large codebases — cost stays flat / devs slower (red)
 *
 * Duration: 1380 frames @ 30 fps (~46 s)
 */
export const Part1Economics10ForkCodebaseSize: React.FC = () => {
  return (
    <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
      <AbsoluteFill
        style={{
          backgroundColor: BG_COLOR,
          overflow: "hidden",
        }}
      >
        {/* Layer 1: Chart grid, axes, labels */}
        <ChartAxes />

        {/* Layer 2: Generate line, patch line, forking lines, debt area */}
        <ForkingLines />

        {/* Layer 3: Text annotations (METR, perception gap, context label) */}
        <Annotations />

        {/* Layer 4: Curved trap arrow + label */}
        <TrapArrow />
      </AbsoluteFill>
    </Sequence>
  );
};

export default Part1Economics10ForkCodebaseSize;

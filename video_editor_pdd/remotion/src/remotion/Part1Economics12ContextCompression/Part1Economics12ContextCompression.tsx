// Part1Economics12ContextCompression.tsx
// Section 1.12: Context Compression — 20 Modules Fit as Prompts
// Duration: ~46s (1380 frames @ 30fps)
import React from "react";
import { AbsoluteFill, Sequence } from "remotion";

import { BG_COLOR, TOTAL_FRAMES } from "./constants";
import ContextWindowFrame from "./ContextWindowFrame";
import ModuleBlocks from "./ModuleBlocks";
import OverflowIndicator from "./OverflowIndicator";
import RemainingSpaceIndicator from "./RemainingSpaceIndicator";
import PhaseLabels from "./PhaseLabels";

export const defaultPart1Economics12ContextCompressionProps = {};

export const Part1Economics12ContextCompression: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Context window frame — draws in from frame 0 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ContextWindowFrame />
      </Sequence>

      {/* Module blocks — slide in from frame 60, morph at frame 420 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ModuleBlocks />
      </Sequence>

      {/* Overflow indicator — appears at frame 300, fades at frame 420 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <OverflowIndicator />
      </Sequence>

      {/* Remaining space indicator — appears at frame 600 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <RemainingSpaceIndicator />
      </Sequence>

      {/* Phase labels */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <PhaseLabels />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics12ContextCompression;

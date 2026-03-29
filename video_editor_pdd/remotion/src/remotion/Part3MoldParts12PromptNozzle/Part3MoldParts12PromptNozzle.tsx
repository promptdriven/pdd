import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { BG_COLOR, TOTAL_FRAMES } from "./constants";
import { BlueprintGrid } from "./BlueprintGrid";
import { MoldCrossSection } from "./MoldCrossSection";
import { NozzleLabels } from "./NozzleLabels";
import { FileLabel } from "./FileLabel";
import { TextStream } from "./TextStream";
import { DualCavity } from "./DualCavity";
import { TerminalWindow } from "./TerminalWindow";

export const defaultPart3MoldParts12PromptNozzleProps = {};

/**
 * Section 3.12: Prompt Nozzle
 *
 * Shows a mold cross-section where the nozzle (injection point) illuminates
 * as the "prompt" — the specification of what you want. Labels float in,
 * prompt text streams into the cavity, and two different code generations
 * demonstrate that implementations vary while behavior stays fixed.
 *
 * Duration: 720 frames (24s @ 30fps)
 */
export const Part3MoldParts12PromptNozzle: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Mold cross-section with nozzle highlight (always visible) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <MoldCrossSection />
      </Sequence>

      {/* Nozzle labels: intent, requirements, constraints */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <NozzleLabels />
      </Sequence>

      {/* File label: user_parser.prompt (frames 90-150) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <FileLabel />
      </Sequence>

      {/* Prompt text streaming into cavity (from frame 120) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <TextStream />
      </Sequence>

      {/* Dual cavity with two code versions (from frame 240) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <DualCavity />
      </Sequence>

      {/* Terminal window (from frame 300) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <TerminalWindow />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part3MoldParts12PromptNozzle;

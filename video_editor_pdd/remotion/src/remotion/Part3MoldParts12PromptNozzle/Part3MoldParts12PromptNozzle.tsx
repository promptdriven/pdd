import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { BG_COLOR, DURATION_FRAMES } from "./constants";
import { BlueprintGrid } from "./BlueprintGrid";
import { MoldCrossSection } from "./MoldCrossSection";
import { NozzleLabels } from "./NozzleLabels";
import { FileLabel } from "./FileLabel";
import { PromptTextStream } from "./PromptTextStream";
import { DualCavity } from "./DualCavity";
import { TerminalWindow } from "./TerminalWindow";

export const defaultPart3MoldParts12PromptNozzleProps = {};

export const Part3MoldParts12PromptNozzle: React.FC = () => {
  return (
    <Sequence from={0} durationInFrames={DURATION_FRAMES}>
      <AbsoluteFill
        style={{
          backgroundColor: BG_COLOR,
          overflow: "hidden",
        }}
      >
        {/* Blueprint grid background */}
        <BlueprintGrid />

        {/* Mold cross-section with highlighted nozzle */}
        <MoldCrossSection wallsOpacity={0.1} nozzleGlowOpacity={1.0} />

        {/* Nozzle labels: "intent", "requirements", "constraints" */}
        <NozzleLabels />

        {/* File label: user_parser.prompt */}
        <FileLabel />

        {/* Prompt text streaming into cavity */}
        <PromptTextStream />

        {/* Dual cavity with two code versions */}
        <DualCavity />

        {/* Terminal showing pdd generate commands */}
        <TerminalWindow />
      </AbsoluteFill>
    </Sequence>
  );
};

export default Part3MoldParts12PromptNozzle;

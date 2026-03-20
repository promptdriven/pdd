import React from "react";
import { AbsoluteFill } from "remotion";
import { BG_COLOR } from "./constants";
import { AmbientGlow } from "./AmbientGlow";
import { QuestionText } from "./QuestionText";

export const defaultColdOpen08StillPatchingBeatProps = {};

export const ColdOpen08StillPatchingBeat: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
      }}
    >
      <AmbientGlow />
      <QuestionText />
    </AbsoluteFill>
  );
};

export default ColdOpen08StillPatchingBeat;

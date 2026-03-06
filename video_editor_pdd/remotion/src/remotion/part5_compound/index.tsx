import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { Part5CompoundSplitPatchingVsPdd } from "../part5_compound_split_patching_vs_pdd";
import { Part5CompoundStatCalloutCisq } from "../part5_compound_stat_callout_cisq";
import { Part5CompoundStatCalloutMaintenance } from "../part5_compound_stat_callout_maintenance";
import { Part5CompoundTitleCard } from "../part5_compound_title_card";

export const Part5CompoundSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 971.426667;
  const durationSeconds = 98.424;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part5_compound/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part5_compound.mp4")} style={{ width: "100%", height: "100%" }} />
      <Sequence from={Math.round(85.86 * fps)} durationInFrames={Math.ceil(5 * fps)}>
        <Part5CompoundSplitPatchingVsPdd />
      </Sequence>
      <Sequence from={Math.round(32.7 * fps)} durationInFrames={Math.ceil(5 * fps)}>
        <Part5CompoundStatCalloutCisq />
      </Sequence>
      <Sequence from={Math.round(18.08 * fps)} durationInFrames={Math.ceil(5 * fps)}>
        <Part5CompoundStatCalloutMaintenance />
      </Sequence>
      <Sequence from={Math.round(0 * fps)} durationInFrames={Math.ceil(5 * fps)}>
        <Part5CompoundTitleCard />
      </Sequence>
    </Sequence>
  );
};

export default Part5CompoundSection;

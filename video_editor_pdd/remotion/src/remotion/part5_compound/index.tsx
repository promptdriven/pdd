import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { Part5CompoundSplitPatchingVsPdd } from "../part5_compound_split_patching_vs_pdd";
import { Part5CompoundStatCalloutCisq } from "../part5_compound_stat_callout_cisq";
import { Part5CompoundStatCalloutMaintenance } from "../part5_compound_stat_callout_maintenance";
import { Part5CompoundTitleCard } from "../part5_compound_title_card";

export const Part5CompoundSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 970.896;
  const durationSeconds = 98.424;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part5_compound/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part5_compound.mp4")} style={{ width: "100%", height: "100%" }} />
      <Part5CompoundSplitPatchingVsPdd />
      <Part5CompoundStatCalloutCisq />
      <Part5CompoundStatCalloutMaintenance />
      <Part5CompoundTitleCard />
    </Sequence>
  );
};

export default Part5CompoundSection;

import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { Part5Compound01TitleCard } from "../Part5Compound01TitleCard";
import { Part5Compound03StatCalloutMaintenance } from "../Part5Compound03StatCalloutMaintenance";
import { Part5Compound05StatCalloutCisq } from "../Part5Compound05StatCalloutCisq";
import { Part5Compound06CompoundDebtChart } from "../Part5Compound06CompoundDebtChart";
import { Part5Compound08SplitPatchingVsPdd } from "../Part5Compound08SplitPatchingVsPdd";
import { Part5Compound10QuoteCard } from "../Part5Compound10QuoteCard";
import { Part5Compound11SubtitleTrack } from "../Part5Compound11SubtitleTrack";

export const Part5CompoundSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 971.490667;
  const durationSeconds = 98.424;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part5_compound/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part5_compound.mp4")} style={{ width: "100%", height: "100%" }} />
      <Part5Compound01TitleCard />
      <Part5Compound03StatCalloutMaintenance />
      <Part5Compound05StatCalloutCisq />
      <Part5Compound06CompoundDebtChart />
      <Part5Compound08SplitPatchingVsPdd />
      <Part5Compound10QuoteCard />
      <Part5Compound11SubtitleTrack />
    </Sequence>
  );
};

export default Part5CompoundSection;

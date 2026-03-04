import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { ClosingSplitDarningVsMolding } from "../closing_split_darning_vs_molding";
import { ClosingStatCalloutRoi } from "../closing_stat_callout_roi";
import { ClosingTitleCard } from "../closing_title_card";

export const ClosingSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 1069.32;
  const durationSeconds = 21.072;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("closing/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/closing.mp4")} style={{ width: "100%", height: "100%" }} />
      <ClosingSplitDarningVsMolding />
      <ClosingStatCalloutRoi />
      <ClosingTitleCard />
    </Sequence>
  );
};

export default ClosingSection;

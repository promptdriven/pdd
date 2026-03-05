import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { ClosingSplitDarningVsMolding } from "../closing_split_darning_vs_molding";
import { ClosingStatCalloutRoi } from "../closing_stat_callout_roi";
import { ClosingTitleCard } from "../closing_title_card";

export const ClosingSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 1069.584;
  const durationSeconds = 21.072;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("closing/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/closing.mp4")} style={{ width: "100%", height: "100%" }} />
      <Sequence from={Math.round(18.5 * fps)} durationInFrames={Math.ceil(5.0 * fps)}>
        <ClosingSplitDarningVsMolding />
      </Sequence>
      <Sequence from={Math.round(0.0 * fps)} durationInFrames={Math.ceil(5.0 * fps)}>
        <ClosingStatCalloutRoi />
      </Sequence>
      <Sequence from={Math.round(0.0 * fps)} durationInFrames={Math.ceil(5.0 * fps)}>
        <ClosingTitleCard />
      </Sequence>
    </Sequence>
  );
};

export default ClosingSection;

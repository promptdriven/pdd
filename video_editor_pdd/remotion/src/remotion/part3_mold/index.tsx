import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { Part3MoldSplitPromptVsCode } from "../part3_mold_split_prompt_vs_code";
import { Part3MoldStatCalloutCoderabbit } from "../part3_mold_stat_callout_coderabbit";
import { Part3MoldStatCalloutDora } from "../part3_mold_stat_callout_dora";
import { Part3MoldStatCalloutNlContext } from "../part3_mold_stat_callout_nl_context";
import { Part3MoldTitleCard } from "../part3_mold_title_card";

export const Part3MoldSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 593.722667;
  const durationSeconds = 280.728;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part3_mold/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part3_mold.mp4")} style={{ width: "100%", height: "100%" }} />
      <Sequence from={Math.round(21 * fps)} durationInFrames={Math.ceil(5 * fps)}>
        <Part3MoldSplitPromptVsCode />
      </Sequence>
      <Sequence from={Math.round(25.72 * fps)} durationInFrames={Math.ceil(5 * fps)}>
        <Part3MoldStatCalloutCoderabbit />
      </Sequence>
      <Sequence from={Math.round(40.82 * fps)} durationInFrames={Math.ceil(5 * fps)}>
        <Part3MoldStatCalloutDora />
      </Sequence>
      <Sequence from={Math.round(207.3 * fps)} durationInFrames={Math.ceil(5 * fps)}>
        <Part3MoldStatCalloutNlContext />
      </Sequence>
      <Sequence from={Math.round(0 * fps)} durationInFrames={Math.ceil(5 * fps)}>
        <Part3MoldTitleCard />
      </Sequence>
    </Sequence>
  );
};

export default Part3MoldSection;

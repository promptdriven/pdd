import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { Part1EconomicsSplitPerceptionVsReality } from "../part1_economics_split_perception_vs_reality";
import { Part1EconomicsStatCalloutGitclear } from "../part1_economics_stat_callout_gitclear";
import { Part1EconomicsStatCalloutGithub } from "../part1_economics_stat_callout_github";
import { Part1EconomicsStatCalloutUplevel } from "../part1_economics_stat_callout_uplevel";

export const Part1EconomicsSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 15.552;
  const durationSeconds = 382.176;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part1_economics/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part1_economics.mp4")} style={{ width: "100%", height: "100%" }} />
      <Part1EconomicsSplitPerceptionVsReality />
      <Part1EconomicsStatCalloutGitclear />
      <Part1EconomicsStatCalloutGithub />
      <Part1EconomicsStatCalloutUplevel />
    </Sequence>
  );
};

export default Part1EconomicsSection;

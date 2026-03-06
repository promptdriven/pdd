import React from "react";
import {
  AbsoluteFill,
  Audio,
  Loop,
  OffthreadVideo,
  Sequence,
  staticFile,
  useCurrentFrame,
} from "remotion";

import { BEATS, VISUAL_SEQUENCE, Part1EconomicsPropsType } from "./constants";
import { Part1Economics10SplitPerceptionReality, defaultPart1Economics10SplitPerceptionRealityProps } from "../Part1Economics10SplitPerceptionReality/Part1Economics10SplitPerceptionReality";
import { Part1Economics07StatCalloutGitclear, defaultPart1Economics07StatCalloutGitclearProps } from "../Part1Economics07StatCalloutGitclear/Part1Economics07StatCalloutGitclear";
import { Part1Economics04StatCalloutGithub, defaultPart1Economics04StatCalloutGithubProps } from "../Part1Economics04StatCalloutGithub/Part1Economics04StatCalloutGithub";
import { Part1Economics06StatCalloutUplevel, defaultPart1Economics06StatCalloutUplevelProps } from "../Part1Economics06StatCalloutUplevel/Part1Economics06StatCalloutUplevel";

export const Part1Economics: React.FC<Part1EconomicsPropsType> = () => {
  const frame = useCurrentFrame();

  let activeVisual = 0;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = i;
      break;
    }
  }

  return (
    <AbsoluteFill style={{ backgroundColor: "#0a0a1a" }}>
      <Audio src={staticFile("part1_economics_narration.wav")} />

      {/* Visual 0: part1_economics_split_perception_vs_reality */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <Part1Economics10SplitPerceptionReality {...defaultPart1Economics10SplitPerceptionRealityProps} />
        </Sequence>
      )}

      {/* Visual 1: part1_economics_stat_callout_gitclear */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <Part1Economics07StatCalloutGitclear {...defaultPart1Economics07StatCalloutGitclearProps} />
        </Sequence>
      )}

      {/* Visual 2: part1_economics_stat_callout_github */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <Part1Economics04StatCalloutGithub {...defaultPart1Economics04StatCalloutGithubProps} />
        </Sequence>
      )}

      {/* Visual 3: part1_economics_stat_callout_uplevel */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <Part1Economics06StatCalloutUplevel {...defaultPart1Economics06StatCalloutUplevelProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};

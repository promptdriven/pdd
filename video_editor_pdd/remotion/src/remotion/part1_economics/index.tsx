import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { Part1Economics01TitleCard } from "../Part1Economics01TitleCard";
import { Part1Economics03CostCrossoverChart } from "../Part1Economics03CostCrossoverChart";
import { Part1Economics04StatCalloutGithub } from "../Part1Economics04StatCalloutGithub";
import { Part1Economics06StatCalloutUplevel } from "../Part1Economics06StatCalloutUplevel";
import { Part1Economics07StatCalloutGitclear } from "../Part1Economics07StatCalloutGitclear";
import { Part1Economics09ContextDegradationChart } from "../Part1Economics09ContextDegradationChart";
import { Part1Economics10SplitPerceptionReality } from "../Part1Economics10SplitPerceptionReality";
import { Part1Economics12RegenerationInfographic } from "../Part1Economics12RegenerationInfographic";
import { Part1Economics13CrossoverZoom } from "../Part1Economics13CrossoverZoom";
import { Part1Economics14SubtitleTrack } from "../Part1Economics14SubtitleTrack";

export const Part1EconomicsSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 15.744;
  const durationSeconds = 382.314667;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part1_economics/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part1_economics.mp4")} style={{ width: "100%", height: "100%" }} />
      <Part1Economics01TitleCard />
      <Part1Economics03CostCrossoverChart />
      <Part1Economics04StatCalloutGithub />
      <Part1Economics06StatCalloutUplevel />
      <Part1Economics07StatCalloutGitclear />
      <Part1Economics09ContextDegradationChart />
      <Part1Economics10SplitPerceptionReality />
      <Part1Economics12RegenerationInfographic />
      <Part1Economics13CrossoverZoom />
      <Part1Economics14SubtitleTrack />
    </Sequence>
  );
};

export default Part1EconomicsSection;

import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { StatCard } from "./StatCard";
import { BG_COLOR, TOTAL_FRAMES } from "./constants";

export const defaultPart1Economics04StatCalloutGithubProps = {};

export const Part1Economics04StatCalloutGithub: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <StatCard />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics04StatCalloutGithub;

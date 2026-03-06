import React from "react";
import { AbsoluteFill, OffthreadVideo, staticFile } from "remotion";
import { StatCard } from "./StatCard";
import { BG_COLOR } from "./constants";

export const defaultPart1Economics07StatCalloutGitclearProps = {};

export const Part1Economics07StatCalloutGitclear: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part1_economics.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Stat callout card overlay */}
      <AbsoluteFill>
        <StatCard />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part1Economics07StatCalloutGitclear;

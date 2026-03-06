import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
} from "remotion";
import { BG_COLOR } from "./constants";
import { SplitPanel } from "./SplitPanel";
import { VerticalDivider } from "./VerticalDivider";
import { SourceAttribution } from "./SourceAttribution";

export const defaultPart1Economics10SplitPerceptionRealityProps = {};

export const Part1Economics10SplitPerceptionReality: React.FC = () => {
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

      {/* Left panel — Perception */}
      <SplitPanel side="left" />

      {/* Divider */}
      <VerticalDivider />

      {/* Right panel — Reality */}
      <SplitPanel side="right" />

      {/* Source attribution */}
      <SourceAttribution />
    </AbsoluteFill>
  );
};

export default Part1Economics10SplitPerceptionReality;

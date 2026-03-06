import React from "react";
import { AbsoluteFill, OffthreadVideo, staticFile } from "remotion";
import { StatCalloutCard } from "./StatCalloutCard";
import { BG_COLOR } from "./constants";

export const defaultPart4Precision04StatCalloutPromptCompressionProps = {};

export const Part4Precision04StatCalloutPromptCompression: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part4_precision.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Stat callout card overlay */}
      <AbsoluteFill>
        <StatCalloutCard />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part4Precision04StatCalloutPromptCompression;

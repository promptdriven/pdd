import React from "react";
import { AbsoluteFill, OffthreadVideo, Sequence, staticFile } from "remotion";
import { StatCalloutCard } from "./StatCalloutCard";
import { BG_COLOR, TOTAL_FRAMES } from "./constants";

export const defaultPart3Mold08StatCalloutNlContextProps = {};

export const Part3Mold08StatCalloutNlContext: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part3_mold.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Stat callout card overlay */}
      <AbsoluteFill>
        <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
          <StatCalloutCard />
        </Sequence>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part3Mold08StatCalloutNlContext;

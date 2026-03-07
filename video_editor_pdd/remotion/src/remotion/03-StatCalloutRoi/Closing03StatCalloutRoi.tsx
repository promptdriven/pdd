import React from "react";
import { AbsoluteFill, OffthreadVideo, Sequence, staticFile } from "remotion";
import { StatCard } from "./StatCard";
import { BG_COLOR, TOTAL_FRAMES } from "./constants";

export const defaultClosing03StatCalloutRoiProps = {};

export const Closing03StatCalloutRoi: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/closing.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Stat callout card overlay */}
      <AbsoluteFill>
        <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
          <StatCard />
        </Sequence>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Closing03StatCalloutRoi;

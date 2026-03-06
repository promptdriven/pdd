import React from "react";
import { AbsoluteFill, OffthreadVideo, staticFile, Sequence } from "remotion";
import { SplitPanel } from "./SplitPanel";
import { VerticalDivider } from "./VerticalDivider";
import { FooterText } from "./FooterText";
import { BG_COLOR, TOTAL_FRAMES } from "./constants";

export const defaultPart5Compound08SplitPatchingVsPddProps = {};

export const Part5Compound08SplitPatchingVsPdd: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part5_compound.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
        />
      </AbsoluteFill>

      {/* Split-screen overlay */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <AbsoluteFill>
          <SplitPanel side="left" />
          <SplitPanel side="right" />
          <VerticalDivider />
          <FooterText />
        </AbsoluteFill>
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part5Compound08SplitPatchingVsPdd;

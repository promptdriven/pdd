import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { StatCard } from "./StatCard";
import { BG_COLOR, TOTAL_FRAMES } from "./constants";

export const defaultPart3Mold03StatCalloutCoderabbitProps = {};

export const Part3Mold03StatCalloutCoderabbit: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <StatCard />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part3Mold03StatCalloutCoderabbit;

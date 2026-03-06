import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { StatCalloutCard } from "./StatCalloutCard";
import { BG_COLOR, TOTAL_FRAMES } from "./constants";

export const defaultPart3Mold04StatCalloutDoraProps = {};

export const Part3Mold04StatCalloutDora: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <StatCalloutCard />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part3Mold04StatCalloutDora;

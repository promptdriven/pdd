import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  Sequence,
} from "remotion";
import { DocIcon } from "./DocIcon";
import { ExpandingArrow } from "./ExpandingArrow";
import { UCurveChart } from "./UCurveChart";
import { CalloutBadge } from "./CalloutBadge";

export const defaultPart1Economics12RegenerationInfographicProps = {};

export const Part1Economics12RegenerationInfographic: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: "#0A1628" }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part1_economics.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Semi-transparent scrim for readability */}
      <AbsoluteFill
        style={{ backgroundColor: "rgba(10, 22, 40, 0.65)" }}
      />

      {/* ─── Part A: Compression Ratio ─── */}

      {/* Small doc icon — "Prompt ~50 lines" */}
      <Sequence from={0} durationInFrames={750}>
        <DocIcon
          x={260}
          y={210}
          width={80}
          height={100}
          color="#3B82F6"
          label="Prompt"
          sublabel="~50 lines"
          appearStart={0}
          appearEnd={30}
        />
      </Sequence>

      {/* Expanding arrow */}
      <Sequence from={0} durationInFrames={750}>
        <ExpandingArrow
          fromX={420}
          fromY={260}
          toX={1300}
          toY={260}
          startWidth={4}
          endWidth={24}
          drawStart={20}
          drawEnd={60}
          labelAppearStart={50}
          labelAppearEnd={70}
        />
      </Sequence>

      {/* Large doc icon — "Generated Module ~250-500 lines" */}
      <Sequence from={0} durationInFrames={750}>
        <DocIcon
          x={1350}
          y={150}
          width={200}
          height={220}
          color="#22C55E"
          label="Generated Module"
          sublabel="~250-500 lines"
          appearStart={50}
          appearEnd={80}
          showCodeLines
        />
      </Sequence>

      {/* ─── Part B: Defect U-Curve ─── */}
      <Sequence from={0} durationInFrames={750}>
        <UCurveChart
          axesFadeStart={100}
          axesFadeEnd={130}
          curveDrawStart={130}
          curveDrawEnd={200}
          sweetSpotStart={190}
        />
      </Sequence>

      {/* MIT callout badge */}
      <Sequence from={0} durationInFrames={750}>
        <CalloutBadge
          text="89% accuracy with NL context — MIT, 2024"
          color="#22C55E"
          appearStart={210}
          appearEnd={240}
          x={1240}
          y={130}
        />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics12RegenerationInfographic;

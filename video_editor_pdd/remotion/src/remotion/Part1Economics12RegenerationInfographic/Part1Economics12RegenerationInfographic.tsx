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
import {
  BG_COLOR,
  BLUE,
  GREEN,
  TOTAL_FRAMES,
  SMALL_DOC_POS,
  SMALL_DOC_SIZE,
  SMALL_DOC_START,
  SMALL_DOC_END,
  ARROW_FROM,
  ARROW_TO,
  ARROW_START_WIDTH,
  ARROW_END_WIDTH,
  ARROW_DRAW_START,
  ARROW_DRAW_END,
  LARGE_DOC_POS,
  LARGE_DOC_SIZE,
  LARGE_DOC_START,
  LARGE_DOC_END,
  AXES_FADE_START,
  AXES_FADE_END,
  CURVE_DRAW_START,
  CURVE_DRAW_END,
  SWEET_SPOT_START,
  BADGE_START,
  BADGE_END,
} from "./constants";

export const defaultPart1Economics12RegenerationInfographicProps = {};

export const Part1Economics12RegenerationInfographic: React.FC = () => {
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

      {/* Semi-transparent scrim for readability */}
      <AbsoluteFill
        style={{ backgroundColor: "rgba(10, 22, 40, 0.65)" }}
      />

      {/* ─── Part A: Compression Ratio ─── */}

      {/* Small doc icon — "Prompt ~50 lines" */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <DocIcon
          x={SMALL_DOC_POS.x - SMALL_DOC_SIZE.w / 2}
          y={SMALL_DOC_POS.y - SMALL_DOC_SIZE.h / 2}
          width={SMALL_DOC_SIZE.w}
          height={SMALL_DOC_SIZE.h}
          color={BLUE}
          label="Prompt"
          sublabel="~50 lines"
          appearStart={SMALL_DOC_START}
          appearEnd={SMALL_DOC_END}
        />
      </Sequence>

      {/* Expanding arrow */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ExpandingArrow
          fromX={ARROW_FROM.x}
          fromY={ARROW_FROM.y}
          toX={ARROW_TO.x}
          toY={ARROW_TO.y}
          startWidth={ARROW_START_WIDTH}
          endWidth={ARROW_END_WIDTH}
          drawStart={ARROW_DRAW_START}
          drawEnd={ARROW_DRAW_END}
          labelAppearStart={LARGE_DOC_START}
          labelAppearEnd={LARGE_DOC_START + 20}
        />
      </Sequence>

      {/* Large doc icon — "Generated Module ~250-500 lines" */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <DocIcon
          x={LARGE_DOC_POS.x - LARGE_DOC_SIZE.w / 2}
          y={LARGE_DOC_POS.y - LARGE_DOC_SIZE.h / 2}
          width={LARGE_DOC_SIZE.w}
          height={LARGE_DOC_SIZE.h}
          color={GREEN}
          label="Generated Module"
          sublabel="~250-500 lines"
          appearStart={LARGE_DOC_START}
          appearEnd={LARGE_DOC_END}
          showCodeLines
        />
      </Sequence>

      {/* ─── Part B: Defect U-Curve ─── */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <UCurveChart
          axesFadeStart={AXES_FADE_START}
          axesFadeEnd={AXES_FADE_END}
          curveDrawStart={CURVE_DRAW_START}
          curveDrawEnd={CURVE_DRAW_END}
          sweetSpotStart={SWEET_SPOT_START}
        />
      </Sequence>

      {/* MIT callout badge */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <CalloutBadge
          text="89% accuracy with NL context — MIT, 2024"
          color={GREEN}
          appearStart={BADGE_START}
          appearEnd={BADGE_END}
          x={1240}
          y={130}
        />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics12RegenerationInfographic;

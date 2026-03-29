import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from "remotion";
import {
  BG_COLOR,
  FONT_FAMILY,
  SUBTITLE_FONT_SIZE,
  SUBTITLE_COLOR,
  SUBTITLE_OPACITY,
  CANVAS_WIDTH,
  SUBTITLE_Y,
  LINE1_Y,
  LINE2_Y,
  LINE1_SEGMENTS,
  LINE2_SEGMENTS,
  LINE1_START,
  LINE2_START,
  SUBTITLE_START,
  FADEOUT_START,
  FADEOUT_END,
  TOTAL_FRAMES,
} from "./constants";
import { BlueprintGrid } from "./BlueprintGrid";
import { TypeWriterLine } from "./TypeWriterLine";
import { ConnectingLines } from "./ConnectingLines";

export const defaultPart2ParadigmShift14SynopsysPddEquivalenceProps = {};

export const Part2ParadigmShift14SynopsysPddEquivalence: React.FC = () => {
  const frame = useCurrentFrame();

  // Global fade out (frames 330-390)
  const fadeOutOpacity = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  // Subtitle fade in (frames 180-210)
  const subtitleOpacity = interpolate(
    frame,
    [SUBTITLE_START, SUBTITLE_START + 30],
    [0, SUBTITLE_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        opacity: fadeOutOpacity,
      }}
    >
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Line 1: Synopsys */}
      <Sequence from={LINE1_START} durationInFrames={TOTAL_FRAMES}>
        <TypeWriterLine
          segments={LINE1_SEGMENTS}
          startFrame={LINE1_START}
          y={LINE1_Y}
        />
      </Sequence>

      {/* Line 2: PDD */}
      <Sequence from={LINE2_START} durationInFrames={TOTAL_FRAMES - LINE2_START}>
        <TypeWriterLine
          segments={LINE2_SEGMENTS}
          startFrame={0}
          y={LINE2_Y}
        />
      </Sequence>

      {/* Equivalence connecting lines */}
      <ConnectingLines />

      {/* Subtitle: "Same architecture." */}
      <div
        style={{
          position: "absolute",
          top: SUBTITLE_Y,
          left: 0,
          width: CANVAS_WIDTH,
          display: "flex",
          justifyContent: "center",
          alignItems: "center",
          fontFamily: FONT_FAMILY,
          fontSize: SUBTITLE_FONT_SIZE,
          fontStyle: "italic",
          color: SUBTITLE_COLOR,
          opacity: subtitleOpacity,
        }}
      >
        Same architecture.
      </div>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift14SynopsysPddEquivalence;

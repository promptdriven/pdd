import React from "react";
import { AbsoluteFill } from "remotion";
import { Part2SubtitleBackdrop } from "./Part2SubtitleBackdrop";
import { Part2WordByWordSubtitle } from "./Part2WordByWordSubtitle";
import { P2_WORD_DATA, BG_COLOR } from "./constants";

export const defaultPart2ParadigmShift11SubtitleTrackProps = {};

export const Part2ParadigmShift11SubtitleTrack: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: 1920,
        height: 1080,
      }}
    >
      {/* Subtitle overlay runs full duration — no Sequence offset */}
      <AbsoluteFill style={{ pointerEvents: "none" }}>
        {/* Semi-transparent backdrop band in the bottom third */}
        <Part2SubtitleBackdrop />

        {/* Word-by-word animated subtitle renderer */}
        <Part2WordByWordSubtitle words={P2_WORD_DATA} />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift11SubtitleTrack;

import React from "react";
import { AbsoluteFill } from "remotion";
import { SubtitleBackdrop } from "./SubtitleBackdrop";
import { WordByWordSubtitle } from "./WordByWordSubtitle";
import { WORD_DATA, BG_COLOR } from "./constants";

export const defaultPart3Mold13SubtitleTrackProps = {};

export const Part3Mold13SubtitleTrack: React.FC = () => {
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
        <SubtitleBackdrop />

        {/* Word-by-word animated subtitle renderer */}
        <WordByWordSubtitle words={WORD_DATA} />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part3Mold13SubtitleTrack;

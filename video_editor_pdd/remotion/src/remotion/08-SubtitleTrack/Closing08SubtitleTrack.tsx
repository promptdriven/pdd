import React from "react";
import { AbsoluteFill } from "remotion";
import { SubtitleBackdrop } from "./SubtitleBackdrop";
import { WordByWordSubtitle } from "./WordByWordSubtitle";
import { WORD_DATA, BG_COLOR } from "./constants";

export const defaultClosing08SubtitleTrackProps = {};

export const Closing08SubtitleTrack: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: 1920,
        height: 1080,
      }}
    >
      <AbsoluteFill style={{ pointerEvents: "none" }}>
        <SubtitleBackdrop />
        <WordByWordSubtitle words={WORD_DATA} />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Closing08SubtitleTrack;

import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { SubtitleBackdrop } from "./SubtitleBackdrop";
import { WordByWordSubtitle } from "./WordByWordSubtitle";
import {
  WORD_DATA,
  TOTAL_FRAMES,
  SUBTITLE_START_FRAME,
  BG_COLOR,
} from "./constants";

const SUBTITLE_DURATION = TOTAL_FRAMES - SUBTITLE_START_FRAME;

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
      {/* Subtitle track starts after the title card (frame 150) and runs to end */}
      <Sequence from={SUBTITLE_START_FRAME} durationInFrames={SUBTITLE_DURATION}>
        <AbsoluteFill style={{ pointerEvents: "none" }}>
          {/* Semi-transparent backdrop band in the bottom third */}
          <SubtitleBackdrop />

          {/* Word-by-word animated subtitle renderer */}
          <WordByWordSubtitle words={WORD_DATA} />
        </AbsoluteFill>
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part3Mold13SubtitleTrack;

import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { SubtitleBackdrop } from "./SubtitleBackdrop";
import { WordByWordSubtitle } from "./WordByWordSubtitle";
import { WORD_DATA, TOTAL_FRAMES, BG_COLOR } from "./constants";

export const defaultColdOpen03SubtitleTrackProps = {};

export const ColdOpen03SubtitleTrack: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: 1920,
        height: 1080,
      }}
    >
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <AbsoluteFill style={{ pointerEvents: "none" }}>
          {/* Semi-transparent backdrop bar in lower third */}
          <SubtitleBackdrop />

          {/* Word-by-word animated subtitle renderer */}
          <WordByWordSubtitle words={WORD_DATA} />
        </AbsoluteFill>
      </Sequence>
    </AbsoluteFill>
  );
};

export default ColdOpen03SubtitleTrack;

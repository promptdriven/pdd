import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { SubtitleBackdrop } from "./SubtitleBackdrop";
import { WordByWordSubtitle } from "./WordByWordSubtitle";
import { WORD_DATA, TOTAL_FRAMES, BG_COLOR } from "./constants";

export const defaultColdOpen03SubtitleTrackProps = {};

export const ColdOpen03SubtitleTrack: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        {/* Semi-transparent backdrop bar in lower third */}
        <SubtitleBackdrop />

        {/* Word-by-word animated subtitle renderer */}
        <WordByWordSubtitle words={WORD_DATA} />
      </Sequence>
    </AbsoluteFill>
  );
};

export default ColdOpen03SubtitleTrack;

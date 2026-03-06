import React from "react";
import {
  AbsoluteFill,
  Audio,
  Loop,
  OffthreadVideo,
  Sequence,
  staticFile,
  useCurrentFrame,
} from "remotion";

import { BEATS, VISUAL_SEQUENCE, ColdOpenSectionPropsType } from "./constants";
import { ColdOpen01TitleCard, defaultColdOpen01TitleCardProps } from "../ColdOpen01TitleCard/ColdOpen01TitleCard";

export const ColdOpenSection: React.FC<ColdOpenSectionPropsType> = () => {
  const frame = useCurrentFrame();

  let activeVisual = 0;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = i;
      break;
    }
  }

  return (
    <AbsoluteFill style={{ backgroundColor: "#0a0a1a" }}>
      <Audio src={staticFile("cold_open_narration.wav")} />

      {/* Visual 0: cold_open_title_card */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <ColdOpen01TitleCard {...defaultColdOpen01TitleCardProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};

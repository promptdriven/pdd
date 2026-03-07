import React from "react";
import { Sequence } from "remotion";

import { ColdOpenSection as ColdOpenSectionBase } from "../ColdOpenSection";
import { ColdOpen01TitleCard } from "../ColdOpen01TitleCard";
import { ColdOpen03SubtitleTrack } from "../ColdOpen03SubtitleTrack";
import { ColdOpen05CrossfadeTransition } from "../ColdOpen05CrossfadeTransition";
import { ColdOpen06FadeBookends } from "../ColdOpen06FadeBookends";
import { ColdOpen07MonitorGlowOverlay } from "../ColdOpen07MonitorGlowOverlay";
import { ColdOpen08ClosingQuestionCard } from "../ColdOpen08ClosingQuestionCard";

export const ColdOpenSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 0;
  const durationSeconds = 15.744;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <ColdOpenSectionBase />
      <ColdOpen01TitleCard />
      <ColdOpen03SubtitleTrack />
      <ColdOpen05CrossfadeTransition />
      <ColdOpen06FadeBookends />
      <ColdOpen07MonitorGlowOverlay />
      <ColdOpen08ClosingQuestionCard />
    </Sequence>
  );
};

export default ColdOpenSection;

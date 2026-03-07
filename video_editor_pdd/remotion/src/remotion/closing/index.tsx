import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { Closing01TitleCard } from "../Closing01TitleCard";
import { Closing03StatCalloutRoi } from "../Closing03StatCalloutRoi";
import { Closing05SplitDarningVsMolding } from "../Closing05SplitDarningVsMolding";
import { Closing07CtaCard } from "../Closing07CtaCard";
import { Closing08SubtitleTrack } from "../Closing08SubtitleTrack";

export const ClosingSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 1069.914667;
  const durationSeconds = 21.072;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("closing/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/closing.mp4")} style={{ width: "100%", height: "100%" }} />
      <Closing01TitleCard />
      <Closing03StatCalloutRoi />
      <Closing05SplitDarningVsMolding />
      <Closing07CtaCard />
      <Closing08SubtitleTrack />
    </Sequence>
  );
};

export default ClosingSection;

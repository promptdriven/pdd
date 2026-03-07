import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { Part3Mold01TitleCard } from "../Part3Mold01TitleCard";
import { Part3Mold03StatCalloutCoderabbit } from "../Part3Mold03StatCalloutCoderabbit";
import { Part3Mold04StatCalloutDora } from "../Part3Mold04StatCalloutDora";
import { Part3Mold06SplitPromptVsCode } from "../Part3Mold06SplitPromptVsCode";
import { Part3Mold08StatCalloutNlContext } from "../Part3Mold08StatCalloutNlContext";
import { Part3Mold10RatchetInfographic } from "../Part3Mold10RatchetInfographic";
import { Part3Mold12ThreePillarsDiagram } from "../Part3Mold12ThreePillarsDiagram";
import { Part3Mold13SubtitleTrack } from "../Part3Mold13SubtitleTrack";

export const Part3MoldSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 593.850667;
  const durationSeconds = 280.728;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part3_mold/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part3_mold.mp4")} style={{ width: "100%", height: "100%" }} />
      <Part3Mold01TitleCard />
      <Part3Mold03StatCalloutCoderabbit />
      <Part3Mold04StatCalloutDora />
      <Part3Mold06SplitPromptVsCode />
      <Part3Mold08StatCalloutNlContext />
      <Part3Mold10RatchetInfographic />
      <Part3Mold12ThreePillarsDiagram />
      <Part3Mold13SubtitleTrack />
    </Sequence>
  );
};

export default Part3MoldSection;

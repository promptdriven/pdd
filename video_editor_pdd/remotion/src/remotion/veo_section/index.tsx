import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { VeoSection01TitleCard } from "../veo_section_01_title_card";
import { VeoSection02KeyVisual } from "../veo_section_02_key_visual";
import { VeoSection03SplitSummary } from "../veo_section_03_split_summary";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "veo_section_01_title_card": VeoSection01TitleCard,
  "veo_section_02_key_visual": VeoSection02KeyVisual,
  "veo_section_03_split_summary": VeoSection03SplitSummary,
};

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 11.392;
  const frame = useCurrentFrame();
  let activeVisual = VISUAL_SEQUENCE.length > 0 ? VISUAL_SEQUENCE[0] : null;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = VISUAL_SEQUENCE[i];
      break;
    }
  }
  const ActiveComponent = activeVisual ? COMPONENT_MAP[activeVisual.id] ?? null : null;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("veo_section/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/veo_section.mp4")} style={{ width: "100%", height: "100%" }} />
      {ActiveComponent && activeVisual ? (
        <Sequence
          from={activeVisual.start}
          durationInFrames={Math.max(1, activeVisual.end - activeVisual.start)}
        >
          <ActiveComponent />
        </Sequence>
      ) : null}
    </Sequence>
  );
};

export default VeoSectionSection;

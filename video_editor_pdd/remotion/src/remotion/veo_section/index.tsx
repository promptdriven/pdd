import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider } from "../_shared/visual-runtime";
import { VeoSection01TitleCard } from "../VeoSection01TitleCard";
import { VeoSection02KeyVisual } from "../veo_section_02_key_visual";
import { VeoSection03SplitSummary } from "../veo_section_03_split_summary";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "veo_section_01_title_card": VeoSection01TitleCard,
  "veo_section_02_key_visual": VeoSection02KeyVisual,
  "veo_section_03_split_summary": VeoSection03SplitSummary,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "veo_section_01_title_card": 90,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "veo_section_01_title_card": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
  "veo_section_02_key_visual": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
  "veo_section_03_split_summary": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
  "04_veo_broll": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
  "05_veo_cutaway": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
};

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 12.053333;
  const frame = useCurrentFrame();
  let activeVisual = VISUAL_SEQUENCE.length > 0 ? VISUAL_SEQUENCE[0] : null;
  let activeVisualIndex = VISUAL_SEQUENCE.length > 0 ? 0 : -1;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = VISUAL_SEQUENCE[i];
      activeVisualIndex = i;
      break;
    }
  }
  let renderVisual = activeVisual;
  for (let i = activeVisualIndex; i >= 0; i--) {
    const candidate = VISUAL_SEQUENCE[i];
    const candidateComponent = COMPONENT_MAP[candidate.id] ?? null;
    const candidateMedia = VISUAL_MEDIA[candidate.id] ?? null;
    if (candidateComponent || candidateMedia?.defaultSrc) {
      renderVisual = candidate;
      break;
    }
  }
  const ActiveComponent = renderVisual ? COMPONENT_MAP[renderVisual.id] ?? null : null;
  const activeVisualDuration = activeVisual ? Math.max(1, activeVisual.end - activeVisual.start) : 1;
  const intrinsicDurationInFrames = renderVisual ? VISUAL_DURATIONS[renderVisual.id] ?? activeVisualDuration : activeVisualDuration;
  const activeVisualMedia = renderVisual ? VISUAL_MEDIA[renderVisual.id] ?? null : null;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("veo_section/narration.wav")} />
      {activeVisualMedia?.defaultSrc ? (
        <OffthreadVideo src={staticFile(activeVisualMedia.defaultSrc)} style={{ width: "100%", height: "100%" }} />
      ) : (
        <OffthreadVideo src={staticFile("veo/veo_section.mp4")} style={{ width: "100%", height: "100%" }} />
      )}
      {ActiveComponent && activeVisual ? (
        <Sequence
          from={activeVisual.start}
          durationInFrames={Math.max(1, activeVisual.end - activeVisual.start)}
        >
          <SlotScaledSequence intrinsicDurationInFrames={intrinsicDurationInFrames}>
            <VisualMediaProvider media={activeVisualMedia}>
              <ActiveComponent />
            </VisualMediaProvider>
          </SlotScaledSequence>
        </Sequence>
      ) : null}
    </Sequence>
  );
};

export default VeoSectionSection;
